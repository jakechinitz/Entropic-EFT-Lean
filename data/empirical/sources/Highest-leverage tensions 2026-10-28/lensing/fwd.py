"""Population forward model of the KiDS-1000 isolated-lens ESD profiles (Brouwer et al. 2021, Fig. 3 data,
four stellar-mass bins, 15 radii each, full covariance) for:
  RAR   uncapped radial-acceleration-relation response (no budget)
  CAP   RAR response capped at the Lagrangian stock budget B = e^{-eta}(1-f_b) M_X  (M_X = M200c or M_sp)
  NFW   LCDM halo, (1-f_b) M200c NFW truncated at the splashback radius, plus the galaxy as a point mass
Every model can add the same environment term A_out * b(M_h) * DSigma_lin(R) (correlated matter outside the
halo / budget; the theory's unallocated stock is cold dust and clusters as CDM does).
The lens population per bin: Baldry+12 stellar mass function x a completeness factor, Gaussian M* errors,
Moster+13 SHMR (M200c) with 0.15 dex scatter, Tinker+08 halo mass function, all at z = 0.2.
Physical units with h = 0.7 (the data are in h70 units).
"""
import numpy as np, json, sys
from scipy.special import erf
from colossus.cosmology import cosmology
from colossus.lss import mass_function, bias
from colossus.halo import concentration, mass_defs, splashback

COS = cosmology.setCosmology('planck18'); h = 0.7     # data units h70; colossus h only enters internally
ZL = 0.2
G = 4.30091e-9          # Mpc (km/s)^2 / Msun
KMS2_MPC_TO_MS2 = 1e6 / 3.0857e22
EPS, ETA, FB = 0.187946, 0.0298668443935, 0.157
E_Z = np.sqrt(0.315 * (1 + ZL)**3 + 0.685)
A0 = 1.2307e-10 * E_Z   # theory: a0 = eps c H(z); 1.2307e-10 at H0 = 67.4
A0_MPC = A0 / KMS2_MPC_TO_MS2   # (km/s)^2 / Mpc

# ---------------------------------------------------------------- data
D = '/home/claude/lens/ext/brouwer/'
DATA = []; RAD = None
for b in range(1, 5):
    t = np.loadtxt(D + f'Fig-3_Lensing-rotation-curves_Massbin-{b}.txt')
    RAD = t[:, 0]; DATA.append(t[:, 1] / t[:, 4])
DATA = np.concatenate(DATA)
cv = np.loadtxt(D + 'Fig-3_Lensing-rotation-curves_Massbins_covmatrix.txt')
bins_lo = np.array([8.5, 10.3, 10.6, 10.8]); NR = len(RAD)
COV = np.zeros((4 * NR, 4 * NR))
for row in cv:
    m = np.argmin(abs(bins_lo - row[0])); n = np.argmin(abs(bins_lo - row[1]))
    i = np.argmin(abs(RAD - row[2])); j = np.argmin(abs(RAD - row[3]))
    COV[m * NR + i, n * NR + j] = row[4] / row[6]
ICOV = np.linalg.inv(COV)
BIN_EDGES = [(8.5, 10.3), (10.3, 10.6), (10.6, 10.8), (10.8, 11.0)]
MGAL_B21 = [10.14, 10.57, 10.78, 10.96]

# ---------------------------------------------------------------- population
def fcold(lms): return 10**(-0.69 * lms + 6.63)
def mgal(lms): return lms + np.log10(1 + fcold(lms))

def smf(lms):                       # Baldry+12 double Schechter, per dex
    M = 10**(lms - 10.66)
    return np.log(10) * np.exp(-M) * (3.96e-3 * M**(1 - 0.35) + 0.79e-3 * M**(1 - 1.47))

def moster(lmh, z=ZL):              # log M* given log M200c [Msun]
    zz = z / (1 + z)
    M1 = 10**(11.590 + 1.195 * zz); N = 0.0351 - 0.0247 * zz
    be = 1.376 - 0.826 * zz; ga = 0.608 + 0.329 * zz
    Mh = 10**lmh
    return lmh + np.log10(2 * N / ((Mh / M1)**(-be) + (Mh / M1)**ga))

LMS = np.arange(8.6, 11.81, 0.04)         # true log M*
LMH = np.arange(10.4, 14.61, 0.04)        # log M200c [Msun]
HMF = mass_function.massFunction(10**LMH * h, ZL, mdef='200c', model='tinker08', q_out='dndlnM')

def population(b, sig_obs=0.15, sig_shmr=0.15, tc=None, dlogm=0.0):
    """Weights w[i_ms, i_mh] for bin b. tc: completeness turnover (log M*). dlogm: systematic shift of the
    observed masses (observed = true + dlogm + noise)."""
    lo, hi = BIN_EDGES[b]
    comp = 1.0 if tc is None else 1 / (1 + 10**(-3.0 * (LMS - tc)))
    # p(true M*) for galaxies observed in the bin
    pobs = 0.5 * (erf((hi - LMS - dlogm) / (np.sqrt(2) * sig_obs)) - erf((lo - LMS - dlogm) / (np.sqrt(2) * sig_obs)))
    # joint (M*, Mh): HMF(Mh) * N(M*; SHMR(Mh), s) ; then multiply by completeness and bin selection
    joint = HMF[None, :] * np.exp(-0.5 * ((LMS[:, None] - moster(LMH)[None, :]) / sig_shmr)**2)
    w = joint * (comp * pobs)[:, None]
    return w / w.sum()

def obs_mean_mgal(b, **kw):
    """log10 <M_gal> of the observed masses, for comparison with B21."""
    lo, hi = BIN_EDGES[b]; sig = kw.get('sig_obs', 0.15); tc = kw.get('tc'); dl = kw.get('dlogm', 0.0)
    o = np.arange(lo, hi, 0.005) + 0.0025
    comp = 1.0 if tc is None else 1 / (1 + 10**(-3.0 * (LMS - tc)))
    p_t = (smf_central_like() * comp)
    p_o = (p_t[:, None] * np.exp(-0.5 * ((o[None, :] - LMS[:, None] - dl) / sig)**2)).sum(0)
    return np.log10(np.sum(p_o * 10**mgal(o)) / p_o.sum())

def smf_central_like():
    # SMF implied by the HMF + SHMR (centrals), on the LMS grid
    joint = HMF[None, :] * np.exp(-0.5 * ((LMS[:, None] - moster(LMH)[None, :]) / 0.15)**2)
    return joint.sum(1)

# ---------------------------------------------------------------- halo quantities on the Mh grid
CONC = concentration.concentration(10**LMH * h, '200c', ZL, model='ishiyama21')
R200 = (10**LMH * h * 3 / (4 * np.pi * 200 * COS.rho_c(ZL) * 1e9))**(1 / 3) / h   # Mpc physical
M200m = np.array([mass_defs.changeMassDefinition(10**l * h, c, ZL, '200c', '200m')[0] for l, c in zip(LMH, CONC)])
RSP, MSP = [], []
for m in M200m:
    r, M, _ = splashback.splashbackRadius(ZL, '200m', M=m, model='diemer20', rspdef='sp-apr-mn')
    RSP.append(r / 1e3 / h); MSP.append(M / h)
RSP, MSP = np.array(RSP), np.array(MSP)
BIAS = bias.haloBias(10**LMH * h, ZL, '200c', model='tinker10')

# ---------------------------------------------------------------- projection
RG = np.logspace(-3.5, 1.3, 1600)   # Mpc, 3D radius grid
def esd_from_menc(Menc):
    """ESD (Msun/pc^2) at RAD for an extended mass profile M(<r) given on RG (no point mass)."""
    rho = np.gradient(Menc, RG) / (4 * np.pi * RG**2)
    # Sigma(R) on a fine R grid via substitution r = sqrt(R^2 + l^2)
    Rf = np.logspace(-3.4, 1.0, 500)
    l = np.logspace(-4, 1.3, 600)
    rr = np.sqrt(Rf[:, None]**2 + l[None, :]**2)
    Sig = 2 * np.trapezoid(np.interp(rr, RG, rho, right=0.0), l, axis=1)
    # inner part below Rf[0]: treat as part of enclosed projected mass using M3D(<Rf0) (small)
    M2 = np.interp(Rf[0], RG, Menc) + np.concatenate([[0], np.cumsum(0.5 * (2 * np.pi * Rf[1:] * Sig[1:] + 2 * np.pi * Rf[:-1] * Sig[:-1]) * np.diff(Rf))])
    dS = M2 / (np.pi * Rf**2) - Sig
    return np.interp(RAD, Rf, dS) / 1e12      # Msun/Mpc^2 -> Msun/pc^2

def nu(y): return 1 / (1 - np.exp(-np.sqrt(y)))

def esd_rar(lmg, budget=None):
    Mb = 10**lmg
    y = G * Mb / RG**2 / A0_MPC
    Mex = Mb * (nu(y) - 1)
    if budget is not None: Mex = np.minimum(Mex, budget)
    return esd_from_menc(Mex) + Mb / (np.pi * RAD**2) / 1e12

def esd_nfw(i_mh):
    c = CONC[i_mh]; r200 = R200[i_mh]; rt = RSP[i_mh]
    x = RG / (r200 / c); m = lambda q: np.log(1 + q) - q / (1 + q)
    Menc = (1 - FB) * 10**LMH[i_mh] * m(np.minimum(x, rt / (r200 / c))) / m(c)
    return esd_from_menc(Menc)

def esd_lin():
    """DSigma of the linear matter correlation (b = 1), physical Msun/pc^2 at RAD."""
    Rf = np.logspace(-2.5, 1.2, 300)
    l = np.linspace(0, 100, 4001)
    rr = np.sqrt(Rf[:, None]**2 + l[None, :]**2) * (1 + ZL) * h     # comoving Mpc/h
    xi = COS.correlationFunction(rr.ravel(), ZL).reshape(rr.shape)
    rhom = COS.rho_m(ZL) * 1e9 * h**2        # Msun/Mpc^3 physical (colossus: Msun h^2 / kpc^3)
    Sig = 2 * rhom * np.trapezoid(xi, l, axis=1)                # l in physical Mpc
    M2 = np.concatenate([[0], np.cumsum(0.5 * (2 * np.pi * Rf[1:] * Sig[1:] + 2 * np.pi * Rf[:-1] * Sig[:-1]) * np.diff(Rf))])
    M2 += np.pi * Rf[0]**2 * Sig[0]
    return np.interp(RAD, Rf, M2 / (np.pi * Rf**2) - Sig) / 1e12

if __name__ == '__main__':
    print('a0(z=0.2) =', A0)
    for i in (np.argmin(abs(LMH - 12.0)), np.argmin(abs(LMH - 12.5))):
        print(f'logM200c {LMH[i]:.2f}: c {CONC[i]:.2f} R200 {R200[i]*1e3:.0f} kpc Rsp {RSP[i]*1e3:.0f} kpc Msp/M200c {MSP[i]/10**LMH[i]:.2f} b {BIAS[i]:.2f}')
    print('DSigma_lin', np.round(esd_lin(), 4))

# ---------------------------------------------------------------- DK14 outer (infall) term beyond the splashback radius
def esd_outer(i_mh, s_e=1.5):
    """DSigma of rho_mean * (r / 5 R200m)^-s_e for r > r_sp (b_e = 1); the uniform mean drops out."""
    rhom = COS.rho_m(ZL) * 1e9 * h**2
    R200m = (M200m[i_mh] * 3 / (4 * np.pi * 200 * COS.rho_m(ZL) * 1e9))**(1 / 3) / h
    rho = np.where(RG > RSP[i_mh], rhom * (RG / (5 * R200m))**(-s_e), 0.0)
    Rf = np.logspace(-3.4, 1.0, 500); l = np.logspace(-4, 2.0, 900)
    rr = np.sqrt(Rf[:, None]**2 + l[None, :]**2)
    rho_i = np.where(rr > RSP[i_mh], rhom * (rr / (5 * R200m))**(-s_e), 0.0)
    Sig = 2 * np.trapezoid(rho_i, l, axis=1)
    M2 = np.concatenate([[0], np.cumsum(0.5 * (2 * np.pi * Rf[1:] * Sig[1:] + 2 * np.pi * Rf[:-1] * Sig[:-1]) * np.diff(Rf))])
    return np.interp(RAD, Rf, M2 / (np.pi * Rf**2) - Sig) / 1e12
