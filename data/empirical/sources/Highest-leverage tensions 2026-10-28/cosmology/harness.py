"""One harness for the K01 reconciliation: LCDM and the tied O.12 release model under identical data and settings.

usage: python3 harness.py MODEL [key=value ...]
  MODEL   LCDM | REL
  sn      dovekie | sn5yr | none          (default dovekie)
  off     0 | 1   free extra magnitude offset for z < 0.1 (the bundle's 'low-z offset marginalization')
  mnu     0 | 0.06                          (0: N_eff = 3.044 massless; 0.06: one massive + 2.046 massless)
  tau     lowE | fp                         (0.0544 +- 0.0073 | 0.0506 +- 0.0086)
  cal     free | fixed                      (free: Gaussian prior 1 +- 0.0025)
  AL      number | calc                     (release model only; LCDM always 1)
  acc     0 | 1                             (1: higher CAMB accuracy)
  tag     output tag
"""
import sys, os, json, time
import numpy as np
import camb
from scipy.io import FortranFile
import scipy.linalg
from scipy.integrate import solve_ivp
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import release as REL

MODEL = sys.argv[1]
O = dict(sn='dovekie', off='0', mnu='0.06', tau='lowE', cal='free', AL='0.979', acc='0', nl='1', tag='')
for a in sys.argv[2:]:
    k, v = a.split('='); O[k] = v
MNU = float(O['mnu']); OFF = O['off'] == '1'; CALFREE = O['cal'] == 'free'; ACC = O['acc'] == '1'
TAU0, TAUS = {'lowE': (0.0544, 0.0073), 'fp': (0.0506, 0.0086)}[O['tau']]
R_FORM = 5.3333
EXT = os.path.join(HERE, 'ext')

# ------------------------------------------------------------ Planck 2018 plik_lite TTTEEE + 2 low-ell TT bins
PD = os.path.join(EXT, 'planck-lite-py', 'data', 'planck2018_plik_lite') + '/'
LD = os.path.join(EXT, 'planck-lite-py', 'data', 'planck2018_low_ell') + '/'
_, Xhi, _ = np.genfromtxt(PD + 'cl_cmb_plik_v22.dat', unpack=True)
blmin = np.loadtxt(PD + 'blmin.dat').astype(int); blmax = np.loadtxt(PD + 'blmax.dat').astype(int)
bw = np.loadtxt(PD + 'bweight.dat')
_, Xlo, Slo = np.genfromtxt(LD + 'CTT_bin_low_ell_2018.dat', unpack=True)
lbmin = np.loadtxt(LD + 'blmin_low_ell.dat').astype(int); lbmax = np.loadtxt(LD + 'blmax_low_ell.dat').astype(int)
lbw = np.loadtxt(LD + 'bweight_low_ell.dat')
NTT, NTE, NEE = 215, 199, 199
f_ = FortranFile(PD + 'c_matrix_plik_v22.dat', 'r')
cov = f_.read_reals(dtype=float).reshape((613, 613))
cov = np.tril(cov) + np.tril(cov, -1).T          # as planck-lite-py: lower triangle mirrored
IC = np.zeros((615, 615)); IC[:2, :2] = np.diag(1 / Slo**2)
IC[2:, 2:] = scipy.linalg.cho_solve(scipy.linalg.cho_factor(cov), np.eye(613))
XDATA = np.concatenate([Xlo, Xhi])

def bin_cl(Cl, ell0, bmin, bmax, w, plmin):
    return np.array([np.sum(Cl[bmin[i] + plmin - ell0: bmax[i] + plmin + 1 - ell0] * w[bmin[i]:bmax[i] + 1])
                     for i in range(len(bmin))])

def cmb_vec(Dtt, Dte, Dee):           # D_ell from ell = 2
    ls = np.arange(2, 2 + len(Dtt)); fac = ls * (ls + 1) / (2 * np.pi)
    Ctt, Cte, Cee = Dtt / fac, Dte / fac, Dee / fac
    return np.concatenate([bin_cl(Ctt, 2, lbmin, lbmax, lbw, 2),
                           bin_cl(Ctt, 2, blmin[:NTT], blmax[:NTT], bw, 30),
                           bin_cl(Cte, 2, blmin[:NTE], blmax[:NTE], bw, 30),
                           bin_cl(Cee, 2, blmin[:NEE], blmax[:NEE], bw, 30)])

# ------------------------------------------------------------ DESI DR2 BAO (DR2 paper Table IV)
ANISO = [(0.510, 13.588, 0.167, 21.863, 0.425, -0.459), (0.706, 17.351, 0.177, 19.455, 0.330, -0.404),
         (0.934, 21.576, 0.152, 17.641, 0.193, -0.416), (1.321, 27.601, 0.318, 14.176, 0.221, -0.434),
         (1.484, 30.512, 0.760, 12.817, 0.516, -0.500), (2.330, 38.988, 0.531, 8.632, 0.101, -0.431)]
BGS = (0.295, 7.942, 0.075)
BZ, BV, BQ = [BGS[0]], [BGS[1]], ['V']
BC = np.zeros((13, 13)); BC[0, 0] = BGS[2]**2
for i, (z, dm, sm, dh, sh, rho) in enumerate(ANISO):
    j = 1 + 2 * i
    BZ += [z, z]; BV += [dm, dh]; BQ += ['M', 'H']
    BC[j, j] = sm**2; BC[j + 1, j + 1] = sh**2; BC[j, j + 1] = BC[j + 1, j] = rho * sm * sh
BZ, BV = np.array(BZ), np.array(BV); BIC = np.linalg.inv(BC)

# ------------------------------------------------------------ supernovae (M marginalised analytically)
if O['sn'] == 'dovekie':
    d = os.path.join(EXT, 'sn_main', '4_DISTANCES_COVMAT')
    rows = [l.split() for l in open(os.path.join(d, 'DES-Dovekie_HD.csv')) if l.startswith('SN:')]
    hdr = [l.split() for l in open(os.path.join(d, 'DES-Dovekie_HD.csv')) if l.startswith('VARNAMES')][0]
    ix = {n: hdr.index(n) for n in ('zHD', 'zHEL', 'MU')}
    SZ = np.array([float(r[ix['zHD']]) for r in rows]); SZH = np.array([float(r[ix['zHEL']]) for r in rows])
    SMU = np.array([float(r[ix['MU']]) for r in rows])
    dd = np.load(os.path.join(d, 'STAT+SYS.npz'))
    n = int(dd['nsn'][0]); SIC = np.zeros((n, n)); SIC[np.triu_indices(n)] = dd['cov']
    il = np.tril_indices(n, -1); SIC[il] = SIC.T[il]
    assert n == len(SZ)
elif O['sn'] == 'sn5yr':
    d = os.path.join(EXT, 'sn5yr')
    t = np.genfromtxt(os.path.join(d, 'DES-SN5YR_HD.csv'), delimiter=',', names=True)
    SZ, SZH, SMU = t['zHD'], t['zHEL'], t['MU']
    import gzip
    v = np.loadtxt(gzip.open(os.path.join(d, 'STAT+SYS.txt.gz')))
    n = int(v[0]); C = v[1:].reshape(n, n) + np.diag(t['MUERR_FINAL']**2)
    SIC = np.linalg.inv(C)
else:
    SZ = np.zeros(0)
NS = len(SZ)
if NS:
    U = np.ones(NS)[:, None]
    if OFF: U = np.column_stack([U[:, 0], (SZ < 0.1).astype(float)])
    PSN = SIC - SIC @ U @ np.linalg.inv(U.T @ SIC @ U) @ U.T @ SIC     # nuisance offsets profiled

# ------------------------------------------------------------ release model
OMG_R = 2.4728e-5 * (1 + 0.2271 * (2.046 if MNU > 0 else 3.044))
OMG_NU = MNU / 93.14
FGRID = np.concatenate([np.linspace(0.0, 3.0, 31), np.linspace(3.5, 8.0, 10)])
_T = [REL.Irel_of_f(f) for f in FGRID]; IREL = np.array([x[0] for x in _T]); F1 = np.array([x[1] for x in _T])

def c2_solve(ombh2, H0):
    h2 = (H0 / 100)**2; omc = R_FORM * ombh2
    omde = h2 - ombh2 - omc - OMG_NU - OMG_R
    g = IREL - (omde + REL.ETA * omc * F1) / (REL.ETA * omc)
    if g[0] < 0 or g[-1] > 0: raise ValueError('no release history for this H0')
    k = np.where(np.sign(g[:-1]) != np.sign(g[1:]))[0][0]
    f = FGRID[k] - g[k] * (FGRID[k + 1] - FGRID[k]) / (g[k + 1] - g[k])
    from scipy.optimize import brentq
    f = brentq(lambda ff: REL.Irel_of_f(ff)[0] - (omde + REL.ETA * omc * REL.Irel_of_f(ff)[1]) / (REL.ETA * omc),
               FGRID[k], FGRID[k + 1], xtol=1e-5)
    I, Fr = REL.Irel_of_f(f)
    return f, I, Fr

def AL_calc(ombh2, H0, f):
    """Ratio of lensing-potential power with and without the clustering deficit, weighted over the CMB lensing kernel
    (sub-horizon linear growth on the same background)."""
    a_t, Fr, I = REL.history(f)
    h2 = (H0 / 100)**2; omc = R_FORM * ombh2; omb = ombh2
    lgr = np.log(a_t); o = np.argsort(lgr)
    Fi = lambda a: np.interp(np.log(a), lgr[o], Fr[o]); Ii = lambda a: np.interp(np.log(a), lgr[o], I[o])
    def rho(a): return (omb + omc + OMG_NU) * a**-3 + OMG_R * a**-4 + REL.ETA * omc * (Ii(a) - Fi(a) * a**-3) \
        + (h2 - omb - omc - OMG_NU - OMG_R - REL.ETA * omc * (Ii(1.0) - Fi(1.0)))
    def rhs(lna, y, true):
        a = np.exp(lna); r = rho(a); dl = 1e-4
        dlnE = 0.25 * (np.log(rho(a * np.exp(dl))) - np.log(rho(a * np.exp(-dl)))) / dl
        cl = (omb + omc * ((1 - REL.ETA * Fi(a)) if true else 1.0)) * a**-3
        return [y[1], -(2 + dlnE) * y[1] + 1.5 * cl / r * y[0]]
    sols = {t: solve_ivp(rhs, [np.log(1e-3), 0.0], [1e-3, 1e-3], args=(t,), dense_output=True, rtol=1e-8, atol=1e-12)
            for t in (False, True)}
    zz = np.linspace(0.01, 12, 600); a = 1 / (1 + zz)
    Dt = sols[True].sol(np.log(a))[0]; Dc = sols[False].sol(np.log(a))[0]
    # Weyl potential ~ (clustering density) x (growth) / a ; ratio squared
    r = ((omb + omc * (1 - REL.ETA * Fi(a))) / (omb + omc)) * Dt / Dc
    E = np.sqrt(rho(a) / h2)
    chi = np.concatenate([[0], np.cumsum(0.5 * (1 / E[1:] + 1 / E[:-1]) * np.diff(zz))]) + zz[0] / E[0]
    chis = 3.1
    w = ((chis - chi) / chis)**2 * (Dc / a)**2 / E * (chi < chis)   # Limber weight ~ W(chi)^2 P / chi^2, crude
    return float(np.sum(w * r**2) / np.sum(w))

# ------------------------------------------------------------ evaluation
def evaluate(p):
    info = {}
    omc = p['omch2'] if MODEL == 'LCDM' else R_FORM * p['ombh2']
    pars = camb.CAMBparams()
    if MNU > 0:
        pars.set_cosmology(H0=p['H0'], ombh2=p['ombh2'], omch2=omc, tau=p['tau'], mnu=MNU, num_massive_neutrinos=1)
    else:
        pars.set_cosmology(H0=p['H0'], ombh2=p['ombh2'], omch2=omc, tau=p['tau'], mnu=0.0, nnu=3.044,
                           num_massive_neutrinos=0)
    pars.InitPower.set_params(As=np.exp(p['lnAs']) * 1e-10, ns=p['ns'])
    if MODEL == 'REL':
        f, I, Fr = c2_solve(p['ombh2'], p['H0'])
        info.update(f=f, Irel=I, F1=Fr)
        de = camb.dark_energy.DarkEnergyPPF(); a_t, w_t, _ = REL.fluid_table(f); de.set_w_a_table(a_t, w_t)
        pars.DarkEnergy = de
        pars.Alens = p['_AL']
    pars.set_for_lmax(2600, lens_potential_accuracy=1)
    if ACC:
        pars.set_accuracy(AccuracyBoost=1.5, lAccuracyBoost=1.5, lSampleBoost=1.5)
    if O['nl'] == '0':
        pars.NonLinear = camb.model.NonLinear_none
        pars.set_accuracy(DoLateRadTruncation=False)
    r = camb.get_results(pars)
    cl = r.get_cmb_power_spectra(pars, CMB_unit='muK', lmax=2508)['total']
    cmb = cmb_vec(cl[2:2509, 0], cl[2:2509, 3], cl[2:2509, 1]) / p['cal']**2
    rd = r.get_derived_params()['rdrag']
    DM = r.comoving_radial_distance(BZ); DH = 299792.458 / r.hubble_parameter(BZ)
    bao = np.array([{'M': DM[i], 'H': DH[i], 'V': (BZ[i] * DM[i]**2 * DH[i])**(1 / 3)}[BQ[i]] / rd for i in range(len(BZ))])
    mu = 5 * np.log10((1 + SZH) * r.comoving_radial_distance(SZ)) + 25 if NS else np.zeros(0)
    info.update(rdrag=rd, Om=float((p['ombh2'] + omc + OMG_NU) / (p['H0'] / 100)**2))
    return cmb, bao, mu, info

def chi2(p, cmb, bao, mu):
    y = XDATA - cmb
    c = dict(cmb=float(y @ IC @ y), bao=float((BV - bao) @ BIC @ (BV - bao)),
             sn=float((SMU - mu) @ PSN @ (SMU - mu)) if NS else 0.0,
             prior=float(((p['tau'] - TAU0) / TAUS)**2 + (((p['cal'] - 1) / 0.0025)**2 if CALFREE else 0.0)))
    c['total'] = sum(c.values())
    return c

NAMES = {'LCDM': ['ombh2', 'omch2', 'H0', 'lnAs', 'ns', 'tau'], 'REL': ['ombh2', 'H0', 'lnAs', 'ns', 'tau']}[MODEL]
if CALFREE: NAMES = NAMES + ['cal']
STEP = dict(ombh2=1e-4, omch2=6e-4, H0=0.15, lnAs=6e-3, ns=2e-3, tau=4e-3, cal=1e-3)
P0 = dict(ombh2=0.02245, omch2=0.1185, H0=68.4 if MODEL == 'LCDM' else 69.0, lnAs=3.045, ns=0.968, tau=0.057, cal=1.0)

def set_AL(p):
    if MODEL != 'REL': return
    p['_AL'] = AL_calc(p['ombh2'], p['H0'], c2_solve(p['ombh2'], p['H0'])[0]) if O['AL'] == 'calc' else float(O['AL'])

def fit(iters=10):
    p = dict(P0); set_AL(p); hist = []
    W = IC
    for it in range(iters):
        cmb0, bao0, mu0, info0 = evaluate(p); c0 = chi2(p, cmb0, bao0, mu0); hist.append(c0['total'])
        J = {}
        for name in NAMES:
            q = dict(p); q[name] += STEP[name]
            if name == 'cal':
                J[name] = ((cmb0 * p['cal']**2 / q['cal']**2 - cmb0) / STEP[name], np.zeros(len(BV)), np.zeros(NS)); continue
            c1, b1, m1, _ = evaluate(q)
            J[name] = ((c1 - cmb0) / STEP[name], (b1 - bao0) / STEP[name], (m1 - mu0) / STEP[name])
        Jc = np.column_stack([J[n][0] for n in NAMES]); Jb = np.column_stack([J[n][1] for n in NAMES])
        A = Jc.T @ W @ Jc + Jb.T @ BIC @ Jb; b = Jc.T @ W @ (XDATA - cmb0) + Jb.T @ BIC @ (BV - bao0)
        if NS:
            Js = np.column_stack([J[n][2] for n in NAMES]); A += Js.T @ PSN @ Js; b += Js.T @ PSN @ (SMU - mu0)
        for k, n in enumerate(NAMES):
            if n == 'tau': A[k, k] += 1 / TAUS**2; b[k] += (TAU0 - p['tau']) / TAUS**2
            if n == 'cal': A[k, k] += 1 / 0.0025**2; b[k] += (1.0 - p['cal']) / 0.0025**2
        dp = np.linalg.solve(A, b)
        # backtracking on the true chi2
        lam = 1.0
        while True:
            q = dict(p)
            for k, n in enumerate(NAMES): q[n] += lam * dp[k]
            try:
                set_AL(q); cq = chi2(q, *evaluate(q)[:3])['total']
            except ValueError:
                cq = np.inf
            if cq <= c0['total'] + 1e-3 or lam < 0.1: break
            lam *= 0.5
        print(f"  it {it}: chi2 {c0['total']:.3f} -> {cq:.3f} (lam {lam})  " +
              ' '.join(f"{n}{dp[k]:+.2e}" for k, n in enumerate(NAMES)), flush=True)
        if cq > c0['total']:
            break
        p = q; hist.append(cq)
        if abs(c0['total'] - cq) < 0.01: break
    cmb, bao, mu, info = evaluate(p); c = chi2(p, cmb, bao, mu)
    return dict(model=MODEL, opts=O, params={k: float(v) for k, v in p.items()}, chi2=c, info=info, n_free=len(NAMES),
                hist=hist)

if __name__ == '__main__':
    t0 = time.time(); res = fit(); res['wall_s'] = round(time.time() - t0)
    tag = MODEL + '_' + '_'.join(f"{k}{v}" for k, v in O.items() if k not in ('tag',) and not (k == 'nl' and v == '1')) + (('_' + O['tag']) if O['tag'] else '')
    os.makedirs(os.path.join(HERE, 'run'), exist_ok=True)
    json.dump(res, open(os.path.join(HERE, 'run', tag + '.json'), 'w'), indent=1)
    print(json.dumps(dict(tag=tag, chi2=res['chi2'], params=res['params'], info=res['info'])))
