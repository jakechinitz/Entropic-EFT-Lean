"""KiDS-1000 isolated lenses (B21, 4 bins x 15 radii, full covariance), population forward model of
Highest-leverage tensions 2026-10-28/lensing (fwd.py, hybrid.py). Adds the MOND row.
Every model: same population, same hot CGM (f_hot = 0.2), same galaxy point mass, same 8-amplitude environment.
Nuisances: NFW gets a global halo-mass shift and concentration factor (as in REVIEW_CORRECTIONS.md, which
reports NFW 132.7 and the support-limited stock 140.3). MOND / uncapped law get a global baryonic-mass shift."""
import sys, json, numpy as np
sys.argv = ['x', '0.2']
import fwd as F
from scipy.optimize import brentq, nnls, minimize
FH, SO, SS, DM = 0.2, 0.15, 0.15, 0.0
TC = brentq(lambda tc: F.obs_mean_mgal(0, sig_obs=SO, tc=tc, dlogm=DM) - F.MGAL_B21[0], 8.6, 10.6)
W = [F.population(b, sig_obs=SO, sig_shmr=SS, tc=TC, dlogm=DM) for b in range(4)]
Ws = sum(W); ki = np.where(Ws.sum(1) > 1e-7)[0]; kj = np.where(Ws.sum(0) > 1e-7)[0]
LMG = F.mgal(F.LMS); RG = F.RG
print('pairs', len(ki), len(kj), flush=True)
LIN = F.esd_lin(); OUT = np.zeros((4, F.NR))
for b in range(4):
    w = W[b].sum(0); js = np.where(w > 1e-4 * w.max())[0]
    OUT[b] = sum(w[j] * F.esd_outer(j) for j in js) / w[js].sum()
beff = [float(np.sum(W[b] * F.BIAS[None, :])) for b in range(4)]
def mask(v, b): z = np.zeros(60); z[b * F.NR:(b + 1) * F.NR] = v; return z
A = np.column_stack([mask(beff[b] * LIN, b) for b in range(4)] + [mask(OUT[b], b) for b in range(4)])
L = np.linalg.cholesky(F.ICOV)
def chi2_env(p):
    x, _ = nnls(L.T @ A, L.T @ (F.DATA - p)); r = F.DATA - p - A @ x; return float(r @ F.ICOV @ r)
def stack(Ei, Ej):
    """Ei: dict i -> ESD (depends on i only), Ej: dict j -> ESD (depends on j only)."""
    out = np.zeros(60)
    for b in range(4):
        wi = W[b].sum(1); wj = W[b].sum(0)
        out[b * F.NR:(b + 1) * F.NR] = sum(wi[i] * Ei[i] for i in ki if wi[i] > 0) + sum(wj[j] * Ej[j] for j in kj if wj[j] > 0)
    return out
mu = lambda q: np.log(1 + q) - q / (1 + q)
HOT = {j: F.esd_from_menc(FH * F.FB * 10**F.LMH[j] * np.minimum(RG / F.R200[j], 1.0)) for j in kj}
PT = {i: 10**LMG[i] / (np.pi * F.RAD**2) / 1e12 for i in ki}
def nfw_profile(dlm, cf):
    E = {}
    for j in kj:
        M = 10**(F.LMH[j] + dlm); r200 = F.R200[j] * 10**(dlm / 3); rsp = F.RSP[j] * 10**(dlm / 3); c = F.CONC[j] * cf
        E[j] = F.esd_from_menc((1 - F.FB) * M * mu(np.minimum(RG, rsp) / (r200 / c)) / mu(c)) + HOT[j]
    return stack(PT, E)
def law_profile(dlb, a0_mpc, nu):
    Ei = {}
    for i in ki:
        Mb = 10**(LMG[i] + dlb)
        Ei[i] = F.esd_from_menc(Mb * (nu(F.G * Mb / RG**2 / a0_mpc) - 1)) + Mb / (np.pi * F.RAD**2) / 1e12
    return stack(Ei, HOT)
nu_exp = lambda y: 1 / (1 - np.exp(-np.sqrt(y)))
nu_simple = lambda y: 0.5 + np.sqrt(0.25 + 1 / y)
A0_MOND = 1.2e-10 / F.KMS2_MPC_TO_MS2
res = {}
res['NFW_rigid'] = chi2_env(nfw_profile(0, 1)); print('NFW rigid', res['NFW_rigid'], flush=True)
f = lambda p: chi2_env(nfw_profile(p[0], 10**p[1]))
best = min((minimize(f, x0, method='Nelder-Mead', options=dict(xatol=1e-3, fatol=1e-2)) for x0 in ([0, 0], [0.2, -0.2], [-0.2, -0.3])), key=lambda m: m.fun)
res['NFW_2nuis'] = dict(chi2=best.fun, dlogMh=best.x[0], cfac=10**best.x[1]); print('NFW 2 nuis', res['NFW_2nuis'], flush=True)
for lab, a0, nu in [('law_stock_a0z', F.A0_MPC, nu_exp), ('MOND_exp_1.2', A0_MOND, nu_exp), ('MOND_simple_1.2', A0_MOND, nu_simple)]:
    r0 = chi2_env(law_profile(0, a0, nu))
    m = minimize(lambda p: chi2_env(law_profile(p[0], a0, nu)), [0.0], method='Nelder-Mead', options=dict(xatol=1e-3, fatol=1e-2))
    res[lab] = dict(chi2_no_nuisance=r0, chi2_mass_shift=m.fun, dlogMb=m.x[0]); print(lab, res[lab], flush=True)
json.dump(res, open('kids_mond.json', 'w'), indent=1)
