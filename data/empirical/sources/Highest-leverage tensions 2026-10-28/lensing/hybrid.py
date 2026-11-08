"""Support-limited stock (Sec. 18 support rule applied to isolated lenses).
The carrier's support ends where its records (stars + cold gas, M_gal) stop dominating the enclosed baryonic
mass. Hot CGM gas: M_hot = f_hot * f_b * M200c, isothermal (M_hot(<r) = M_hot r / r200) out to r200.
Support radius r_s = min(r200 * M_gal / M_hot, r_sp).
Stock (total (1-f_b) M200c NFW truncated at r_sp, i.e. the same total as the NFW model):
 inside r_s the carried stock M_N(<r_s) relaxes to the law excess, capped at M_N(<r_s) (any surplus stays as a shell at r_s);
 outside r_s the stock is uncarried and keeps its NFW distribution.
Hot gas mass is added (Newtonian) to every model, including NFW and the full-cap model, for a like-for-like comparison.
usage: python3 hybrid.py f_hot [sig_obs sig_shmr dlogm]"""
import sys, json, numpy as np
sys.path.insert(0, '/home/claude/lens'); import fwd as F
from scipy.optimize import brentq, nnls
FH = float(sys.argv[1]); SO, SS, DM = [float(x) for x in sys.argv[2:5]] if len(sys.argv) > 4 else (0.15, 0.15, 0.0)
TC = brentq(lambda tc: F.obs_mean_mgal(0, sig_obs=SO, tc=tc, dlogm=DM) - F.MGAL_B21[0], 8.6, 10.6)
W = [F.population(b, sig_obs=SO, sig_shmr=SS, tc=TC, dlogm=DM) for b in range(4)]
Ws = sum(W); ki = np.where(Ws.sum(1) > 1e-7)[0]; kj = np.where(Ws.sum(0) > 1e-7)[0]
LMG = F.mgal(F.LMS); RG = F.RG
def nfw_menc(j):
    c = F.CONC[j]; r200 = F.R200[j]; rs = r200 / c; m = lambda q: np.log(1 + q) - q / (1 + q)
    return (1 - F.FB) * 10**F.LMH[j] * m(np.minimum(RG, F.RSP[j]) / rs) / m(c)
def hot_menc(j):
    Mh = FH * F.FB * 10**F.LMH[j]; return Mh * np.minimum(RG / F.R200[j], 1.0)
nu = lambda y: 1 / (1 - np.exp(-np.sqrt(y)))
out = {k: np.zeros(60) for k in ('RAR', 'NFW', 'CAP_sp', 'HYB')}; RS = [[] for _ in range(4)]
cache = {}
for i in ki:
    Mb = 10**LMG[i]; ex = Mb * (nu(F.G * Mb / RG**2 / F.A0_MPC) - 1); pt = Mb / (np.pi * F.RAD**2) / 1e12
    for j in kj:
        if Ws[i, j] < 1e-9: continue
        MN = nfw_menc(j); MH = hot_menc(j)
        Mhot = FH * F.FB * 10**F.LMH[j]
        rs = min(F.R200[j] * Mb / Mhot if Mhot > 0 else 1e9, F.RSP[j])
        MNs = np.interp(rs, RG, MN)
        hyb = np.where(RG < rs, np.minimum(ex, MNs), MN)
        cap = np.minimum(ex, np.exp(-F.ETA) * (1 - F.FB) * F.MSP[j])
        e_h = F.esd_from_menc(MH)
        E = {'RAR': F.esd_from_menc(ex) + e_h + pt, 'NFW': F.esd_from_menc(MN) + e_h + pt, 'CAP_sp': F.esd_from_menc(cap) + e_h + pt, 'HYB': F.esd_from_menc(hyb) + e_h + pt}
        for b in range(4):
            if W[b][i, j] < 1e-12: continue
            for k in out: out[k][b * F.NR:(b + 1) * F.NR] += W[b][i, j] * E[k]
            RS[b].append((W[b][i, j], rs))
# environment templates as in envfit
LIN = F.esd_lin(); OUT = np.zeros((4, F.NR))
for b in range(4):
    w = W[b].sum(0); js = np.where(w > 1e-4 * w.max())[0]
    OUT[b] = sum(w[j] * F.esd_outer(j) for j in js) / w[js].sum()
beff = [float(np.sum(W[b] * F.BIAS[None, :])) for b in range(4)]
def mask(v, b): z = np.zeros(60); z[b * F.NR:(b + 1) * F.NR] = v; return z
T = [mask(beff[b] * LIN, b) for b in range(4)] + [mask(OUT[b], b) for b in range(4)]
L = np.linalg.cholesky(F.ICOV); A = np.column_stack(T)
inner = np.tile(F.RAD < 0.31, 4)
def c2(r, sel=None):
    if sel is None: return float(r @ F.ICOV @ r)
    C = F.COV[np.ix_(sel, sel)]; return float(r[sel] @ np.linalg.solve(C, r[sel]))
print(f'f_hot {FH}  pop {SO} {SS} {DM}')
print('  support radius r_s (weighted median, kpc) per bin:', [round(1e3 * float(np.median([r for w, r in RS[b]])), 0) for b in range(4)])
for k, p in out.items():
    x, _ = nnls(L.T @ A, L.T @ (F.DATA - p)); r = F.DATA - p - A @ x
    print(f'  {k:7s} inner(32) {c2(F.DATA - p, inner):7.1f}  all no env {c2(F.DATA - p):7.1f}  all + env(8) {c2(r):7.1f}')
json.dump({k: v.tolist() for k, v in out.items()}, open(f'/home/claude/lens/hyb_{FH}_{SO}_{SS}_{DM}.json', 'w'))
