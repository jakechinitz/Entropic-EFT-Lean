import numpy as np, json, sys, time
from scipy.optimize import brentq, minimize_scalar
sys.path.insert(0, '/home/claude/lens')
import fwd as F

SIG_OBS = float(sys.argv[1]) if len(sys.argv) > 1 else 0.15
SIG_SHMR = float(sys.argv[2]) if len(sys.argv) > 2 else 0.15
DLOGM = float(sys.argv[3]) if len(sys.argv) > 3 else 0.0     # observed - true systematic
TAG = f'so{SIG_OBS}_ss{SIG_SHMR}_dm{DLOGM}'

# completeness turnover chosen so that bin 1 reproduces B21's log<M_gal> = 10.14
f = lambda tc: F.obs_mean_mgal(0, sig_obs=SIG_OBS, tc=tc, dlogm=DLOGM) - F.MGAL_B21[0]
TC = brentq(f, 8.6, 10.6)
means = [F.obs_mean_mgal(b, sig_obs=SIG_OBS, tc=TC, dlogm=DLOGM) for b in range(4)]
print('completeness turnover', round(TC, 3), ' model log<Mgal> per bin', np.round(means, 3), ' B21', F.MGAL_B21)

W = [F.population(b, sig_obs=SIG_OBS, sig_shmr=SIG_SHMR, tc=TC, dlogm=DLOGM) for b in range(4)]
Wsum = sum(W)
keep_ms = np.where(Wsum.sum(1) > 1e-7)[0]; keep_mh = np.where(Wsum.sum(0) > 1e-7)[0]
LMG = F.mgal(F.LMS)

t0 = time.time()
E_rar = {i: F.esd_rar(LMG[i]) for i in keep_ms}
E_nfw = {j: F.esd_nfw(j) for j in keep_mh}
BUD = {'200c': np.exp(-F.ETA) * (1 - F.FB) * 10**F.LMH, 'sp': np.exp(-F.ETA) * (1 - F.FB) * F.MSP}
E_cap = {k: {} for k in BUD}
for i in keep_ms:
    for j in keep_mh:
        if Wsum[i, j] < 1e-9: continue
        for k in BUD:
            E_cap[k][(i, j)] = F.esd_rar(LMG[i], BUD[k][j])
print('profiles', round(time.time() - t0, 1), 's')

def stack(b, kind):
    w = W[b]; out = np.zeros(F.NR)
    for i in keep_ms:
        for j in keep_mh:
            if Wsum[i, j] < 1e-9: continue
            if kind == 'RAR': e = E_rar[i]
            elif kind == 'NFW': e = F.esd_nfw_cache[j] + 10**LMG[i] / (np.pi * F.RAD**2) / 1e12
            else: e = E_cap[kind[4:]][(i, j)]
            out += w[i, j] * e
    return out
F.esd_nfw_cache = E_nfw
LIN = F.esd_lin()
BEFF = [float(np.sum(W[b] * F.BIAS[None, :])) for b in range(4)]
MH_MEAN = [float(np.log10(np.sum(W[b] * 10**F.LMH[None, :]))) for b in range(4)]
MH_INV = [float(F.LMH[np.argmin(abs(F.moster(F.LMH) - F.LMS[np.argmin(abs(LMG - F.MGAL_B21[b]))]))]) for b in range(4)]
print('log <M200c> per bin', np.round(MH_MEAN, 3), ' inverted SHMR at B21 mean', MH_INV, ' b_eff', np.round(BEFF, 2))

MODELS = ['RAR', 'NFW', 'CAP_200c', 'CAP_sp']
PRED = {m: np.concatenate([stack(b, m) for b in range(4)]) for m in MODELS}
T2H = np.concatenate([BEFF[b] * LIN for b in range(4)])
inner = np.tile(F.RAD < 0.31, 4)

def chi2(pred, sel=None):
    if sel is None: d = F.DATA - pred; return float(d @ F.ICOV @ d)
    C = F.COV[np.ix_(sel, sel)]; d = (F.DATA - pred)[sel]; return float(d @ np.linalg.solve(C, d))

res = {'tag': TAG, 'tc': TC, 'mean_mgal': means, 'logMh_mean': MH_MEAN, 'logMh_inverted': MH_INV, 'b_eff': BEFF, 'models': {}}
for m in MODELS:
    p = PRED[m]
    r = {'chi2_inner_noenv': chi2(p, inner), 'chi2_all_noenv': chi2(p)}
    # best common environment amplitude A >= 0 (all radii)
    num = T2H @ F.ICOV @ (F.DATA - p); den = T2H @ F.ICOV @ T2H; A = max(0.0, num / den)
    r.update(A_env=A, A_env_err=float(1 / np.sqrt(den)), chi2_all_env=chi2(p + A * T2H), chi2_inner_env=chi2(p + A * T2H, inner))
    # residual pulls by bin at R > 0.3 without env
    pulls = (F.DATA - p) / np.sqrt(np.diag(F.COV))
    r['pulls_outer_noenv'] = [np.round(pulls[b * F.NR:(b + 1) * F.NR][F.RAD > 0.3], 1).tolist() for b in range(4)]
    res['models'][m] = r
    print(f"{m:9s} chi2(R<0.31, 32 pts) {r['chi2_inner_noenv']:7.1f} | all 60 no env {r['chi2_all_noenv']:7.1f} | "
          f"env A={A:.2f}+-{r['A_env_err']:.2f}: all {r['chi2_all_env']:7.1f} inner {r['chi2_inner_env']:6.1f}")
res['pred'] = {m: PRED[m].tolist() for m in MODELS}; res['T2H'] = T2H.tolist()
json.dump(res, open(f'/home/claude/lens/out_{TAG}.json', 'w'), indent=1)
