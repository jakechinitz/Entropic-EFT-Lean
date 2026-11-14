import sys, json, time, numpy as np
exec(open('nuis.py').read().split("res = {}")[0])
from scipy.optimize import minimize_scalar
# NFW with the concentration factor held at >= 0.6 (the review's stated range)
r06 = minimize_scalar(lambda d: chi2_env(nfw_profile(d, 0.6)), bounds=(-0.3, 0.6), method='bounded')
print('NFW cf=0.6 profiled dlogMh', r06.x, r06.fun, flush=True)
# MOND with the hot CGM inside the MOND source (all baryons boosted), per (i, j) pair
def mond_full(dlb, a0, nu):
    out = np.zeros(60)
    for b in range(4):
        acc = np.zeros(F.NR)
        for i in ki:
            Mg = 10**(LMG[i] + dlb)
            for j in kj:
                w = W[b][i, j]
                if w < 1e-12: continue
                Mb = Mg + FH * F.FB * 10**F.LMH[j] * np.minimum(RG / F.R200[j], 1.0)
                acc += w * (F.esd_from_menc(Mb * nu(F.G * Mb / RG**2 / a0) - Mg) + Mg / (np.pi * F.RAD**2) / 1e12)
        out[b * F.NR:(b + 1) * F.NR] = acc
    return out
t = time.time(); p0 = mond_full(0, A0_MOND, nu_exp); print('MOND full no nuisance', chi2_env(p0), time.time() - t, flush=True)
res = {'NFW_cf0.6': dict(chi2=r06.fun, dlogMh=r06.x)}
grid = {}
for d in (-0.1, 0.0, 0.05, 0.1, 0.15):
    grid[d] = chi2_env(mond_full(d, A0_MOND, nu_exp)); print('MOND full', d, grid[d], flush=True)
res['MOND_exp_1.2_hot_boosted'] = {str(k): v for k, v in grid.items()}
json.dump(res, open('kids_mond2.json', 'w'), indent=1)
