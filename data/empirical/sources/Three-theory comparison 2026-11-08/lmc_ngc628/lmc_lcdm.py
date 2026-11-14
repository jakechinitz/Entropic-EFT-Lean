"""LCDM abundance-matched LMC halo: enclosed mass at 30 and 50 kpc (isolated, untruncated NFW + baryons),
for comparison with the stock-model 5.03 / 8.29 x 1e10 and the stream / outer-halo inferences."""
import numpy as np, json
G = 4.300917270e-6
RHO200 = 200 * 3 * (70 / 1000)**2 / (8 * np.pi * G)
def moster(lM):
    M1, N, b, g = 10**11.590, 0.0351, 1.376, 0.608; M = 10**lM
    return np.log10(2 * N * M / ((M / M1)**(-b) + (M / M1)**g))
grid = np.linspace(9, 14, 5001)
def inv(lms): return np.interp(lms, moster(grid), grid)
def c_dm(lM): return 10**(0.905 - 0.101 * (lM - 12 + np.log10(0.7)))
def menc(r, lM, c):
    M = 10**lM; r200 = (3 * M / (4 * np.pi * RHO200))**(1 / 3); mu = lambda t: np.log1p(t) - t / (1 + t)
    return M * mu(c * r / r200) / mu(c), r200
Mstar, Mbar = 2.7e9, 3.0e9
lM0 = inv(np.log10(Mstar)); out = {'M200_median_from_Moster13': 10**lM0}
rows = []
for dM in (-0.3, 0.0, 0.3):
    for dc in (-0.11, 0.0, 0.11):
        lM = lM0 + dM; c = c_dm(lM) * 10**dc
        m30, r200 = menc(30, lM, c); m50, _ = menc(50, lM, c)
        fb = 1 - Mbar / 10**lM   # halo mass excludes baryons; baryons added as enclosed point mass
        rows.append(dict(dlogM=dM, dlogc=dc, M200=10**lM, c=c, r200=r200, M30=(m30 * fb + Mbar) / 1e10, M50=(m50 * fb + Mbar) / 1e10))
out['grid'] = rows
for r in rows: print({k: round(v, 3) if isinstance(v, float) and v < 1e3 else f'{v:.3g}' for k, v in r.items()})
json.dump(out, open('lmc_lcdm.json', 'w'), indent=1)
