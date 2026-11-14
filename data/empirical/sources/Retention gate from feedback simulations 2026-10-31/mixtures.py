import json, numpy as np, sys
ETA = 0.0298668443935; wb = 0.02238; wc = 5.333 * wb; wnu = 0.06 / 93.14
def cosmo(I, F0):
    wL = ETA * wc * I; h2 = wb + wc * (1 - ETA * F0) + wnu + wL
    return np.sqrt(h2), wL / h2
for fn in sys.argv[1:]:
    g = json.load(open(fn)); lM = np.array(sorted(float(k) for k in g))
    K = [k for k in g[str(lM[0])] if k != 'F0']
    I = np.array([[g[str(m)][k] for k in K] for m in lM]); F0 = np.array([g[str(m)]['F0'] for m in lM])
    Im = I.mean(1); Ilo, Ihi = I.min(1), I.max(1)
    def at(x): return np.interp(x, lM, Im), np.interp(x, lM, Ilo), np.interp(x, lM, Ihi), np.interp(x, lM, F0)
    x94 = np.interp(-94.2, -Im, lM)
    print(f'== {fn}: constant-mass gate giving I_rel=94.2: log M = {x94:.2f}')
    def mix(cdf_pts):
        xs, cs = np.array(cdf_pts).T
        grid = np.linspace(xs[0], xs[-1], 400); c = np.interp(grid, xs, cs); w = np.diff(c); mid = 0.5 * (grid[1:] + grid[:-1])
        return [float(np.sum(w * np.interp(mid, lM, col)) / np.sum(w)) for col in (Im, Ilo, Ihi, F0)]
    rows = {
      'sharp 10^7.0': at(7.0), 'sharp 10^7.5 (MW sat M50, Nadler)': at(7.51), 'sharp 10^7.56 (GRUMPY M50)': at(7.56),
      'sharp 10^7.93 (Nadler 95% upper)': at(7.93), 'sharp 10^8.0 (Renaissance active-SF 50%)': at(8.0),
      'Renaissance active-SF occupation, soft': mix([(6.85, 0), (7.0, 0.1), (8.0, 0.5), (8.5, 1.0)]),
    }
    for k, (i, lo, hi, f0) in rows.items():
        h, OL = cosmo(i, f0)
        print(f'  {k:42s} I_rel={i:6.1f} [{lo:6.1f},{hi:6.1f}]  h={h:.3f}  Omega_L={OL:.3f}')
