import json, numpy as np, itertools, sys
fn = sys.argv[1]; g = json.load(open(fn)); lM = np.array(sorted(float(k) for k in g))
K = [k for k in g[str(lM[0])] if k != 'F0']; I = np.array([[g[str(m)][k] for k in K] for m in lM]); Im = I.mean(1)
def mix(pts):
    xs, cs = np.array(pts).T; grid = np.linspace(xs[0], xs[-1], 400); c = np.interp(grid, xs, cs); w = np.diff(c); mid = .5*(grid[1:]+grid[:-1])
    return float(np.sum(w*np.interp(mid, lM, Im))/np.sum(w))
vals = []
for x0, f7, x50, x1 in itertools.product([6.7, 6.85, 7.0], [0.05, 0.1, 0.2], [7.9, 8.0, 8.1], [8.3, 8.5, 8.7]):
    pts = [(x0 - (0.01 if x0 >= 7.0 else 0), 0), (7.0, f7), (x50, 0.5), (x1, 1.0)] if x0 < 7.0 else [(6.99, 0), (7.0, f7), (x50, 0.5), (x1, 1.0)]
    vals.append(mix(pts))
vals = np.array(vals); print(fn, 'Renaissance-curve variations: I_rel median %.1f, range %.1f-%.1f, 16-84%% %.1f-%.1f' % (np.median(vals), vals.min(), vals.max(), *np.percentile(vals, [16, 84])))
