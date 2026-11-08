"""Effective retention gate measured in the Gadget-4 run (Release zoom/run): fraction of FOF groups holding
condensed baryons (star-forming gas or stars) as a function of virial velocity, per snapshot.
V_vir from the FOF mass with the Bryan-Norman overdensity of the run cosmology (Om 0.3111, h 0.6766)."""
import h5py, glob, json, numpy as np
Om, h = 0.3111, 0.6766; G = 4.30091e-9
def Hz(z): return 100 * h * np.sqrt(Om * (1 + z) ** 3 + 1 - Om)
def dc(z):
    x = Om * (1 + z) ** 3 / (Om * (1 + z) ** 3 + 1 - Om) - 1; return 18 * np.pi ** 2 + 82 * x - 39 * x * x
def Vvir(M, z): return (G * M * Hz(z) * np.sqrt(dc(z) / 2)) ** (1 / 3)
edges = np.array([6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 23, 27, 35])
out = {}; allV = []; allC = []; allz = []
for fn in sorted(glob.glob('fof/fof_tab_*.hdf5')):
    f = h5py.File(fn, 'r'); z = f['Header'].attrs['Redshift']; g = f['Group']
    if f['Header'].attrs['Ngroups_Total'] == 0: continue
    M = g['GroupMass'][:] * 1e10 / h; MT = g['GroupMassType'][:] * 1e10 / h; sfr = g['GroupSFR'][:]
    ngas = g['GroupLenType'][:, 0]
    V = Vvir(M, z); cond = (sfr > 0) | (MT[:, 4] > 0)
    allV += list(V); allC += list(cond); allz += [z] * len(V)
    row = []
    for lo, hi in zip(edges[:-1], edges[1:]):
        m = (V >= lo) & (V < hi)
        row.append((int(m.sum()), float(cond[m].mean()) if m.sum() else None))
    out[f'{z:.2f}'] = dict(n=len(V), Vmax=float(V.max()), bins=row, min_ngas_cond=int(ngas[cond].min()) if cond.any() else None)
allV, allC, allz = map(np.array, (allV, allC, allz))
print('V bins:', list(zip(edges[:-1], edges[1:])))
for z, r in out.items():
    print(z, 'n', r['n'], 'Vmax %.1f' % r['Vmax'], ' '.join('-' if f is None else f'{f:.2f}({n})' for n, f in r['bins']))
# pooled by redshift band, logistic V50
from scipy.optimize import minimize
def v50(V, C):
    nll = lambda p: -np.sum(C * np.log(1 / (1 + np.exp(-(np.log(V) - p[0]) / p[1])) + 1e-12) + (1 - C) * np.log(1 - 1 / (1 + np.exp(-(np.log(V) - p[0]) / p[1])) + 1e-12))
    r = minimize(nll, [np.log(14), 0.1], method='Nelder-Mead'); return np.exp(r.x[0]), r.x[1]
res = {}
for lo, hi in ((6, 7.5), (7.5, 9), (9, 11), (11, 15)):
    m = (allz >= lo) & (allz < hi)
    if m.sum() > 20 and allC[m].any():
        V50, w = v50(allV[m], allC[m].astype(float)); res[f'{lo}-{hi}'] = dict(V50=V50, width_dex=w / np.log(10), n=int(m.sum()), ncond=int(allC[m].sum()))
        print(f'z {lo}-{hi}: V50 = {V50:.2f} km/s, width {w/np.log(10):.3f} dex, groups {m.sum()}, with condensed baryons {allC[m].sum()}')
json.dump(dict(per_snapshot=out, V50=res, edges=edges.tolist()), open('gate_from_run.json', 'w'), indent=1)
