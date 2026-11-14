import json, numpy as np, sys
from scipy.optimize import minimize_scalar
from multiprocessing import Pool
import sparc_prior_sens as P2, sparc_compare as S
base = P2.base
groups = {'Vflat<80': [r for r in S.selected if 0 < r['Vflat'] < 80], '80-150': [r for r in S.selected if 80 <= r['Vflat'] < 150],
          'Vflat>=150': [r for r in S.selected if r['Vflat'] >= 150], 'no Vflat': [r for r in S.selected if r['Vflat'] <= 0]}
out = []
with Pool(2) as P:
    for floor in (0.0, 5.0):
        for g, sample in groups.items():
            kw = dict(base, floor=floor)
            f = lambda la: P2.total(10**la * 1e-10, sample, kw, P)[0]
            m = minimize_scalar(f, bounds=(np.log10(0.4), np.log10(3)), method='bounded', options=dict(xatol=1e-3))
            tc = P2.total(P2.A0C, sample, kw, P)[0]
            out.append(dict(group=g, floor=floor, n=len(sample), a0_best=10**m.x * 1e-10, dchi2_cosmo=tc - m.fun))
            print(g, floor, len(sample), round(10**m.x, 3), round(tc - m.fun, 1), flush=True)
json.dump(out, open('sparc_split.json', 'w'), indent=1)
