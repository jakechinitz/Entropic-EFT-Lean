"""Exact positivity- and budget-constrained minimiser of the spherical mismatch functional.

Domain [r_in, R].  Stock enclosed mass Y(r) = M_s(<r); target T(r) = r^2 J(g_b(r)) / G.
  E_mis = (1/2G) int (g_s - J)^2 r^2 dr = (G/2) int (Y - T)^2 / r^2 dr.
Constraints: rho_s >= 0  <=>  Y non-decreasing;  Y >= 0;  Y(R) <= M (stock beyond R does not
act inside R in spherical symmetry, so unused budget is parked outside the domain).
This is weighted isotonic regression of T with weight w = G/(2 r^2), with box constraint
[0, M].  For isotonic regression, clipping the unconstrained solution to the box is optimal,
so  Y* = clip(isotonic_w(T), 0, M).  The minimiser is unique because the objective is strictly
convex in Y in the weighted L2 norm.

Checks
  1. GPT's shell counterexample: T = (2,1,2), equal weights -> (1.5,1.5,2), shell masses
     (1.5, 0, 0.5), E = 1/2 < 5/9 for the clipped-renormalised profile.
  2. Benchmarks with monotone T: Y* = T up to the budget edge, then M.
  3. A dense Plummer core (1e12 Msun, b = 2 kpc), where the response density is negative: compare Y* with the O.3
     clipped-and-renormalised profile.
"""
import numpy as np, math, json
import static_analysis as S
G = S.G

def pava(y, w):
    """Weighted isotonic (non-decreasing) regression by pool-adjacent-violators."""
    vals, wts, cnt = [], [], []
    for yi, wi in zip(y, w):
        vals.append(yi); wts.append(wi); cnt.append(1)
        while len(vals) > 1 and vals[-2] > vals[-1]:
            v = (vals[-2]*wts[-2] + vals[-1]*wts[-1])/(wts[-2]+wts[-1])
            ww = wts[-2]+wts[-1]; c = cnt[-2]+cnt[-1]
            vals[-2:] = [v]; wts[-2:] = [ww]; cnt[-2:] = [c]
    return np.repeat(vals, cnt)

def minimiser(r, T, M):
    w = G/(2*r**2)*np.gradient(r)
    return np.clip(pava(T, w), 0, M)

def emis(r, Y, T):
    return float(np.trapezoid(G*(Y-T)**2/(2*r**2), r))

def clip_renorm(r, T, M):
    """O.3 target: positive part of the response density, renormalised to the same mass."""
    dT = np.diff(T, prepend=0.0)
    pos = np.maximum(dT, 0)
    Mtarget = min(M, T.max())
    return np.cumsum(pos)*Mtarget/pos.sum()

if __name__ == '__main__':
    out = {}
    # 1. counterexample (discrete, equal weights)
    T3 = np.array([2.0, 1.0, 2.0])
    iso = pava(T3, np.ones(3))
    out['counterexample'] = dict(isotonic_enclosed=iso.tolist(), shell_masses=np.diff(iso, prepend=0).tolist(),
                                 E_isotonic=float(((iso-T3)**2)[:2].sum()),
                                 E_clip_renorm=float(((np.cumsum([4/3, 0, 2/3])-T3)**2)[:2].sum()))

    # 2. benchmarks
    for case in ('MW', 'dwarf', 'massive_spiral'):
        b = S.BENCH[case]; parts = b['parts']; Mbf = S.Mb_of(parts)
        Mbt = sum(p[1] for p in parts); M200 = b.get('M200') or S.moster_M200(Mbt)
        M = 0.84*M200
        r = np.geomspace(0.5, 200.0, 20000)
        T = r**2*S.J(G*Mbf(r)/r**2)/G
        Y = minimiser(r, T, M)
        edge = float(r[np.argmax(Y >= M)]) if (Y >= M).any() else None
        out[case] = dict(budget=M, T_monotone=bool(np.all(np.diff(T) >= 0)), budget_edge_kpc=edge,
                         Emis_floor=emis(r, Y, T), Emis_clip=emis(r, np.minimum(clip_renorm(r, T, M), M), T))

    # 3. compact core with a negative response density
    # dense Plummer core: the response density turns negative only where the peak x exceeds
    # ~100 (audit scan); 1e12 Msun with b = 2 kpc is the largest case found (~7e-7)
    Mpl, bpl = 1.0e12, 2.0
    Mbf = lambda rr: Mpl*rr**3/(rr**2+bpl**2)**1.5
    r = np.geomspace(0.02, 50.0, 40000)
    T = r**2*S.J(G*Mbf(r)/r**2)/G
    M = T[-1]                          # budget equal to the response mass inside the domain
    dT = np.diff(T)
    neg = r[1:][dT < 0]
    Y = minimiser(r, T, M); Yc = clip_renorm(r, T, M)
    out['compact_core'] = dict(negative_response_range_kpc=[float(neg.min()), float(neg.max())] if neg.size else None,
                               negative_mass=float(-dT[dT < 0].sum()),
                               Emis_isotonic=emis(r, Y, T), Emis_clip_renorm=emis(r, Yc, T),
                               max_enclosed_difference=float(np.max(np.abs(Y-Yc))),
                               g_offset_isotonic_dex_max=float(np.max(np.abs(np.log10((G*(Mbf(r)+Y)/r**2)/(G*Mbf(r)/r**2+S.J(G*Mbf(r)/r**2)))))),
                               g_offset_clip_dex_max=float(np.max(np.abs(np.log10((G*(Mbf(r)+Yc)/r**2)/(G*Mbf(r)/r**2+S.J(G*Mbf(r)/r**2)))))))
    print(json.dumps(out, indent=1))
    json.dump(out, open('/tmp/claude-0/c25/minimizer_results.json', 'w'), indent=1)
