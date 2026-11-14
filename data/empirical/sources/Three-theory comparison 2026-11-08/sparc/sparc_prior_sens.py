"""How much of SPARC's preference for a0 below the cosmological 1.249e-10 survives other nuisance priors?
Same 130 galaxies and law as sparc_compare.py; only the priors (or the sample) change.
For each variant: best global a0 for the exponential law, its formal and chi2/dof-scaled 1-sigma range,
and the chi2 cost of fixing a0 at the cosmological value 1.2494e-10."""
import json, sys
import numpy as np
from scipy.optimize import least_squares, minimize_scalar
from multiprocessing import Pool
sys.argv = ['x']
import sparc_compare as S

def fit_gal(row, a0, floor, Ud, sU, Ub, inc_mult, dist_mult):
    arr = row['array']; rr, v, ev, vg, vd, vb = arr[:, :6].T
    good = (rr > 0) & (v > 0) & (ev > 0)
    rr, v, ev, vg, vd, vb = [x[good] for x in [rr, v, ev, vg, vd, vb]]
    ds = max(row['Derr'] / row['D'], .01) * dist_mult; si = max(row['incerr'], .1) * inc_mult
    def residual(p):
        ld, di, ldisk, lbulge = p
        dd = np.exp(ld); inc = np.deg2rad(row['inc'] + di)
        b2 = vg * abs(vg) + Ud * 10**ldisk * vd * abs(vd) + Ub * 10**lbulge * vb * abs(vb)
        gb = np.maximum(b2 * 1e6 / (rr * S.KPC), 1e-18)
        vp = np.sqrt(gb * S.nu_exp(gb / a0) * rr * dd * S.KPC / 1e6) * np.sin(inc) / np.sin(np.deg2rad(row['inc']))
        return np.r_[(v - vp) / np.sqrt(ev**2 + floor**2), ld / ds, di / si, ldisk / sU, lbulge / sU]
    w = max(0.8, 3 * sU)
    lo = [np.log(.25), max(-25 * inc_mult, 5 - row['inc']), -w, -w]; hi = [np.log(4), min(25 * inc_mult, 89 - row['inc']), w, w]
    f = least_squares(residual, np.zeros(4), bounds=(lo, hi), max_nfev=200, ftol=1e-7, xtol=1e-7, gtol=1e-7)
    r = residual(f.x); n = len(rr)
    return float(r @ r), float(r[:n] @ r[:n]), n, float(10**f.x[2] * Ud)

def total(a0, sample, kw, P):
    out = P.starmap(fit_gal, [(r, a0, kw['floor'], kw['Ud'], kw['sU'], kw['Ub'], kw['inc'], kw['dist']) for r in sample])
    return sum(x[0] for x in out), sum(x[1] for x in out), sum(x[2] for x in out), float(np.median([x[3] for x in out]))

base = dict(floor=0.0, Ud=0.5, sU=0.1, Ub=0.7, inc=1.0, dist=1.0)
abs_dist = [r for r in S.selected if r['Dmethod'] in (2, 3, 5)]     # TRGB, Cepheid, SN distances
VARIANTS = [
    ('baseline (U_disk 0.5, 0.1 dex)', S.selected, {}),
    ('U_disk 0.6', S.selected, dict(Ud=0.6, Ub=0.8)),
    ('U_disk 0.4', S.selected, dict(Ud=0.4, Ub=0.6)),
    ('M/L prior 0.2 dex', S.selected, dict(sU=0.2)),
    ('M/L prior 0.3 dex (near free)', S.selected, dict(sU=0.3)),
    ('inclination prior x2', S.selected, dict(inc=2.0)),
    ('distance prior x2', S.selected, dict(dist=2.0)),
    ('all priors x2', S.selected, dict(sU=0.2, inc=2.0, dist=2.0)),
    ('absolute distances only (TRGB/Cepheid/SN)', abs_dist, {}),
    ('absolute distances, M/L 0.2 dex', abs_dist, dict(sU=0.2)),
]
A0C = S.A0_HEAD
if __name__ == '__main__':
    res = []
    with Pool(2) as P:
        for floor in (0.0, 5.0):
            for name, sample, ov in VARIANTS:
                kw = dict(base, **ov, floor=floor)
                f = lambda la: total(10**la * 1e-10, sample, kw, P)[0]
                m = minimize_scalar(f, bounds=(np.log10(0.5), np.log10(2.5)), method='bounded', options=dict(xatol=1e-3))
                a0b = 10**m.x * 1e-10
                tb, vb, n, mlb = total(a0b, sample, kw, P); tc, vc, _, mlc = total(A0C, sample, kw, P)
                # 1-sigma from the chi2 curvature, formal and scaled by chi2/dof
                h = 0.01; fp, fm = f(m.x + h), f(m.x - h); curv = (fp + fm - 2 * tb) / h**2
                sig_dex = np.sqrt(2 / curv) if curv > 0 else np.nan
                scale = np.sqrt(max(tb / (n - 1), 1.0)); sig_scaled = sig_dex * scale
                nsig = abs(np.log10(A0C / a0b)) / sig_scaled
                row = dict(variant=name, floor=floor, galaxies=len(sample), points=n, a0_best=a0b,
                           a0_sigma_formal_dex=sig_dex, a0_sigma_scaled_dex=sig_scaled, chi2_best=tb, chi2_at_cosmo=tc,
                           delta_chi2=tc - tb, delta_velocity_chi2=vc - vb, median_disk_ML_best=mlb, median_disk_ML_cosmo=mlc,
                           cosmo_a0_offset_scaled_sigma=nsig)
                res.append(row)
                print(f"{name:44s} floor {floor:.0f}  N_gal {len(sample):3d}  a0 {a0b*1e10:.3f} (+-{sig_scaled:.3f} dex scaled)  "
                      f"dchi2 {tc-tb:7.1f} (vel {vc-vb:6.1f})  ML {mlb:.3f}->{mlc:.3f}  cosmo at {nsig:.1f} sig", flush=True)
                json.dump(res, open('sparc_prior_sens.json', 'w'), indent=1)
