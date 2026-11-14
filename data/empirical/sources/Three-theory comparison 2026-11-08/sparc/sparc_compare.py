"""SPARC: stock-model law, MOND (three interpolation functions, free global a0) and NFW halos
on the identical pipeline of Unified empirical program 2026-10-23/galaxy_tests.py.

Same 130 galaxies (quality <= 2, 30 <= i <= 80), same points, same nuisance priors
(distance, inclination, disk and bulge M/L), same optional 5 km/s velocity floor.
Only the gravity model changes.

Models
  stock      g = g_b / (1 - exp(-sqrt(g_b/a0))), a0 fixed by cosmology (no galaxy fit)
  mond_exp   same function, global a0 fitted (McGaugh-Lelli RAR form)
  mond_simple  nu(y) = 1/2 + sqrt(1/4 + 1/y), global a0 fitted
  mond_std   nu(y) = sqrt(1/2 + sqrt(1/4 + 1/y^2)), global a0 fitted
  nfw_free   baryons + NFW halo, per-galaxy log M200 and log c, wide bounds
  nfw_lcdm   same, with LCDM priors: Dutton-Maccio 2014 c(M200) (0.11 dex) and the
             Moster+13 stellar-to-halo relation (halo mass at fixed M*, 0.3 dex)
"""
import io, zipfile, json, sys, time
from pathlib import Path
import numpy as np
from scipy.optimize import least_squares, minimize_scalar
from multiprocessing import Pool

H = Path(__file__).resolve().parent
KPC = 3.0856775814913673e19
G = 4.300917270e-6                      # kpc (km/s)^2 / Msun
g_share = 7.419800023570902; eps = g_share / (4 * np.pi**2)
A0_REF = eps * 299792458 * 67400 / (KPC * 1000)        # 1.2307e-10 at H0 = 67.4
A0_HEAD = eps * 299792458 * 68.42235620670189e3 / (KPC * 1000)   # frozen 4-parameter fit
A0_EXPFIT = A0_REF * 68.93885586416 / 67.4                       # paper's current S03 value

archive = zipfile.ZipFile(H / 'mass_models.zip')
names = {Path(n).name.replace('_rotmod.dat', ''): n for n in archive.namelist() if n.endswith('_rotmod.dat')}
cat = []
for line in (H / 'catalog.mrt').read_text().splitlines():
    v = line.split()
    if len(v) != 19: continue
    try:
        row = dict(name=v[0], D=float(v[2]), Derr=float(v[3]), Dmethod=int(v[4]), inc=float(v[5]), incerr=float(v[6]),
                   L=float(v[7]), MHI=float(v[13]), Vflat=float(v[15]), eVflat=float(v[16]), quality=int(v[17]))
    except ValueError: continue
    row['array'] = np.atleast_2d(np.loadtxt(io.BytesIO(archive.read(names[row['name']]))))
    cat.append(row)
assert len(cat) == 175
selected = [r for r in cat if r['quality'] <= 2 and 30 <= r['inc'] <= 80]

def nu_exp(y): return 1 / (-np.expm1(-np.sqrt(y)))
def nu_simple(y): return 0.5 + np.sqrt(0.25 + 1 / y)
def nu_std(y): return np.sqrt(0.5 + np.sqrt(0.25 + 1 / y**2))
NU = dict(exp=nu_exp, simple=nu_simple, std=nu_std)

# NFW helpers (H0 = 70 for the overdensity definition; SPARC distances are ~ that scale)
RHO200 = 200 * 3 * (70 / 1000)**2 / (8 * np.pi * G)      # Msun / kpc^3 with H in km/s/kpc
def v2_nfw(r, lM, lc):
    M = 10**lM; c = 10**lc
    r200 = (3 * M / (4 * np.pi * RHO200))**(1 / 3)
    x = c * r / r200; mu = lambda t: np.log1p(t) - t / (1 + t)
    return G * M * mu(x) / (mu(c) * r)

def c_dm14(lM):   # Dutton & Maccio 2014, NFW, M200c, z = 0, h = 0.7
    return 0.905 - 0.101 * (lM - 12 + np.log10(0.7))

def moster_mstar(lM):   # Moster+13 z = 0
    M1, N, b, g = 10**11.590, 0.0351, 1.376, 0.608
    M = 10**lM
    return np.log10(2 * N * M / ((M / M1)**(-b) + (M / M1)**g))
LMGRID = np.linspace(9, 15, 2001); LSGRID = moster_mstar(LMGRID)
def moster_inverse(lms): return np.interp(lms, LSGRID, LMGRID)

def fit_gal(row, model, a0=None, floor=0.0):
    arr = row['array']; rr, v, ev, vg, vd, vb = arr[:, :6].T
    good = (rr > 0) & (v > 0) & (ev > 0)
    rr, v, ev, vg, vd, vb = [x[good] for x in [rr, v, ev, vg, vd, vb]]
    ds = max(row['Derr'] / row['D'], .01); si = max(row['incerr'], .1)
    halo = model.startswith('nfw')
    lms0 = np.log10(max(0.5 * row['L'] * 1e9, 1e6))
    def residual(p):
        ld, di, ldisk, lbulge = p[:4]
        dd = np.exp(ld); inc = np.deg2rad(row['inc'] + di)
        b2 = vg * abs(vg) + .5 * 10**ldisk * vd * abs(vd) + .7 * 10**lbulge * vb * abs(vb)
        if halo:
            lM, lc = p[4:6]
            vp2 = np.maximum(b2 * dd + v2_nfw(rr * dd, lM, lc), 1e-6)
        else:
            gb = np.maximum(b2 * 1e6 / (rr * KPC), 1e-18)
            gp = gb * NU[model](gb / a0)
            vp2 = gp * rr * dd * KPC / 1e6
        vp = np.sqrt(vp2) * np.sin(inc) / np.sin(np.deg2rad(row['inc']))
        out = [(v - vp) / np.sqrt(ev**2 + floor**2), [ld / ds, di / si, ldisk / .1, lbulge / .1]]
        if model == 'nfw_lcdm':
            lms = np.log10(10**lms0 * 10**ldisk * dd**2)
            out.append([(lc - c_dm14(lM)) / 0.11, (lM - moster_inverse(lms)) / 0.3])
        return np.concatenate(out)
    lo = [np.log(.25), max(-25, 5 - row['inc']), -.8, -.8]; hi = [np.log(4), min(25, 89 - row['inc']), .8, .8]
    if halo:
        lo += [8.0, -0.5]; hi += [14.5, 2.0]
        best = None
        for lM0 in (10.5, 11.5, 12.5):
            p0 = np.r_[0, 0, 0, 0, lM0, c_dm14(lM0)]
            f = least_squares(residual, p0, bounds=(lo, hi), max_nfev=400, ftol=1e-8, xtol=1e-8, gtol=1e-8)
            if best is None or f.cost < best.cost: best = f
        fit = best
    else:
        fit = least_squares(residual, np.zeros(4), bounds=(lo, hi), max_nfev=120, ftol=1e-7, xtol=1e-7, gtol=1e-7)
    res = residual(fit.x); n = len(rr)
    d = dict(name=row['name'], points=n, chi2_velocity=float(res[:n] @ res[:n]), prior_penalty=float(res[n:] @ res[n:]),
             total=float(res @ res), success=bool(fit.success))
    if halo: d.update(logM200=float(fit.x[4]), logc=float(fit.x[5]))
    return d

def run(model, a0=None, floor=0.0):
    with Pool(2) as P:
        rows = P.starmap(fit_gal, [(r, model, a0, floor) for r in selected])
    return rows

def summary(rows):
    return dict(total=sum(x['total'] for x in rows), chi2_velocity=sum(x['chi2_velocity'] for x in rows),
                median_chi2_per_point=float(np.median([x['chi2_velocity'] / x['points'] for x in rows])),
                points=sum(x['points'] for x in rows), galaxies=len(rows), failed=sum(not x['success'] for x in rows))

if __name__ == '__main__':
    out = {'a0_reference_H0_67.4': A0_REF, 'a0_headline_frozen_fit': A0_HEAD, 'a0_paper_S03': A0_EXPFIT, 'runs': {}}
    t0 = time.time()
    for floor in (0.0, 5.0):
        tag = f'floor{int(floor)}'
        # reproduction checks and the stock model at the headline normalization
        for name, a0 in [('stock_a0_paper_S03', A0_EXPFIT), ('stock_a0_reference', A0_REF), ('stock_a0_headline', A0_HEAD)]:
            out['runs'][f'{name}_{tag}'] = dict(a0=a0, free_global=0, free_per_galaxy=0, **summary(run('exp', a0, floor)))
            print(name, tag, out['runs'][f'{name}_{tag}']['total'], f'{time.time()-t0:.0f}s', flush=True)
        # MOND, three interpolations, canonical a0 = 1.2e-10 and globally fitted a0
        for nu in ('exp', 'simple', 'std'):
            r = run(nu, 1.2e-10, floor)
            out['runs'][f'mond_{nu}_a0_1.2_{tag}'] = dict(a0=1.2e-10, free_global=0, free_per_galaxy=0, **summary(r))
            f = lambda la: summary(run(nu, 10**la * 1e-10, floor))['total']
            m = minimize_scalar(f, bounds=(np.log10(0.6), np.log10(2.0)), method='bounded', options=dict(xatol=2e-3))
            a0b = 10**m.x * 1e-10
            out['runs'][f'mond_{nu}_a0_free_{tag}'] = dict(a0=a0b, free_global=1, free_per_galaxy=0, **summary(run(nu, a0b, floor)))
            print('mond', nu, tag, out['runs'][f'mond_{nu}_a0_1.2_{tag}']['total'], out['runs'][f'mond_{nu}_a0_free_{tag}']['total'], a0b, f'{time.time()-t0:.0f}s', flush=True)
        for model in ('nfw_free', 'nfw_lcdm'):
            r = run(model, None, floor)
            out['runs'][f'{model}_{tag}'] = dict(free_global=0, free_per_galaxy=2, **summary(r),
                                                 logM200_median=float(np.median([x['logM200'] for x in r])),
                                                 logc_median=float(np.median([x['logc'] for x in r])),
                                                 at_c_bound=int(sum((x['logc'] < -0.49) or (x['logc'] > 1.99) for x in r)),
                                                 at_M_bound=int(sum((x['logM200'] < 8.01) or (x['logM200'] > 14.49) for x in r)),
                                                 rows=r)
            print(model, tag, out['runs'][f'{model}_{tag}']['total'], f'{time.time()-t0:.0f}s', flush=True)
        (H / 'sparc_compare.json').write_text(json.dumps(out, indent=1))
    print('done', flush=True)
