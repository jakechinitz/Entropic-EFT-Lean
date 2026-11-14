"""MOND on the X-COP hydrostatic profiles, same inputs as Observed cluster tests 2026-10-23.
Spherical algebraic MOND (exact for QUMOND in spherical symmetry): M_dyn(<r) = M_bar(<r) nu(g_bar/a0)."""
import json, csv, numpy as np
from pathlib import Path
U = Path('/mnt/user-data/uploads/Sol and Fable/02 Research/Observed cluster tests 2026-10-23/results')
G = 4.30091727003628e-6; KPC = 3.0856775814913673e19
summ = json.loads((U / 'radial_summary.json').read_text())['clusters']
nu = {'simple': lambda y: 0.5 + np.sqrt(0.25 + 1 / y),
      'standard': lambda y: np.sqrt(0.5 + np.sqrt(0.25 + 1 / y**2)),
      'exp_RAR': lambda y: 1 / (-np.expm1(-np.sqrt(y)))}
K = 5.1760752079627395; FB = 0.157
out = {}
for c, info in summ.items():
    rows = list(csv.DictReader(open(U / f'{c}_radial.csv')))
    r = np.array([float(x['r_kpc']) for x in rows]); mg = np.array([float(x['Mgas_Msun']) for x in rows])
    ms = np.array([float(x['Mstar_3D_approx_Msun']) for x in rows]); mh = np.array([float(x['M_NFW_Msun']) for x in rows])
    r5 = info['R500_kpc']
    rec = {'stars': bool(info['has_stellar_profile']), 'R500_kpc': r5, 'rmax_over_R500': float(r.max() / r5)}
    for label, rad in [('R500', r5), ('0.5R500', 0.5 * r5), ('rmax', r.max())]:
        if rad > r.max() * 1.0001 or rad < r.min(): continue
        Mb = np.exp(np.interp(np.log(rad), np.log(r), np.log(mg + ms))); Mh = np.exp(np.interp(np.log(rad), np.log(r), np.log(mh)))
        gb = G * Mb / rad**2 * 1e6 / KPC
        d = {'r_kpc': float(rad), 'Mbar': Mb, 'M_hydro_NFW': Mh, 'gbar_over_1.2e-10': gb / 1.2e-10,
             'hydro_total_over_baryon': Mh / Mb, 'stock_cohort_over_hydro': (1 + K) * Mb / Mh, 'LCDM_fb_over_hydro': Mb / FB / Mh}
        for n, f in nu.items(): d[f'MOND_{n}_over_hydro'] = Mb * f(gb / 1.2e-10) / Mh
        rec[label] = d
    out[c] = rec
json.dump(out, open('cluster_mond.json', 'w'), indent=1)
def med(key, lab='R500', stars_only=True):
    v = [o[lab][key] for o in out.values() if lab in o and (o['stars'] or not stars_only)]
    return np.median(v), np.min(v), np.max(v), len(v)
for so in (True, False):
    print('stars only' if so else 'all 12')
    for k in ['hydro_total_over_baryon', 'stock_cohort_over_hydro', 'LCDM_fb_over_hydro', 'MOND_simple_over_hydro', 'MOND_standard_over_hydro', 'MOND_exp_RAR_over_hydro', 'gbar_over_1.2e-10']:
        print(f'  {k:28s} median %.3f  range %.3f-%.3f  n=%d' % med(k, 'R500', so))
for c, o in out.items(): print(c, o['stars'], round(o['rmax_over_R500'], 2), {k: round(v, 3) for k, v in o['R500'].items() if 'over' in k})
