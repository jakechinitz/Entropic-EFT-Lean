"""Rescore the 22-dwarf test with the relaxed class taken from the contact-dynamics harness (dsph_W.py, paper
register 0.9 V_f^2, supernova coupling 0.1, z_start = 6, the classical-rerun settings) in place of law + 0.08 dex."""
import json, numpy as np, pandas as pd, os
G = 4.30091e-6; A0 = 1.2307e-10 / 3.2408e-14
reg = json.load(open('/home/claude/reg/registered_predictions.json'))
d = pd.read_csv('/home/claude/reg/ext/lvdb/data/dwarf_all.csv').set_index('key')
nu = lambda y: 1 / (1 - np.exp(-np.sqrt(y)))
SIG = reg['sig_model']; tot = {'NFW': 0, 'HEAT': 0, 'RULE_law': 0, 'RULE_runs': 0}; rows = []
for p in reg['predictions']:
    k = p['key']; r = d.loc[k]; o = r.mass_dynamical_wolf; eo = 0.5 * (r.mass_dynamical_wolf_em + r.mass_dynamical_wolf_ep)
    s = np.hypot(eo, SIG)
    if p['cls'] == 'relaxed':
        f = f'/home/claude/dsph/out/gravsphere/runs/{k}_reg.json'
        if not os.path.exists(f): continue
        h = json.load(open(f))['hist']; off = np.mean([x['off_today'][3] for x in h[-3:]])
        ms = 10**p['logMs']; a = p['Re_pc'] / 1e3; r12 = 1.305 * a; mb = ms * r12**3 / (r12**2 + a**2)**1.5
        mrun = np.log10(mb * nu(G * mb / r12**2 / A0)) + off
    else:
        mrun = p['logM_NFW']
    pred = {'NFW': p['logM_NFW'], 'HEAT': p['logM_HEAT'], 'RULE_law': p['logM_RULE'], 'RULE_runs': mrun}
    z = {m: (o - v) / s for m, v in pred.items()}
    for m in tot: tot[m] += z[m]**2
    rows.append((k, p['cls'], o, pred['HEAT'], pred['RULE_law'], mrun, z['HEAT'], z['RULE_runs']))
for x in rows: print(f"{x[0]:18s} {x[1]:8s} obs {x[2]:5.2f} HEAT {x[3]:5.2f} RULE(law) {x[4]:5.2f} RULE(runs) {x[5]:5.2f} | pull HEAT {x[6]:+4.1f} RULE {x[7]:+4.1f}")
print(len(rows), 'dwarfs; chi2', {m: round(v, 1) for m, v in tot.items()})
