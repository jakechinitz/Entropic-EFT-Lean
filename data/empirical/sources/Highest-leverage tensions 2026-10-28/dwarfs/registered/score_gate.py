"""22-dwarf test with the combined rule: a dwarf's stock relaxes only if its own field dominates (support) AND its
main progenitor crossed the release gate (Section 20: 17 km/s before z_re, 30 km/s after); otherwise it keeps its
committed, CDM-like allocation. Relaxed values from the contact-dynamics runs. Gate sensitivity: 14 km/s (the gate
at which the measured mixing kernel reaches the fitted release integral)."""
import json, numpy as np, pandas as pd
from gate import crossed, history, Vvir
G = 4.30091e-6; A0 = 1.2307e-10 / 3.2408e-14; nu = lambda y: 1 / (1 - np.exp(-np.sqrt(y)))
reg = json.load(open('registered_predictions.json')); d = pd.read_csv('ext/lvdb/data/dwarf_all.csv').set_index('key')
def run_mass(p):
    h = json.load(open(f"/home/claude/dsph/out/gravsphere/runs/{p['key']}_reg.json"))['hist']
    off = np.mean([x['off_today'][3] for x in h[-3:]]); ms = 10**p['logMs']; a = p['Re_pc'] / 1e3; r12 = 1.305 * a
    mb = ms * r12**3 / (r12**2 + a**2)**1.5; return np.log10(mb * nu(G * mb / r12**2 / A0)) + off
for gpre in (17.0, 14.0):
    tot = {'NFW': 0, 'HEAT': 0, 'RULE': 0}; lines = []
    for p in reg['predictions']:
        _, pre, post = crossed(p['M200']); gate = pre >= gpre or post >= 30
        relax = p['cls'] == 'relaxed' and gate
        rule = run_mass(p) if relax else p['logM_NFW']
        r = d.loc[p['key']]; o = r.mass_dynamical_wolf; s = np.hypot(0.5 * (r.mass_dynamical_wolf_em + r.mass_dynamical_wolf_ep), reg['sig_model'])
        z = {'NFW': (o - p['logM_NFW']) / s, 'HEAT': (o - p['logM_HEAT']) / s, 'RULE': (o - rule) / s}
        for m in tot: tot[m] += z[m]**2
        lines.append(f"  {p['key']:18s} support {'self' if p['cls']=='relaxed' else 'host'}  gate {'yes' if gate else 'no '} -> {'relaxed ' if relax else 'retained'}  obs {o:5.2f} rule {rule:5.2f} heat {p['logM_HEAT']:5.2f}  pulls rule {z['RULE']:+4.1f} heat {z['HEAT']:+4.1f}")
    print(f'gate {gpre} km/s before z_re:'); print('\n'.join(lines)); print('  chi2 (22):', {m: round(v, 1) for m, v in tot.items()})
