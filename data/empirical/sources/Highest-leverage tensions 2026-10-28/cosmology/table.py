import json, glob, os
R = {}
for f in glob.glob('/home/claude/cos/run/*.json'):
    d = json.load(open(f)); o = d['opts']
    key = (o['sn'], o['off'], o['mnu'], o['tau'], o['cal'], o['acc'], o.get('nl', '1'))
    R.setdefault(key, {})[(d['model'], o['AL'] if d['model'] == 'REL' else '-')] = d
rows = []
print(f"{'SN':8s} {'lowz off':8s} {'mnu':5s} {'tau prior':9s} {'cal':6s} {'acc':3s} {'NL lens':7s} | {'LCDM':>9s} | REL A_L=0.979, calc, 1  -> Delta chi2")
for k in sorted(R):
    g = R[k]; L = g.get(('LCDM', '-'))
    if not L: continue
    cells = []
    for al in ('0.979', 'calc', '1'):
        r = g.get(('REL', al))
        cells.append(f"{r['chi2']['total'] - L['chi2']['total']:+6.2f}" if r else '   -  ')
    print(f"{k[0]:8s} {k[1]:8s} {k[2]:5s} {k[3]:9s} {k[4]:6s} {k[5]:3s} {k[6]:7s} | {L['chi2']['total']:9.3f} | " + '  '.join(cells))
