"""Figures for the galaxy-sector note (second-version runs, descent2.py)."""
import json, numpy as np, matplotlib
matplotlib.use('Agg'); import matplotlib.pyplot as plt
plt.rcParams.update({'font.size': 9, 'axes.edgecolor': '#52514e', 'xtick.color': '#52514e',
                     'ytick.color': '#52514e', 'axes.spines.top': False, 'axes.spines.right': False})
B1, B2, B3 = '#2a78d6', '#eb6834', '#1baf7a'
def load(f): d = json.load(open(f)); o = d['offsets_final']; return np.array([float(k) for k in o]), np.array(list(o.values())), d
fig, ax = plt.subplots(1, 3, figsize=(7.2, 2.6))
for a, title, f0, fs, rcap in [
    (ax[0], 'Milky Way model, 12 Gyr', 'd2_MW_k0_reg0_N4000_sig0_s1.json',
     ['d2_MW_k10_reg15000_N8000_sig175_s1.json', 'd2_MW_k10_reg15000_N4000_sig175_s2.json', 'd2_MW_k10_reg15000_N4000_sig175_s3.json'], None),
    (ax[1], 'Dwarf model, 12 Gyr', 'd2_dwarf_k0_reg0_N4000_sig0_s1.json',
     ['d2_dwarf_k10_reg1000_N4000_sig175_s1.json', 'd2_dwarf_k10_reg1000_N4000_sig175_s2.json', 'd2_dwarf_k10_reg1000_N4000_sig175_s3.json'], 96)]:
    a.axhline(0, color='#b5b4ae', lw=1)
    r0, o0, _ = load(f0); a.plot(r0, o0, color=B2, lw=2, label='no contacts')
    for k, f in enumerate(fs):
        r1, o1, _ = load(f); a.plot(r1, o1, color=B1, lw=1.6 if k == 0 else 1.0, alpha=1 if k == 0 else 0.6,
                                    label='contact descent (3 seeds)' if k == 0 else None)
    if rcap: a.axvline(rcap, color='#b5b4ae', lw=1, ls=':'); a.text(rcap*0.92, -0.3, 'budget edge', ha='right', fontsize=7, color='#52514e')
    a.set_xscale('log'); a.set_title(title, fontsize=9); a.set_xlabel('r (kpc)'); a.set_ylim(-0.42, 0.4)
    a.grid(axis='y', color='#ececea', lw=0.8)
ax[0].set_ylabel('log g_obs / g_RAR (dex)'); ax[0].legend(frameon=False, fontsize=7, loc='lower left')
a = ax[2]
for (f, col, lab), dy in zip([('d2_MW_k1_reg15000_N4000_sig175_s1.json', B2, '1 proposal / orbit'),
                    ('d2_MW_k3_reg15000_N4000_sig175_s1.json', B3, '3 / orbit'),
                    ('d2_MW_k10_reg15000_N4000_sig175_s1.json', B1, '10 / orbit')], (0, 0.007, -0.007)):
    H = json.load(open(f))['history']
    t = [h['t_Gyr'] for h in H]
    rms = [np.sqrt(np.mean(np.square([v for k, v in h['offsets'].items() if 5 <= float(k) <= 200]))) for h in H]
    a.plot(t, rms, color=col, lw=2, label=lab)
    a.text(t[-1]+0.3, rms[-1]+dy, lab.replace(' proposal',''), fontsize=7, color='#52514e', va='center')
a.set_title('MW rms offset vs time', fontsize=9); a.set_xlim(0, 16.5); a.set_ylabel('rms, 5-200 kpc (dex)'); a.set_xlabel('t (Gyr)'); a.set_ylim(0, 0.14)
a.grid(axis='y', color='#ececea', lw=0.8)
plt.tight_layout(); plt.savefig('note/images/offsets.png', dpi=220); print('ok')
