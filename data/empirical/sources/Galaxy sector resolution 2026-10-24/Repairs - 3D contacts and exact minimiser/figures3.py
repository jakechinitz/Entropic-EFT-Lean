"""Figures for the repair note (descent3.py, 3-D central-impulse contacts)."""
import json, numpy as np, matplotlib
matplotlib.use('Agg'); import matplotlib.pyplot as plt
plt.rcParams.update({'font.size': 9, 'axes.edgecolor': '#52514e', 'xtick.color': '#52514e',
                     'ytick.color': '#52514e', 'axes.spines.top': False, 'axes.spines.right': False})
B1, B2, B3 = '#2a78d6', '#eb6834', '#1baf7a'
def off(f): d = json.load(open(f)); o = d['offsets_final']; return np.array([float(k) for k in o]), np.array(list(o.values()))
fig, ax = plt.subplots(1, 3, figsize=(7.2, 2.6))
for a, title, f0, fs, rcap in [
    (ax[0], 'Milky Way, 12 Gyr', 'd3_MW_k0_reg0_N4000_sig0_s1.json',
     ['d3_MW_k1_reg15000_N8000_sig175_s1.json', 'd3_MW_k1_reg15000_N4000_sig175_s2.json', 'd3_MW_k1_reg15000_N4000_sig175_s3.json'], None),
    (ax[1], 'Dwarf, 12 Gyr', 'd3_dwarf_k0_reg0_N4000_sig0_s1.json',
     ['d3_dwarf_k3_reg1000_N4000_sig0_s1.json', 'd3_dwarf_k3_reg1000_N4000_sig175_s2.json', 'd3_dwarf_k3_reg1000_N4000_sig175_s3.json'], 96)]:
    a.axhline(0, color='#b5b4ae', lw=1)
    r0, o0 = off(f0); a.plot(r0, o0, color=B2, lw=2, label='no contacts')
    for k, f in enumerate(fs):
        r1, o1 = off(f); a.plot(r1, o1, color=B1, lw=1.6 if k == 0 else 1.0, alpha=1 if k == 0 else 0.6,
                                label='3-D contact descent' if k == 0 else None)
    if rcap: a.axvline(rcap, color='#b5b4ae', lw=1, ls=':'); a.text(rcap*0.92, -0.3, 'budget edge', ha='right', fontsize=7, color='#52514e')
    a.set_xscale('log'); a.set_title(title, fontsize=9); a.set_xlabel('r (kpc)'); a.set_ylim(-0.42, 0.4)
    a.grid(axis='y', color='#ececea', lw=0.8)
ax[0].set_ylabel('log g_obs / g_RAR (dex)'); ax[0].legend(frameon=False, fontsize=7, loc='lower left')
a = ax[2]
for f, col, lab, dy in [('d3_MW_k0_reg0_N4000_sig0_s1.json', B2, 'MW, no contacts', 0),
                        ('d3_MW_k1_reg15000_N4000_sig175_s2.json', B1, 'MW, descent', 0),
                        ('d3_dwarf_k3_reg1000_N4000_sig175_s2.json', B3, 'dwarf', 0)]:
    d = json.load(open(f)); H = d['history']; t = [h['t_Gyr'] for h in H]; E = np.array([h['Emis'] for h in H])
    a.plot(t, E/E[0], color=col, lw=2); a.text(t[-1]+0.3, E[-1]/E[0], lab, fontsize=7, color='#52514e', va='center')
fl = json.load(open('d3_dwarf_k3_reg1000_N4000_sig175_s2.json'))
a.axhline(fl['Emis_floor']/fl['history'][0]['Emis'], color=B3, lw=1, ls=':')
a.text(4.0, fl['Emis_floor']/fl['history'][0]['Emis']*0.42, 'dwarf exact floor (dotted)', fontsize=7, color='#52514e')
a.set_yscale('log'); a.set_xlim(0, 18); a.set_title('Mismatch E_mis / initial', fontsize=9); a.set_xlabel('t (Gyr)')
a.grid(axis='y', color='#ececea', lw=0.8)
plt.tight_layout(); plt.savefig('note3/images/descent3.png', dpi=220); print('ok')
