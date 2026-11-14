import json,glob,numpy as np
rows=[]
for f in sorted(glob.glob('d2_*.json')):
    d=json.load(open(f)); H=d['history']
    hi=200 if d['case'] in ('MW','massive_spiral','massive_spiral_heavy','group_small') else (100 if 'dwarf' in d['case'] else 1000)
    lo=5 if hi<1000 else 20
    def rms(h): v=[val for k,val in h['offsets'].items() if lo<=float(k)<=hi]; return float(np.sqrt(np.mean(np.square(v))))
    late=[h for h in H if h['t_Gyr']>=7.99]
    r=[rms(h) for h in late]
    maxdev=max(abs(v) for h in late for k,v in h['offsets'].items() if lo<=float(k)<=hi)
    print(f"{f[3:]:50s} t0 {rms(H[0]):.3f} | 8-12 Gyr rms {min(r):.3f}-{max(r):.3f} mean {np.mean(r):.3f} maxdev {maxdev:.3f} | dE {H[-1]['dE_stock_Vf2']:+.3f} W {H[-1]['work_Vf2']:+.3f} | out {H[-1]['frac_beyond_r200']:.2f} | tob1000 {d['total_over_baryon']['1000.0']:.2f} tob1500 {d['total_over_baryon']['1500.0']:.2f}")
