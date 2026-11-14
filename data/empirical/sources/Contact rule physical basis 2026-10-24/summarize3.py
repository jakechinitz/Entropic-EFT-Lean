import json,glob,numpy as np,sys
pat = sys.argv[1] if len(sys.argv)>1 else 'd3_*.json'
for f in sorted(glob.glob(pat)):
    d=json.load(open(f)); H=d['history']
    hi=200 if d['case'] in ('MW','massive_spiral','massive_spiral_heavy','group_small') else (100 if 'dwarf' in d['case'] else 1000)
    lo=5 if hi<1000 else 20
    def rms(h): v=[val for k,val in h['offsets'].items() if lo<=float(k)<=hi]; return float(np.sqrt(np.mean(np.square(v))))
    late=[h for h in H if h['t_Gyr']>=7.99]; r=[rms(h) for h in late]
    md=max(abs(v) for h in late for k,v in h['offsets'].items() if lo<=float(k)<=hi)
    E=[h['Emis'] for h in H]; rises=sum(1 for a,b in zip(E,E[1:]) if b>a)
    sm=np.convolve(E,np.ones(3)/3,mode='valid'); srises=sum(1 for a,b in zip(sm,sm[1:]) if b>a)
    eo=[h['Emis_over_floor'] for h in late if h['Emis_over_floor']]
    print(f"{f[3:-5]:42s} t0 {rms(H[0]):.3f} | 8-12 rms {min(r):.3f}-{max(r):.3f} (mean {np.mean(r):.3f}) maxdev {md:.3f} | Emis end/start {E[-1]/E[0]:.3f} rises {rises}/{len(E)-1} (1.5Gyr-smoothed {srises}/{len(sm)-1})"
          + (f" | Emis/floor late {min(eo):.1f}-{max(eo):.1f}" if eo else "")
          + f" | dE {H[-1]['dE_stock_Vf2']:+.3f} W {H[-1]['work_Vf2']:+.3f} | dP {d['contact_dP_max']/d['momentum_scale']:.1e} dL {d['contact_dL_max']/d['angmom_scale']:.1e} | sig {H[0]['sigma_carrier']:.0f}->{H[-1]['sigma_carrier']:.0f}")
