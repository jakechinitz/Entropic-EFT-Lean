import json,glob,os,numpy as np
R='/tmp/claude-0/c28/sim/runs'; sr=json.load(open('/tmp/claude-0/c28/support_radii.json')); inp=json.load(open('/tmp/claude-0/c28/sim/inputs/summary.json'))
car=json.load(open('/tmp/claude-0/c28/sim/carriers.json'))
runs={}
for d in sorted(glob.glob(R+'/*10k')):
    if not os.path.exists(d+'/summary.json'): continue
    s=json.load(open(d+'/summary.json')); runs[(s['cluster'],s['label'])]=(s,np.load(d+'/profiles_and_state.npz'))
rows=[]
for c in sr:
    if (c,'control10k') not in runs: continue
    cs,cp=runs[(c,'control10k')]; r5=inp[c]['R500_kpc']; rd=sr[c]['rd_proj']
    for lab in ['labeled10k','support10k']:
        if (c,lab) not in runs: continue
        s,p=runs[(c,lab)]; r=p['r_kpc']
        at=lambda f:float(p['late_mean_total_mass'][np.argmin(abs(r-f*r5))]/cp['late_mean_total_mass'][np.argmin(abs(r-f*r5))])
        xf=np.linalg.norm(p['x_final'],axis=1); xc=np.linalg.norm(cp['x_final'],axis=1)
        core=lambda R_:float(np.sum(xf<R_)/max(np.sum(xc<R_),1))
        row=dict(cluster=c,rule=lab,acc=s['accepted_contacts'],spent=s['initial_register_specific_km2_s2']-s['final_register_specific'],
                 reg=s['initial_register_specific_km2_s2'],R500=at(1),r03=at(.3),r01=at(.1),core_rd=core(rd),core_2rd=core(2*rd),n_core_ctrl=int(np.sum(xc<rd)),
                 dE=s['max_abs_mechanical_ledger_residual_over_MV2'],dP=s['contact_delta_P_max_over_MV'],dL=s['contact_delta_L_max_over_MVR'])
        rows.append(row)
        print(f"{c:7s} {lab:11s} acc {row['acc']:6d} spent {row['spent']:8.1f}/{row['reg']:6.1f} | R500 {row['R500']:.4f} 0.3 {row['r03']:.4f} 0.1 {row['r01']:.4f} | core<r_d {row['core_rd']:.3f} <2r_d {row['core_2rd']:.3f} (n={row['n_core_ctrl']}) dP {row['dP']:.1e}")
json.dump(rows,open('/tmp/claude-0/c28/results10k.json','w'),indent=1)
