import json,glob,os,numpy as np
R='/tmp/claude-0/c28/sim/runs'; sr=json.load(open('/tmp/claude-0/c28/support_radii.json')); inp=json.load(open('/tmp/claude-0/c28/sim/inputs/summary.json'))
runs={}
for d in sorted(glob.glob(R+'/*')):
    if not os.path.exists(d+'/summary.json'): continue
    s=json.load(open(d+'/summary.json')); p=np.load(d+'/profiles_and_state.npz')
    runs[(s['cluster'],s['label'],s['k'])]=(s,p)
rows=[]
for (c,l,k),(s,p) in sorted(runs.items()):
    if l in('control','timing'):continue
    cs,cp=runs[(c,'control',0.0)] if (c,'control',0.0) in runs else runs[(c,'control',0)]
    r5=inp[c]['R500_kpc']; r=p['r_kpc']
    def at(f): i=np.argmin(abs(r-f*r5)); return p['late_mean_total_mass'][i]/cp['late_mean_total_mass'][i]
    xf=np.linalg.norm(p['x_final'],axis=1); xc=np.linalg.norm(cp['x_final'],axis=1); rd=sr[c]['rd_proj']
    core=lambda xx,R:np.sum(xx<R)
    row=dict(cluster=c,label=l,k=k,register=s['initial_register_specific_km2_s2'],acc=s['accepted_contacts'],
             work_spent=s['initial_register_specific_km2_s2']-s['final_register_specific'],
             R500=at(1.0),r03=at(0.3),r01=at(0.1),
             core_rd=(core(xf,rd)/max(core(xc,rd),1)),core_n_ctrl=int(core(xc,rd)),
             dE=s['max_abs_mechanical_ledger_residual_over_MV2'],dP=s['contact_delta_P_max_over_MV'])
    rows.append(row)
    print(f"{c:7s} {l:15s} k{k:.0f} reg {row['register']:9.1f} acc {row['acc']:5d} spent {row['work_spent']:9.1f} | R500 {row['R500']:.4f} 0.3R500 {row['r03']:.4f} 0.1R500 {row['r01']:.4f} | core(<r_d) {row['core_rd']:.3f} (n={row['core_n_ctrl']})")
json.dump(rows,open('/tmp/claude-0/c28/results_rows.json','w'),indent=1)
