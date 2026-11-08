"""Assess saved encounters, preserving original records and every attempted run."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from analyze import evaluate,mapping,peak,CENTRE
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,data):
    with p.open('x',encoding='utf-8') as f:f.write(data)
inputs=[]
prior=ROOT/'02 Research/Effective dynamics and coupling 2026-10-23'
old=json.loads((prior/'source_records/input_manifest.json').read_text(encoding='utf-8'))
assert all(sha(ROOT/r['path'])==r['sha256'] for r in old['inputs'])
for rel in ['Research note/main.tex','Research note/warm_extension.tex','hermitian_contact.py','formalization/EffectiveContact.lean','VALIDATION.json']:
    p=prior/rel;inputs.append({'path':str(p.relative_to(ROOT)),'sha256':sha(p)})
for rel in ['01 Current Papers/Astra Full/Entropic Scalar EFT.tex','01 Current Papers/Empirical Results/Empirical_Results.tex',
            '02 Research/Unified closure 2026-10-21/formalization/Entropic/Reciprocity.lean',
            '02 Research/Cluster reciprocity audit 2026-10-22/CLUSTER_RECIPROCITY_AUDIT.txt',
            '02 Research/Unified empirical program 2026-10-23/results/cluster_cohort_audit.json']:
    p=ROOT/rel;inputs.append({'path':rel,'sha256':sha(p)})
write(HERE/'source_records/input_manifest.json',json.dumps({'prior_verified_unchanged':len(old['inputs']),'inputs':inputs},indent=2))

allrows={};repairs=[];summaries=[];isolated=[];apertures=[]
for path in sorted((HERE/'results').glob('*/result.json')):
    r=json.loads(path.read_text());tag=path.parent.name;snapshot=sha(path.parent/'executed_source.py')
    if r['source_sha256']!=snapshot:
        backup=HERE/'source_records'/(tag+'_result_before_source_hash_repair.json')
        with backup.open('xb') as f:f.write(path.read_bytes())
        repairs.append({'tag':tag,'old':r['source_sha256'],'correct':snapshot,'backup':str(backup.relative_to(HERE)),
                        'reason':'An initial run hashed the live script at completion after a performance edit; its start-of-run source snapshot is the executed source.'})
        r['source_sha256']=snapshot;r['source_hash_metadata_repaired']=True
        path.write_text(json.dumps(r,indent=2),encoding='utf-8')
    assert not r['clips'] and r['minimum_clock_surplus']>=0 and r['minimum_bath']>=0
    assert r['max_momentum_error']<1e-12 and r['max_angular_error']<1e-12
    assert r['max_energy_error_over_initial_binding']<1e-4
    a=np.load(path.parent/'history.npz');gas=a['kind']==2
    entropy={}
    if a['rho_gas'].shape[1]:
        assert a['u'][:,gas].min()>0
        s=np.sum(a['m'][gas][None,:]*np.log(a['u'][:,gas]/a['rho_gas']**(2/3)),axis=1)
        entropy={'minimum_sampled_entropy_increment':float(np.diff(s).min()),'entropy_increase':float(s[-1]-s[0])}
        assert np.diff(s).min()>-1e-7
    allrows[tag]={**{k:r[k] for k in ['particles','settings','contact','max_energy_error_over_initial_binding','max_momentum_error','max_angular_error','minimum_clock_surplus','minimum_bath','source_sha256']},**entropy}
    if r['settings']['isolated']:
        radius=np.array([z['median_radii_about_core'][0] for z in r['history']])
        isolated.append({'tag':tag,'final_radius_ratio_stock_stars_gas':(radius[-1]/radius[0]).tolist()})
        continue
    summary,data=evaluate(tag);summaries.append(summary);_,_,idx,_,_=data
    x=a['x'][idx];mass=a['m'];kind=a['kind'];cohort=a['cohort']
    # Exploratory cohort-resolved 3D aperture diagnostic; not a survey aperture.
    for c in [0,1]:
        centre=np.array(r['history'][idx]['core_centres'][c])
        for rad in [1.,2.,3.]:
            inside=np.linalg.norm(x-centre,axis=1)<rad
            bmass=float(sum(mass[inside&(kind!=0)]));smass=float(sum(mass[inside&(kind==0)]))
            own=cohort==c;b0=sum(mass[own&(kind!=0)]);s0=sum(mass[own&(kind==0)])
            b=float(sum(mass[inside&own&(kind!=0)])/b0);s=float(sum(mass[inside&own&(kind==0)])/s0)
            apertures.append({'tag':tag,'cohort':c,'radius':rad,'total_aperture_baryon_fraction':bmass/(bmass+smass),
                              'own_baryon_retention':b,'own_stock_retention':s,'own_b_over_s':b/s,
                              'imported_stock_mass':float(sum(mass[inside&~own&(kind==0)])),
                              'imported_baryon_mass':float(sum(mass[inside&~own&(kind!=0)]))})

base=np.load(HERE/'results/baseline_optimized/history.npz');floor=np.load(HERE/'results/exact_floor/history.npz')
floor_difference=float(np.max(abs(base['x']-floor['x'])))
assert floor_difference==0 and allrows['exact_floor']['contact']['accepted']==0
order=np.log2(allrows['baseline_optimized']['max_energy_error_over_initial_binding']/allrows['baseline_fine']['max_energy_error_over_initial_binding'])
assert 1.8<order<2.2
leanpath=sorted((HERE/'results').glob('lean_*.json'))[-1];lean=json.loads(leanpath.read_text())
assert lean['success'] and lean['theorems']==8
assert sha(HERE/'formalization/MergerContact.lean')==lean['source_sha256']
log=Path(lean['log']).read_text();assert 'sorryAx' not in log and log.count('depends on axioms:')==8

report={'completed_runs':len(allrows),'prior_inputs_unchanged':len(old['inputs']),'checks_passed':True,
        'runs':allrows,'isolated_controls':isolated,'merger_diagnostics':summaries,'exploratory_apertures':apertures,
        'baseline_energy_convergence_order':float(order),'exact_floor_position_difference_from_zero_contact':floor_difference,
        'source_metadata_repairs':repairs,'Lean':lean,
        'limits':['Selected pair-relative target, rate, range, initial work allocation and bath identification remain inputs.',
                  'Single-carrier orbital target theorem does not establish equilibrium of this multicarrier interaction.',
                  'The nonzero-contact stock is a kinetic medium with internal energy registers; the full spatial clock/floor-fluid stress has not been evolved.',
                  'Gravitational mass of internal energies is neglected at Newtonian order.',
                  'Two particle resolutions and two seeds establish a qualitative control, not a converged observed mass map.',
                  'Gas-free control changes initial baryonic pressure support to an isotropic velocity distribution; it isolates effective component physics, not an otherwise identical pressure switch.',
                  'No observed lensing, X-ray or galaxy likelihood has been fitted; no cross-sector physical rate has been selected.']}
write(HERE/'ASSESSMENT.json',json.dumps(report,indent=2))
write(HERE/'results/baseline/STOPPED.txt','Stopped the first slow baseline after confirming that allocation-free scalar kernels reproduce its forces. Its initial state, settings and source are preserved. The full replacement is baseline_optimized. No final result is claimed for this interrupted run.\n')

# Final figures use clear physical labels and identical map normalization rules.
names=['baseline_res2','weak_res2','active_res2','depleted_nu1']
labels=['No contact','Weak contact','Strong contact','Nearly depleted']
fig,axs=plt.subplots(2,2,figsize=(10,7.8),layout='constrained')
for ax,tag,label in zip(axs.flat,names,labels):
    row,(a,r,idx,total,gm)=evaluate(tag);x=a['x'][idx];stars=a['kind']==1
    im=ax.imshow(np.log10(gm.T/gm.max()+1e-4),origin='lower',extent=[-8,8,-8,8],vmin=-3,vmax=0,cmap='magma')
    ax.contour(CENTRE,CENTRE,total.T,levels=total.max()*np.array([.15,.3,.5,.75]),colors='cyan',linewidths=.8)
    ax.scatter(x[stars,0],x[stars,1],s=2,c='white',alpha=.5)
    ax.set(xlim=(-4,5),ylim=(-3,3),xlabel='x / a',ylabel='y / a',aspect='equal',title=f"{label}: t = {row['evaluation_time']:.1f}")
fig.colorbar(im,ax=axs.ravel().tolist(),shrink=.7,label='log10(emission proxy / panel maximum)')
fig.suptitle('Common gravity: gas emission proxy, total-mass contours and stellar tracers')
fig.savefig(HERE/'figures/merger_maps.png',dpi=180);plt.close(fig)

fig,axs=plt.subplots(1,3,figsize=(12,3.6),layout='constrained')
for tag,label in zip(['initial_isolated','weak_isolated','active_isolated'],['No contact','Weak contact','Strong contact']):
    r=json.loads((HERE/'results'/tag/'result.json').read_text());t=[z['time'] for z in r['history']]
    rad=np.array([z['median_radii_about_core'][0] for z in r['history']]);rad/=rad[0]
    for j,ax in enumerate(axs):ax.plot(t,rad[:,j],label=label)
for ax,title in zip(axs,['Stock','Stellar tracers','Gas']):
    ax.set(title=title,xlabel='Time / dynamical unit',ylabel='Median radius / initial radius');ax.grid(alpha=.2)
axs[0].legend(fontsize=8);fig.suptitle('Isolated controls reveal whether the chosen contact preserves the starting halo')
fig.savefig(HERE/'figures/isolated_controls.png',dpi=180);plt.close(fig)

selected=[next(z for z in summaries if z['tag']==t) for t in ['baseline_optimized','baseline_fine','baseline_res2','baseline_seed2','weak_nu01','weak_res2','weak_seed2','active_nu1','active_fine','active_res2','active_short_range','depleted_nu1','collisionless_baryons']]
table=[]
for r in selected:
    c=r['cohorts'][1]
    table.append({'tag':r['tag'],'t':r['evaluation_time'],'secondary_stock_gas_offset':c['stock_gas_peak_distance'],
                  'secondary_stock_stars_offset':c['stock_stars_peak_distance'],'core_separation':r['core_separation_at_evaluation']})
write(HERE/'comparison_table.json',json.dumps(table,indent=2))
print(json.dumps({'completed_runs':len(allrows),'energy_order':order,'isolated':isolated,'table':table,'repairs':repairs}))
