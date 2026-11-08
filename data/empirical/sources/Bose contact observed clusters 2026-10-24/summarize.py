"""Summarize completed regularized runs without treating fitted starts as predictions."""
from pathlib import Path
import json,csv
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.ticker import NullFormatter
from datetime import datetime
HERE=Path(__file__).resolve().parent
META=json.loads((HERE/'inputs/summary.json').read_text())
NAMES=['A85','A1795','A2029','A2142','A2319','A644','ZW1215']

def collect():
    runs=[]
    for p in sorted((HERE/'runs').glob('*/summary.json')):
        s=json.loads(p.read_text())
        if not (s['label'].startswith('final') or s['label'].startswith('shared_')):continue
        a=np.load(p.parent/'profiles_and_state.npz');meta=META[s['cluster']];r5=meta['R500_kpc']
        r=a['r_kpc'];times=a['t_Gyr'];late=times>=8
        prof=a['total_mass'];mean=prof[late].mean(0)
        hist=[json.loads(t) for t in (p.parent/'history.jsonl').read_text().splitlines()]
        s['first_record_below_1percent_reserve_Gyr']=next((h['t_Gyr'] for h in hist if h['register_specific_km2_s2']<.01*s['initial_register_specific_km2_s2']),None)
        v2=4.30091e-6*meta['observed_total_M500']/r5
        s['energy_residual_fraction_initial_reserve']=s['max_abs_mechanical_ledger_residual_over_MV2']*v2/s['initial_register_specific_km2_s2']
        s['mass_relative_initial_at_radii']={str(q):float(np.interp(q*r5,r,mean/prof[0])) for q in [.1,.2,.3,.5,1]}
        s['final_mass_relative_initial_at_radii']={str(q):float(np.interp(q*r5,r,prof[-1]/prof[0])) for q in [.1,.2,.3,.5,1]}
        s['actual_input_total_mass_at_R500']=float(np.interp(r5,r,prof[0]))
        s['late_profile']=mean.tolist();s['r_over_R500']=(r/r5).tolist()
        s['late_R500_minmax_over_HSE']=[min(h['total_at_R500_over_HSE'] for h in hist if h['t_Gyr']>=8),max(h['total_at_R500_over_HSE'] for h in hist if h['t_Gyr']>=8)]
        runs.append(s)
    return runs

def main():
    runs=collect();out=HERE/('analysis_'+datetime.now().strftime('%Y%m%d_%H%M%S'));out.mkdir()
    rows=[]
    for s in runs:
        control_label='shared_resolution' if s['label']=='shared_resolution' else 'final'
        control=next((z for z in runs if z['cluster']==s['cluster'] and z['k']==0 and z['label']==control_label and z['N']==s['N'] and z['seed']==s['seed']),None)
        if control:
            ratio=np.array(s['late_profile'])/np.array(control['late_profile'])
            s['relative_no_contact_at_radii']={str(q):float(np.interp(q,s['r_over_R500'],ratio)) for q in [.1,.2,.3,.5,1]}
            dom=(np.array(s['r_over_R500'])>=.1)&(np.array(s['r_over_R500'])<=1)
            s['radial_rms_change_from_control_dex']=float(np.sqrt(np.mean(np.log10(ratio[dom])**2)))
        row={k:s[k] for k in ['cluster','k','N','seed','label','softening_kpc','dt_Myr','initial_register_specific_km2_s2','late_mean_total_R500_over_HSE','late_std_total_R500_over_HSE','energy_residual_fraction_initial_reserve','accepted_contacts','final_register_specific']}
        for q in [.1,.2,.3,.5,1]:row[f'ratio_to_control_at_{q}R500']=s.get('relative_no_contact_at_radii',{}).get(str(q))
        rows.append(row)
    with (out/'run_summary.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]) if rows else []);w.writeheader();w.writerows(rows)
    (out/'all_results.json').write_text(json.dumps(runs,indent=2,allow_nan=False))
    static=[]
    for name in NAMES:
        m=META[name]
        static.append(dict(cluster=name,R500_kpc=m['R500_kpc'],RAR_mass_over_XCOP=m['RAR_total_over_observed_at_R500'],RAR_stock_over_XCOP=m['RAR_stock_over_observed_at_R500'],RAR_mass_over_lensing=m.get('independent_lensing',{}).get('RAR_total_over_published_M500')))
    with (out/'static_observed.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(static[0]));w.writeheader();w.writerows(static)
    fig,axs=plt.subplots(2,4,figsize=(13,6.4),sharex=True,sharey=True)
    cols={1:'#236b8e',3:'#ba5734'}
    for ax,name in zip(axs.flat,NAMES):
        m=META[name];a=np.load(HERE/'inputs'/f'{name}.npz')
        baseline=next((t for t in runs if t['cluster']==name and t['label']=='final' and t['k']==0),None)
        denominator=np.interp(a['observed_r']/m['R500_kpc'],baseline['r_over_R500'],baseline['late_profile']) if baseline else a['observed_total']
        ax.plot(a['observed_r']/m['R500_kpc'],(a['observed_b']+a['target_stock'])/denominator,color='#8468a3',ls='--',label='Bose equilibrium / control')
        for s in runs:
            if s['cluster']!=name or s['k']==0:continue
            if not (s['label']=='shared_scaling' or (s['label']=='final' and s['k']==3)):continue
            control=next((t for t in runs if t['cluster']==name and t['label']=='final' and t['k']==0),None)
            if control:
                shared=s['label']=='shared_scaling'
                ax.plot(s['r_over_R500'],np.array(s['late_profile'])/np.array(control['late_profile']),color=cols[s['k']] if shared else '#666666',ls='-' if shared else ':',label=f"Galaxy-scaled work; {s['k']:g}/orbit / control" if shared else 'Small fixed work; 3/orbit / control')
        ax.axhline(1,color='.4',lw=.8);ax.set_title(name);ax.set_xscale('log');ax.set_xlim(.1,1);ax.set_ylim(.1,1.2);ax.grid(alpha=.15)
        ax.set_xticks([.1,.3,1]);ax.set_xticklabels(['0.1','0.3','1']);ax.xaxis.set_minor_formatter(NullFormatter())
    axs.flat[-1].axis('off');handles,labels=axs.flat[0].get_legend_handles_labels();axs.flat[-1].legend(handles,labels,loc='center',fontsize=8)
    fig.supxlabel('Radius / observed R500');fig.supylabel('Enclosed mass / matched no-contact control (8–10 Gyr)')
    fig.suptitle('Observed clusters: galaxy-scaled versus restricted available work',fontsize=12)
    fig.tight_layout();fig.savefig(out/'cluster_profiles.png',dpi=170);plt.close(fig)
    print('ANALYSIS',out)
    for s in runs:
        if s['k']>0 and 'relative_no_contact_at_radii' in s:
            print(s['cluster'],s['label'],s['k'],'ratios', {k:round(v,3) for k,v in s['relative_no_contact_at_radii'].items()},'energy/reserve',round(s['energy_residual_fraction_initial_reserve'],5))
    return out,runs

if __name__=='__main__':main()
