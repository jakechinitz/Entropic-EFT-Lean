"""Fixed-count replication outcomes, with no choice of favorable epochs."""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
os.environ['NUMBA_NUM_THREADS']='1'
import sys, json, argparse
import numpy as np
HERE=Path(__file__).resolve().parent
QUIET=HERE.parent/'Halo quiet realization 2026-10-21'
sys.path.insert(0,str(QUIET))
from analysis_common import load_run as old_run

def current_run(seed):
    return json.loads((HERE/f'live_seed{seed}_8/results.json').read_text())

def metrics(d,label,seed):
    rows=d['rows']; av=d['half_Gyr_averages']; last=rows[-1]
    if not av:return {'label':label,'seed':seed,'end':last['time']}
    final=av[-1]; h=final['stock']['radial'][4]; s=final['stars']['radial'][4]
    J=np.array(d['J0']);J/=np.linalg.norm(J)
    e1=np.array([0.,0.,1.]);e1-=e1@J*J;e1/=np.linalg.norm(e1);e2=np.cross(J,e1)
    normals=np.array([r['disk_normal'] for r in rows]);t=np.array([r['time'] for r in rows])
    phase=np.unwrap(np.arctan2(normals@e2,normals@e1));slope,intercept=np.polyfit(t,phase,1)
    diskangles=np.degrees(np.arccos(np.clip(normals@J,-1,1)))
    def axis_az(v):
        a=np.array(v['stock']['radial'][4]['major_axis']);a*=1 if a[0]>=0 else -1
        return float(np.degrees(np.arctan2(a[1],a[0])))
    history=[{'end':a['end'],'halo':a['stock']['radial'][4]['tilt'],
              'stars':a['stars']['radial'][4]['tilt'],'beta':a['stars']['radial'][1]['beta'],
              'halo_azimuth':axis_az(a),'halo_gap':a['stock']['radial'][4]['eigen_gap'],
              'stars_gap':a['stars']['radial'][4]['eigen_gap'],
              'halo_density_L1':a['stock']['L1_density_6_60'],
              'stars_density_L1':a['stars']['L1_density_6_60']} for a in av]
    mchange={r:float(last['mass_inside'][r]/rows[0]['mass_inside'][r]-1) for r in last['mass_inside']}
    gates={'energy':d['maximum_sampled_energy_error']<.001,
           'J':d['maximum_sampled_J_error']<1e-6,'completed':last['time']==8.}
    return {'label':label,'seed':seed,'end':last['time'],'N':d['particles_represented'],
            'numerical_gates':gates,'numerical_pass':all(gates.values()),
            'descriptive_retention':bool(h['tilt']>=35 and s['tilt']>=20),
            'final_halo_tilt':h['tilt'],'final_stellar_tilt':s['tilt'],
            'final_beta_10_20':final['stars']['radial'][1]['beta'],
            'final_halo_shape':h,'final_stellar_shape':s,
            'final_halo_density_L1':final['stock']['L1_density_6_60'],
            'final_stellar_density_L1':final['stars']['L1_density_6_60'],
            'energy_max':d['maximum_sampled_energy_error'],'J_max':d['maximum_sampled_J_error'],
            'mass_fractional_change':mchange,'disk_spin_fraction':last['disk_spin_fraction'],
            'precession_rate_rad_Gyr':float(slope),
            'precession_rate_relative_input':float(slope/(.5954784772215926/.9778)),
            'phase_linear_fit_max_residual_deg':float(np.max(abs(phase-(slope*t+intercept)))*180/np.pi),
            'disk_angle_J_range':[float(diskangles.min()),float(diskangles.max())],
            'disk_angle_J_final':float(diskangles[-1]),'final_halo_azimuth':history[-1]['halo_azimuth'],
            'halo_gap_min':min(x['halo_gap'] for x in history),
            'final_two_Gyr':[x for x in history if x['end']>6.],
            'half_Gyr_history':history,'last_instantaneous':last,
            'qualifications':['Angles from averaged position moments in the 10-40 kpc cut.',
              'Beta is the raw second-moment diagnostic, not streaming-subtracted.',
              'The retention flag is descriptive, not an observational likelihood.',
              'All realizations share fitted orbit totals and stellar phases.']}

def collect():
    a=old_run('live_131072_eps02_dt05_continue8')
    ds=[(a,'Original',211033)]
    ds += [(current_run(s),f'Replica {i}',s) for i,s in enumerate([211034,211035],1)]
    return ds

def figures(ds):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False,
        'savefig.dpi':190,'axes.labelcolor':'#183744','text.color':'#183744'})
    cols=['#2079a6','#cd6c24','#24836b']
    fig,ax=plt.subplots(2,2,figsize=(10,6.5),sharex=True,layout='constrained')
    for (d,label,seed),col in zip(ds,cols):
        av=d['half_Gyr_averages'];t=[a['end']-.25 for a in av]
        m=metrics(d,label,seed)
        ys=[[a['stock']['radial'][4]['tilt'] for a in av],
            [a['stars']['radial'][4]['tilt'] for a in av],
            [a['stars']['radial'][1]['beta'] for a in av],
            [x['halo_azimuth'] for x in m['half_Gyr_history']]]
        for panel,y in zip(ax.ravel(),ys):panel.plot(t,y,'o-',ms=3,color=col,label=label)
    for key,color,ls,label in [('live_eps02_dt05_8','#a1a5aa','--','65,536 reference'),('rigid_quiet_8','#666c75',':','Prescribed field')]:
        d=old_run(key);av=d['half_Gyr_averages'];t=[a['end']-.25 for a in av]
        ax[0,0].plot(t,[a['stock']['radial'][4]['tilt'] for a in av],ls,color=color,lw=1,label=label)
        ax[0,1].plot(t,[a['stars']['radial'][4]['tilt'] for a in av],ls,color=color,lw=1)
    ax[0,0].axhline(43,color='#bbb',lw=.7);ax[0,1].axhline(25.4,color='#bbb',lw=.7)
    ax[0,0].set_ylabel('Halo inclination (degrees)');ax[0,1].set_ylabel('Stellar inclination (degrees)')
    ax[1,0].set_ylabel('Stellar beta, 10-20 kpc');ax[1,1].set_ylabel('Halo azimuth in disk frame (degrees)')
    for panel in ax.ravel():panel.grid(alpha=.18);panel.set_xlim(0,8)
    for panel in ax[1]:panel.set_xlabel('Time (Gyr)')
    ax[0,0].legend(fontsize=8,loc='lower left')
    fig.suptitle('Fixed particle count: three independent stock phase seeds\nHalf-Gyr averaged moments; no outcome retuning',fontsize=13)
    for ext in ['png','svg']:fig.savefig(HERE/f'replication_evolution.{ext}')
    plt.close(fig)
    fig,ax=plt.subplots(2,2,figsize=(10,6),sharex=True,layout='constrained')
    for (d,label,seed),col in zip(ds,cols):
        m=metrics(d,label,seed);hist=m['half_Gyr_history'];t=[x['end']-.25 for x in hist]
        for panel,key in zip(ax.ravel(),['halo_gap','stars_gap','halo_density_L1','stars_density_L1']):
            panel.plot(t,[x[key] for x in hist],color=col,label=label)
    for panel,label in zip(ax.ravel(),['Halo shape eigenvalue gap','Stellar shape eigenvalue gap','Halo density L1, 6-60 kpc','Stellar density L1, 6-60 kpc']):
        panel.set_ylabel(label);panel.grid(alpha=.18);panel.set_xlim(0,8)
    for panel in ax[1]:panel.set_xlabel('Time (Gyr)')
    ax[0,0].legend(fontsize=8)
    fig.suptitle('Shape and density diagnostics alongside tilt retention',fontsize=13)
    for ext in ['png','svg']:fig.savefig(HERE/f'replication_shapes.{ext}')
    plt.close(fig)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--progress',action='store_true');a=p.parse_args()
    ds=collect();res=[metrics(*d) for d in ds]
    if a.progress:
        print(json.dumps([{k:r.get(k) for k in ['label','end','final_halo_tilt','final_stellar_tilt','energy_max','J_max']} for r in res],indent=2))
    else:
        assert all(r['end']==8 for r in res),'Wait for every registered run.'
        assert not (HERE/'replication_assessment.json').exists(),'Preserve final reports.'
        result={'runs':res,'targets':{'halo':43.,'stars':25.4},
            'final_halo_range':[min(r['final_halo_tilt'] for r in res),max(r['final_halo_tilt'] for r in res)],
            'final_stellar_range':[min(r['final_stellar_tilt'] for r in res),max(r['final_stellar_tilt'] for r in res)],
            'retention_count':sum(r['descriptive_retention'] for r in res),
            'sample_qualification':'Three seeds at one N, conditional on common orbit fit; no population confidence interval or continuum convergence.'}
        (HERE/'replication_assessment.json').write_text(json.dumps(result,indent=2))
        figures(ds)
        import force_compatibility as fc
        fc.HERE=HERE;fc.load_run=lambda name:json.loads((HERE/name/'results.json').read_text())
        checks=[fc.check(f'live_seed{s}_8') for s in [211034,211035]]
        (HERE/'final_force_checks.json').write_text(json.dumps(checks,indent=2))
        print(json.dumps([{k:r[k] for k in ['label','final_halo_tilt','final_stellar_tilt','energy_max','J_max','descriptive_retention']} for r in res],indent=2))
