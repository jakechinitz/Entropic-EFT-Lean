from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
HERE=Path(__file__).resolve().parent;QUIET=HERE.parent/'Halo quiet realization 2026-10-21'
read=lambda root,name:json.loads((root/name).read_text())
sources=[read(QUIET,'temporal_check_131072.json')]+[read(HERE,f'temporal_diagnostics_{s}.json') for s in [211034,211035]]
multi=[read(HERE,'higher_multipole_reference.json')['runs'][-1]]+read(HERE,'higher_multipole_final.json')['runs']
colors=['#2079a6','#cd6c24','#24836b'];labels=['Original','Replica 1','Replica 2']
plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False,'savefig.dpi':190})
fig,ax=plt.subplots(1,2,figsize=(10,4),layout='constrained')
for d,m,c,label in zip(sources,multi,colors,labels):
    ax[0].plot([r['time_Gyr'] for r in d['rows']],
       [100*max(x['transverse_force_error'] for x in r['quiet']['force_errors'] if 8.2<=x['r_kpc']<=60) for r in d['rows']],
       'o-',color=c,ms=4,label=label)
    R=[r['radius_kpc'] for r in m['rows']]
    ax[1].plot(R,[100*r['l4_to_l6_transverse_fraction'] for r in m['rows']],'-o',color=c,ms=4,label=label)
    ax[1].plot(R,[100*r['l6_to_l8_transverse_fraction'] for r in m['rows']],'--',color=c,lw=1)
ax[0].set_xlabel('Time in prescribed field (Gyr)');ax[0].set_ylabel('Max transverse-force error (%)')
ax[0].set_title('Unfitted future phases, 8.2-60 kpc');ax[0].legend(fontsize=8)
ax[1].set_xlabel('Radius (kpc)');ax[1].set_ylabel('Increment / transverse force (%)')
ax[1].set_title('Final snapshots: solid 4 to 6; dashed 6 to 8')
for a in ax:a.grid(alpha=.2)
for ext in ['png','svg']:fig.savefig(HERE/f'force_resolution.{ext}')
plt.close(fig)
