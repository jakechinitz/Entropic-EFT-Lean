from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from analyze_replicas import collect
HERE=Path(__file__).resolve().parent;QUIET=HERE.parent/'Halo quiet realization 2026-10-21'
target=json.loads((QUIET/'final_assessment.json').read_text())['desired_shape_moments']['stars']['radial'][:4]
fig,ax=plt.subplots(1,3,figsize=(10,3.4),layout='constrained');x=range(4)
for (d,label,seed),color in zip(collect(),['#2079a6','#cd6c24','#24836b']):
    rows=d['half_Gyr_averages'][-1]['stars']['radial'][:4]
    for a,key in zip(ax,['tilt','p','q']):a.plot(x,[r[key] for r in rows],'o-',color=color,label=label,ms=4)
for a,key,label in zip(ax,['tilt','p','q'],['Stellar inclination (degrees)','Stellar inertia ratio p','Stellar inertia ratio q']):
    a.plot(x,[r[key] for r in target],'k--',lw=1,label='Adopted target')
    a.set_xticks(list(x),['6-10','10-20','20-40','40-60']);a.set_xlabel('Radial bin (kpc)');a.set_ylabel(label)
    a.grid(alpha=.2);a.spines[['top','right']].set_visible(False)
ax[0].legend(fontsize=7)
fig.suptitle('Final averaged stellar shape: radial variation remains visible',fontsize=12)
for ext in ['png','svg']:fig.savefig(HERE/f'radial_shapes.{ext}',dpi=190)
plt.close(fig)
