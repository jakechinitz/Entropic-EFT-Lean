from pathlib import Path
import numpy as np,matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from thermal_interfaces import cold,primitive
HERE=Path(__file__).resolve().parent
d=np.load(HERE/'results/thermal_refinement_traces.npz');x=d['n2048_x']
out=HERE/'figures/thermal_interface_refined.png';assert not out.exists()
fig,axs=plt.subplots(1,3,figsize=(12,3.5),layout='constrained')
for k,state in enumerate(d['n2048_snapshots']):
    n,v,eth,p,mu,c2,lam=primitive(state);label=['Initial','Midpoint','Final'][k]
    for ax,y in zip(axs,[n,eth,cold(n)[0]+eth+1]):ax.plot(x,y,label=label)
for ax,y in zip(axs,['Proper current density','Thermal energy density','Rest energy density / floor']):
    ax.set(xlabel='Position',ylabel=y);ax.grid(alpha=.2)
axs[0].legend(fontsize=8);fig.suptitle('Conservative thermal continuation at 2048 cells')
fig.savefig(out,dpi=180);plt.close(fig)
