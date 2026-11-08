"""Separate small-bath-temperature check; target orbital scales are unchanged."""
from pathlib import Path
import json,numpy as np
from kinetic_feedback import run
import matplotlib.pyplot as plt
HERE=Path(__file__).resolve().parent
out=HERE/'results/kinetic_feedback_cold.json';assert not out.exists()
rows=[];data={};traces=[]
for available in [.15,1.2]:
    row,a=run(available,dt=.005,bath_temperature=1e-6)
    rows.append(row);traces.append(a)
    data.update({f'a{available}_{key}':value for key,value in a.items()})
out.write_text(json.dumps({'scope':__doc__,'rows':rows,
 'interpretation':'Thermal heat is negligible compared with mechanical work in this small-temperature demonstration. No dimensional identification with the actual horizon temperature is made.',
 'limitation':'The thermostat, target and rate are still selected effective inputs; this is not a quantum-bath derivation.'},indent=2),encoding='utf-8')
np.savez_compressed(HERE/'results/kinetic_feedback_cold_traces.npz',**data)
fig,axs=plt.subplots(1,3,figsize=(12,3.5),layout='constrained')
for row,a in zip(rows,traces):
    h=a['history'];label=f"Available energy {row['available_initial_clock_energy']}"
    axs[0].plot(h[:,0],h[:,1]-1,label=label)
    axs[1].semilogy(h[:,0],h[:,2],label=label)
    axs[2].hist(a['r'],bins=60,density=True,histtype='step',label=label)
axs[2].plot(traces[-1]['grid'],traces[-1]['target'],ls='--',c='black',label='Requested target')
axs[0].set(xlabel='Time',ylabel='Clock energy above floor');axs[1].set(xlabel='Time',ylabel='Source-clock speed')
axs[2].set(xlabel='Radius',ylabel='Radial probability density',xlim=(0,4))
axs[0].legend(fontsize=8);axs[2].legend(fontsize=8)
for ax in axs:ax.grid(alpha=.2)
fig.suptitle('Finite clock supply with negligible thermal heat exchange')
fig.savefig(HERE/'figures/kinetic_feedback_cold.png',dpi=180);plt.close(fig)
