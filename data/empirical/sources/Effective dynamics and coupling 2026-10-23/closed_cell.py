from pathlib import Path
import json
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from model import clock_homogeneous

HERE=Path(__file__).resolve().parent
def run(available):
    L=3.;K=1.;p=.8;w0=.1;nu=1.;gap=1.;theta=.05
    heat=theta*np.log(p/(1-p));work=gap+heat
    J0=brentq(lambda J:clock_homogeneous(J,L)[2]-K-available,1e-10,10.)
    def rhs(t,y):
        J=np.exp(y[0]);v,lam,rho=clock_homogeneous(J,L)
        b=nu*(p-y[1]);power_coefficient=work*b
        return [-power_coefficient/lam,v*v*b,v*v*heat*b,v*v]
    t=np.linspace(0,180,1801)
    sol=solve_ivp(rhs,(0,t[-1]),[np.log(J0),w0,0.,0.],t_eval=t,rtol=2e-11,atol=2e-13)
    assert sol.success
    J=np.exp(sol.y[0]);states=np.array([clock_homogeneous(x,L) for x in J])
    v,lam,rho=states.T
    total=rho+gap*sol.y[1]+sol.y[2]
    target_cost=work*(p-w0)
    endpoint=w0+min(available,target_cost)/work
    activity_bound=None if available>=target_cost else -np.log1p(-available/target_cost)/nu
    result={'available_clock_energy':available,'target_work':target_cost,'work_gap':work,
      'final_weight':float(sol.y[1,-1]),'predicted_endpoint':float(endpoint),
      'final_clock_speed':float(v[-1]),'min_current':float(J.min()),
      'min_clock_energy_over_floor':float(rho.min()/K),
      'max_absolute_total_energy_error':float(np.max(abs(total-total[0]))),
      'contact_activity':float(sol.y[3,-1]),'predicted_activity_bound':activity_bound,
      'boundary_clipping':False,'positivity_method':'log current integrates a derived regular fractional-rate equation'}
    return result,np.column_stack([t,J,v,rho,sol.y[1],sol.y[2],sol.y[3]])

def main():
    path=HERE/'results/closed_cell.json';assert not path.exists()
    rows=[];traces=[]
    for a in [.25,1.]:
        r,x=run(a);rows.append(r);traces.append(x);print(json.dumps(r),flush=True)
    path.write_text(json.dumps({'scope':'Closed deterministic local cell with prescribed two-state contact and constant clock potential. Internal excitation energy is additional kinetic energy of existing stock, not a second rest-mass source.','rows':rows},indent=2),encoding='utf-8')
    np.savez_compressed(HERE/'results/closed_cell_traces.npz',limited=traces[0],sufficient=traces[1])
    fig,axs=plt.subplots(1,3,figsize=(12,3.5),layout='constrained')
    for r,x in zip(rows,traces):
        label=f"Available energy {r['available_clock_energy']}"
        axs[0].plot(x[:,0],x[:,4],label=label)
        axs[1].semilogy(x[:,0],x[:,2],label=label)
        axs[2].plot(x[:,0],x[:,3]-1,label=label)
    axs[0].axhline(.8,ls='--',c='black',lw=.8,label='Requested target')
    for ax,y in zip(axs,['Upper-state fraction','Source-clock speed','Clock energy above floor']):
        ax.set(xlabel='Time in contact units',ylabel=y,xlim=(0,100));ax.grid(alpha=.2)
    axs[0].legend(fontsize=8)
    fig.suptitle('The same contact reaches its target or stops as its supply is exhausted')
    fig.savefig(HERE/'figures/closed_cell.png',dpi=180);plt.close(fig)

if __name__=='__main__':main()
