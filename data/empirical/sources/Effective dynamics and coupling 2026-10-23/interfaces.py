"""Conservative finite-volume spatial test; no positivity clipping of J."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from model import clock_state

HERE=Path(__file__).resolve().parent
def minmod(a,b):return np.where(a*b>0,np.sign(a)*np.minimum(abs(a),abs(b)),0.)
def run(n,final=5.):
    domain=24.;dx=domain/n;x=(np.arange(n)+.5)*dx-domain/2
    z=np.clip((abs(x)-3.)/1.,0,1);smooth=z**3*(10-15*z+6*z*z)
    U=np.array([.2+3.4*smooth,np.zeros(n)])
    initial=U.copy();dt=.32*dx;steps=int(np.ceil(final/dt));dt=final/steps
    def flux(u):
        v,lam,X,P,rho=clock_state(u[0],u[1],iterations=32)
        return np.array([-lam*u[1],-v])
    def rhs(u):
        slope=minmod(u-np.roll(u,1,axis=1),np.roll(u,-1,axis=1)-u)
        left=u+slope/2;right=np.roll(u-slope/2,-1,axis=1)
        # Unit causal signal bound, valid on the regular branches being tested.
        f=.5*(flux(left)+flux(right))-.5*(right-left)
        return -(f-np.roll(f,1,axis=1))/dx
    v,lam,X,P,rho=clock_state(U[0],U[1]);E0=rho.mean();J0=U[0].mean()
    rec=[];snaps=[]
    for k in range(steps+1):
        if k%max(1,steps//100)==0 or k==steps:
            v,lam,X,P,rho=clock_state(U[0],U[1]);t=k*dt
            outside=abs(x)>4+t+3*dx
            tail=0. if not outside.any() else float(np.max(abs(U[:,outside]-initial[:,outside])))
            rec.append([t,U[0].min(),X.min(),rho.min(),rho.mean(),U[0].mean(),tail])
        if k in {0,steps//2,steps}:snaps.append(U.copy())
        if k==steps:break
        stage=U+dt*rhs(U);U=.5*(U+stage+dt*rhs(stage))
    rec=np.array(rec)
    report={'grid':n,'dt':dt,'final_time':final,'minimum_J':float(rec[:,1].min()),
      'minimum_X':float(rec[:,2].min()),'minimum_energy_over_floor':float(rec[:,3].min()),
      'max_fractional_total_energy_change':float(np.max(abs(rec[:,4]/E0-1))),
      'max_absolute_mean_current_change':float(np.max(abs(rec[:,5]-J0))),
      'max_numerical_tail_outside_unit_cone_plus_three_cells':float(rec[:,6].max()),
      'source_or_current_clipping':False,'negative_current_seen':bool(rec[:,1].min()<0),
      'spacelike_state_seen':bool(rec[:,2].min()<0)}
    print(json.dumps(report),flush=True)
    return report,dict(x=x,final=U,initial=initial,history=rec,snapshots=np.array(snaps))

def main():
    path=HERE/'results/interfaces.json';assert not path.exists()
    rows=[];arrays={};last=None;changes=[]
    for n in [256,512,1024]:
        r,a=run(n);rows.append(r)
        if last is not None:
            restricted=a['final'].reshape(2,n//2,2).mean(axis=2)
            changes.append(float(np.mean(abs(restricted-last['final']))))
        arrays.update({f'n{n}_{k}':v for k,v in a.items()});last=a
    result={'scope':__doc__,'rows':rows,'mean_state_restriction_changes':changes,
      'limitations':['Frozen potential and flat metric, planar periodic geometry; not a cosmological void.',
        'Rusanov flux has numerical viscosity. Energy change and tails require refinement.',
        'This run is not a proof of global well-posedness, interface stability or absence of dust caustics.']}
    path.write_text(json.dumps(result,indent=2),encoding='utf-8')
    np.savez_compressed(HERE/'results/interface_traces.npz',**arrays)
    fig,axs=plt.subplots(1,3,figsize=(12,3.5),layout='constrained')
    x=last['x']
    for i,U in enumerate(last['snapshots']):
        v,lam,X,P,rho=clock_state(U[0],U[1]);lab=['Initial','Midpoint','Final'][i]
        for ax,val in zip(axs,[U[0],v,rho]):ax.plot(x,val,label=lab)
    for ax,y in zip(axs,['Current density','Source-clock time derivative','Total energy density / floor']):
        ax.set(xlabel='Position',ylabel=y);ax.grid(alpha=.2)
    axs[0].legend(fontsize=8);fig.suptitle('Spatial transition from depleted to dust-like regions')
    fig.savefig(HERE/'figures/interface.png',dpi=180);plt.close(fig)

if __name__=='__main__':main()
