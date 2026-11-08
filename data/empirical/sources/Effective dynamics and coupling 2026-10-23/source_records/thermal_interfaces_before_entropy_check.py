"""Conservative relativistic Euler extension with a selected thermal EOS.
Same cold clock Hamiltonian, constant V=0 and L=3. Add e_th=z*n^(4/3).
This is a causal isotropic fluid closure, not a collisionless halo solver.
"""
from pathlib import Path
import json,numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
HERE=Path(__file__).resolve().parent
GAMMA=4/3;K=1.;L=3.
vc=np.linspace(0,1,300001);rr=1-.5*np.sqrt(1-vc*vc);ll=L*rr;nn=ll*vc
ee=ll/2+2*(L-ll)**3/(3*L*L);rc=ll*vc*vc/2+ee
pc=ll*vc*vc/2-ee+K
cs=4*rr*(1-rr)/(4*rr*(1-rr)+vc*vc)

def cold(n):
    mu=np.interp(n,nn,vc);rho=np.where(n>=L,n,np.interp(n,nn,rc))
    pressure=np.where(n>=L,K,np.interp(n,nn,pc))
    c2=np.where(n>=L,0.,np.interp(n,nn,cs))
    lam=np.where(n>=L,n,np.interp(n,nn,ll))
    return rho-K,pressure,mu,c2,lam

def cons(n,v,eth):
    e0,p0,mu,c2,lam=cold(n);e=e0+eth;p=p0+(GAMMA-1)*eth;h=e+p
    W=1/np.sqrt(1-v*v)
    return np.array([n*W,h*W*W*v,h*W*W-p])

def primitive(state):
    D,M,E=state
    if np.any(D<=0) or np.any(E<=abs(M)):
        raise RuntimeError('Conservative state left positive density/energy cone')
    def fun(p):
        v=M/(E+p);W=1/np.sqrt(1-v*v);n=D/W
        e0,p0,mu,c2,lam=cold(n)
        h=e0+p0+GAMMA/(GAMMA-1)*(p-p0)
        return h*W*W-p-E
    lo=np.zeros_like(D);hi=2*(E+abs(M)+1.)
    fl=fun(lo);fh=fun(hi)
    if fl.max()>1e-7 or fh.min()<0:raise RuntimeError('No physical pressure bracket')
    for _ in range(40):
        mid=(lo+hi)/2;f=fun(mid);below=f<0
        lo=np.where(below,mid,lo);hi=np.where(below,hi,mid)
    p=(lo+hi)/2;v=M/(E+p);W=1/np.sqrt(1-v*v);n=D/W
    e0,p0,mu,c2,lam=cold(n);eth=(p-p0)/(GAMMA-1)
    if eth.min()<-2e-7:raise RuntimeError(f'Negative thermal energy {eth.min()}')
    # No clipping: tiny inversion errors remain in the reported thermal field.
    return n,v,eth,p,mu,c2,lam

def run(N,final=5.):
    domain=24.;dx=domain/N;x=(np.arange(N)+.5)*dx-domain/2
    a=np.clip(abs(x)-3.,0,1);smooth=a**3*(10-15*a+6*a*a)
    n=.2+3.4*smooth;state=cons(n,np.zeros(N),np.zeros(N));initial=state.copy()
    dt=.3*dx;steps=int(np.ceil(final/dt));dt=final/steps
    E0=state[2].mean();D0=state[0].mean();rec=[];snaps=[]
    def flux(s):
        n,v,eth,p,mu,c2,lam=primitive(s)
        return np.array([s[0]*v,s[1]*v+p,s[1]])
    def rhs(s):
        # First-order invariant-domain flux with the unit causal speed bound.
        f=flux(s);edge=.5*(f+np.roll(f,-1,axis=1))-.5*(np.roll(s,-1,axis=1)-s)
        return -(edge-np.roll(edge,1,axis=1))/dx
    for k in range(steps+1):
        if k%max(1,steps//100)==0 or k==steps:
            n,v,eth,p,mu,c2,lam=primitive(state)
            thermal_h=GAMMA*eth;cold_h=n*mu
            total_cs=(cold_h*c2+thermal_h*(GAMMA-1))/(cold_h+thermal_h)
            chemical=mu+GAMMA*eth/n
            gate=n*chemical/(lam+thermal_h)
            rec.append([k*dt,n.min(),eth.min(),state[2].mean()-E0,state[0].mean()-D0,
               eth.mean(),total_cs.min(),total_cs.max(),gate.min(),gate.max()])
        if k in {0,steps//2,steps}:snaps.append(state.copy())
        if k==steps:break
        stage=state+dt*rhs(state);state=.5*(state+stage+dt*rhs(stage))
    rec=np.array(rec);n,v,eth,p,mu,c2,lam=primitive(state)
    result={'grid':N,'dt':dt,'final_time':final,'gamma':GAMMA,
       'minimum_proper_density':float(rec[:,1].min()),'minimum_thermal_energy':float(rec[:,2].min()),
       'max_absolute_mean_energy_drift':float(abs(rec[:,3]).max()),
       'max_absolute_mean_current_drift':float(abs(rec[:,4]).max()),
       'final_mean_thermal_energy':float(eth.mean()),'max_sound_speed_squared':float(rec[:,7].max()),
       'minimum_contact_gate':float(rec[:,8].min()),'maximum_contact_gate':float(rec[:,9].max()),
       'min_final_rest_energy_over_floor':float((cold(n)[0]+eth+K).min()),
       'density_or_thermal_clipping':False}
    print(json.dumps(result),flush=True)
    return result,dict(x=x,final=state,initial=initial,history=rec,snapshots=np.array(snaps),
       n=n,v=v,eth=eth)

def main():
    out=HERE/'results/thermal_interfaces.json';assert not out.exists()
    rows=[];data={};previous=None;changes=[];last=None
    for N in [128,256,512]:
        r,a=run(N);rows.append(r)
        if previous is not None:
            restricted=a['final'].reshape(3,N//2,2).mean(2)
            changes.append(float(np.mean(abs(restricted-previous['final']))))
        data.update({f'n{N}_{key}':value for key,value in a.items()});previous=a;last=a
    out.write_text(json.dumps({'scope':__doc__,'rows':rows,'restricted_mean_state_changes':changes,
      'limitations':['First-order finite-volume viscosity creates resolution-dependent thermal energy.',
         'Chosen gamma=4/3 closure; no native selection or calibrated physical viscosity is claimed.',
         'Planar flat frozen-potential test; no realistic void or collisionless multistream calculation.',
         'Thermal floor and causal inequalities hold for bounded nonnegative entropy coefficient; shocks require the entropy condition.']},indent=2),encoding='utf-8')
    np.savez_compressed(HERE/'results/thermal_interface_traces.npz',**data)
    fig,axs=plt.subplots(1,3,figsize=(12,3.5),layout='constrained')
    for i,s in enumerate(last['snapshots']):
        n,v,eth,p,mu,c2,lam=primitive(s);label=['Initial','Midpoint','Final'][i]
        for ax,val in zip(axs,[n,eth,cold(n)[0]+eth+K]):ax.plot(last['x'],val,label=label)
    for ax,y in zip(axs,['Proper current density','Thermal energy density','Rest energy density / floor']):
        ax.set(xlabel='Position',ylabel=y);ax.grid(alpha=.2)
    axs[0].legend(fontsize=8);fig.suptitle('A selected thermal stress retains the energy of compression')
    fig.savefig(HERE/'figures/thermal_interface.png',dpi=180);plt.close(fig)

if __name__=='__main__':main()
