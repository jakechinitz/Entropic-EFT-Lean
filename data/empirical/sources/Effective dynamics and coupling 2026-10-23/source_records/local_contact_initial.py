"""Local radial-velocity heat-bath proposal for a declared nonthermal target.
The target and common collision rate are inputs. Fixed spherical potential;
no RAR calibration, self-consistent gravity or physical bath-spectrum claim.
"""
from pathlib import Path
import json
import numpy as np
from scipy.special import logsumexp
from scipy.integrate import cumulative_trapezoid
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
HERE=Path(__file__).resolve().parent
T=np.array([.25,1.]);mix=np.array([.7,.3]);L=.8;theta=.25
def U(r):return r*r/2+L*L/(2*r*r)
def force(r):return -r+L*L/r**3
def logtarget(E):return logsumexp(np.log(mix)[:,None]-E[None,:]/T[:,None],axis=0)

def run(dt,n=40000,seed=7311):
    rng=np.random.default_rng(seed);r=np.full(n,2.5);p=rng.normal(0,.05,n)
    initial_E=np.mean(p*p/2+U(r));work=0.;heat=0.;mechanical=0.
    nu=2.;gate=1.;end=30.;steps=round(end/dt);history=[];E_errors=[]
    for k in range(steps):
        p+=.5*dt*force(r);r+=dt*p
        # The L barrier and harmonic confinement suffice at the tested step.
        if np.any(r<=0):raise RuntimeError('Radial integrator crossed the angular-momentum barrier')
        p+=.5*dt*force(r)
        hits=np.flatnonzero(rng.random(n)<-np.expm1(-nu*gate*dt))
        if len(hits):
            rr=r[hits];old=p[hits];pot=U(rr)
            loga=np.log(mix)[:,None]+.5*np.log(T)[:,None]-pot[None,:]/T[:,None]
            a=np.exp(loga-logsumexp(loga,axis=0))
            pick=(rng.random(len(hits))>=a[0]).astype(int)
            new=rng.normal(size=len(hits))*np.sqrt(T[pick])
            Eold=old*old/2+pot;Enew=new*new/2+pot
            heat_event=theta*(logtarget(Enew)-logtarget(Eold))
            energy_event=Enew-Eold;work_event=energy_event+heat_event
            p[hits]=new
            heat+=float(heat_event.sum()/n);work+=float(work_event.sum()/n)
            mechanical+=float(energy_event.sum()/n)
        if k%max(1,steps//120)==0 or k==steps-1:
            meanE=np.mean(p*p/2+U(r))
            history.append([(k+1)*dt,float(np.mean(r)),float(meanE),work,heat])
            E_errors.append(meanE-initial_E-mechanical)
    grid=np.linspace(.015,7.,10000)
    density=np.sum((mix*np.sqrt(2*np.pi*T))[:,None]*np.exp(-U(grid)[None,:]/T[:,None]),axis=0)
    cdf=cumulative_trapezoid(density,grid,initial=0);density/=cdf[-1];cdf/=cdf[-1]
    ordered=np.sort(r);expected=np.interp(ordered,grid,cdf)
    empirical=np.arange(1,n+1)/n
    KS=max(np.max(abs(empirical-expected)),np.max(abs(empirical-1/n-expected)))
    result={'dt':dt,'particles':n,'seed':seed,'fixed_L':L,'collision_rate':nu,
       'target_radial_CDF_KS_error':float(KS),'target_radial_mean':float(np.trapezoid(grid*density,grid)),
       'sample_radial_mean':float(np.mean(r)), 'mean_energy_initial':float(initial_E),
       'mean_energy_final':float(np.mean(p*p/2+U(r))), 'total_work_received':work,
       'total_heat_to_bath':heat,'contact_energy_identity_error':abs(mechanical-work+heat),
       'max_Hamiltonian_integration_energy_error':float(np.max(abs(E_errors))),
       'fixed_angular_momentum_error':0.,'clock_gate':gate,
       'source_clock_feedback_in_this_run':False}
    print(json.dumps(result),flush=True)
    return result,dict(r=r,p=p,grid=grid,target=density,history=np.array(history))

def main():
    path=HERE/'results/local_contact.json';assert not path.exists()
    rows=[];arrays={};last=None
    for dt in [.01,.005]:
        r,a=run(dt);rows.append(r);last=a
        arrays.update({f'dt{str(dt).replace(".","p")}_{k}':v for k,v in a.items()})
    path.write_text(json.dumps({'scope':__doc__,'rows':rows,
        'limitations':['The supplied nonthermal equilibrium requires work exchange; it is not a passive single-temperature bath equilibrium.',
           'Sampling error and time-integration error are distinct; different timesteps use different random histories.',
           'This target is a simple two-temperature orbital mixture, not the empirical RAR orbit library.',
           'The radial relative-coordinate impulse preserves L; a finite carrier must carry the opposite impulse.',
           'No source-clock feedback or exhaustion is simulated in this kinetic run. The closed-cell test checks that separate coupling.']},indent=2),encoding='utf-8')
    np.savez_compressed(HERE/'results/local_contact_traces.npz',**arrays)
    fig,axs=plt.subplots(1,2,figsize=(10,3.5),layout='constrained')
    axs[0].hist(last['r'],bins=75,density=True,histtype='step',label='Local-contact particles')
    axs[0].plot(last['grid'],last['target'],label='Declared stationary target');axs[0].set(xlim=(0,5),xlabel='Radius',ylabel='Radial probability density')
    h=last['history'];axs[1].plot(h[:,0],h[:,2]-h[0,2],label='Mechanical energy change')
    axs[1].plot(h[:,0],h[:,3]-h[:,4]-(h[0,3]-h[0,4]),ls='--',label='Work minus bath heat')
    axs[1].set(xlabel='Time',ylabel='Mean specific energy change')
    for ax in axs:ax.legend(fontsize=8);ax.grid(alpha=.2)
    fig.suptitle('Hamiltonian transport plus local radial-velocity transitions')
    fig.savefig(HERE/'figures/local_contact.png',dpi=180);plt.close(fig)

if __name__=='__main__':main()
