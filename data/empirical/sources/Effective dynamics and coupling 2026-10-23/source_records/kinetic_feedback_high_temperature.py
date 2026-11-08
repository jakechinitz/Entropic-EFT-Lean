"""One-carrier finite-energy contact demonstration.
The clock is a common coarse energy reservoir. Kinetic excitation energy is
included once, without adding a second rest-mass density. This energy-level
coupling is not a full covariant multistream stress/action derivation.
"""
from pathlib import Path
import json,numpy as np
from scipy.optimize import brentq
from scipy.special import logsumexp
from scipy.integrate import cumulative_trapezoid
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from model import clock_homogeneous
from local_contact import U,force,logtarget,T,mix,L,theta
HERE=Path(__file__).resolve().parent

def run(available,dt=.01,n=16000,seed=28119):
    rng=np.random.default_rng(seed);r=np.full(n,np.sqrt(L));p=rng.normal(0,.04,n)
    K=1.;energy=K+available;heat=0.;work=0.;rejected=0;attempted=0
    Ekin0=float(np.mean(p*p/2+U(r)));total0=energy+Ekin0;nu=2.;end=60.
    history=[];Jprevious=brentq(lambda j:clock_homogeneous(j)[2]-energy,0,10)
    for k in range(round(end/dt)):
        p+=.5*dt*force(r);r+=dt*p
        if np.any(r<=0):raise RuntimeError('Crossed angular barrier')
        p+=.5*dt*force(r)
        J=brentq(lambda j:clock_homogeneous(j)[2]-energy,0,max(10.,energy+1),xtol=2e-12)
        v,lam,_=clock_homogeneous(J);gate=v*v
        hits=np.flatnonzero(rng.random(n)<-np.expm1(-nu*gate*dt));attempted+=len(hits)
        if len(hits):
            pot=U(r[hits]);olda=p[hits]
            logits=np.log(mix)[:,None]+.5*np.log(T)[:,None]-pot[None,:]/T[:,None]
            a=np.exp(logits-logsumexp(logits,axis=0));pick=(rng.random(len(hits))>=a[0]).astype(int)
            new=rng.normal(size=len(hits))*np.sqrt(T[pick])
            oldE=olda*olda/2+pot;newE=new*new/2+pot
            qs=theta*(logtarget(newE)-logtarget(oldE));ws=newE-oldE+qs
            for q,index in enumerate(hits):
                cost=ws[q]/n
                # Finite-event admissibility, not clipping an exhausted state.
                if cost>energy-K:
                    rejected+=1;continue
                energy-=cost;heat+=qs[q]/n;work+=cost;p[index]=new[q]
        if k%max(1,round(.25/dt))==0 or k==round(end/dt)-1:
            kin=float(np.mean(p*p/2+U(r)))
            history.append([(k+1)*dt,energy,v,kin,heat,work,energy+kin+heat-total0])
    grid=np.linspace(.015,7,10000)
    dens=np.sum((mix*np.sqrt(2*np.pi*T))[:,None]*np.exp(-U(grid)[None,:]/T[:,None]),axis=0)
    cdf=cumulative_trapezoid(dens,grid,initial=0);dens/=cdf[-1];cdf/=cdf[-1]
    ordered=np.sort(r);targetcdf=np.interp(ordered,grid,cdf)
    ks=max(np.max(abs(np.arange(1,n+1)/n-targetcdf)),np.max(abs(np.arange(n)/n-targetcdf)))
    hist=np.array(history)
    report={'available_initial_clock_energy':available,'dt':dt,'particles':n,'seed':seed,
      'final_clock_energy_above_floor':float(energy-K),'minimum_clock_energy_above_floor':float(hist[:,1].min()-K),
      'final_clock_speed':float(hist[-1,2]),'max_absolute_energy_ledger_error':float(abs(hist[:,-1]).max()),
      'attempted_events':attempted,'rejected_unaffordable_events':rejected,
      'radial_CDF_KS_from_requested_target':float(ks),'work_to_orbits':float(work),'heat_to_bath':float(heat),
      'initial_orbit_energy':Ekin0,'final_orbit_energy':float(np.mean(p*p/2+U(r))),
      'no_density_or_energy_clipping':True,'fixed_L':L}
    print(json.dumps(report),flush=True)
    return report,dict(history=hist,r=r,grid=grid,target=dens)

def main():
    out=HERE/'results/kinetic_feedback.json';assert not out.exists()
    rows=[];data={};traces=[]
    for avail,dt in [(.15,.01),(1.2,.01),(.15,.005),(1.2,.005)]:
        r,a=run(avail,dt);rows.append(r);traces.append(a)
        data.update({f'a{avail}_dt{dt}_{key}':value for key,value in a.items()})
    out.write_text(json.dumps({'scope':__doc__,'rows':rows,'limitations':[
      'Single shared carrier reservoir and frozen spherical potential; no local gravity feedback or cosmological expansion.',
      'Dimensionless excitation energies are chosen for a stress test, not a halo calibration.',
      'Finite-energy rejection modifies the prescribed target near the floor.',
      'A covariant allocation of kinetic stress and the bath momentum remains necessary before this represents the full same-stock theory.']},indent=2),encoding='utf-8')
    np.savez_compressed(HERE/'results/kinetic_feedback_traces.npz',**data)
    fig,axs=plt.subplots(1,3,figsize=(12,3.5),layout='constrained')
    for row,a in zip(rows[2:],traces[2:]):
        h=a['history'];label=f"Available energy {row['available_initial_clock_energy']}"
        axs[0].plot(h[:,0],h[:,1]-1,label=label)
        axs[1].semilogy(h[:,0],h[:,2],label=label)
        axs[2].hist(a['r'],bins=60,density=True,histtype='step',label=label)
    axs[2].plot(traces[-1]['grid'],traces[-1]['target'],ls='--',c='black',label='Requested target')
    axs[0].set(xlabel='Time',ylabel='Clock energy above floor');axs[1].set(xlabel='Time',ylabel='Source-clock speed')
    axs[2].set(xlabel='Radius',ylabel='Radial probability density',xlim=(0,4))
    axs[0].legend(fontsize=8);axs[2].legend(fontsize=8)
    for ax in axs:ax.grid(alpha=.2)
    fig.suptitle('Local velocity transitions with a finite clock-energy supply')
    fig.savefig(HERE/'figures/kinetic_feedback.png',dpi=180);plt.close(fig)

if __name__=='__main__':main()
