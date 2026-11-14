"""Finite-event symmetric clock gate for the same local kinetic proposal.
The edge factor v(U)v(U-W) is symmetric between the joint endpoint states.
The chosen target and base rate remain inputs. Fixed potential, one carrier.
"""
from pathlib import Path
import json,numpy as np
from local_contact import U,force,logtarget,T,mix,L
from scipy.special import logsumexp
from scipy.integrate import cumulative_trapezoid
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
HERE=Path(__file__).resolve().parent

# Homogeneous clock speed squared as a function of total clock density.
# Interpolate v^2, whose slope is finite at the resting endpoint.
v2_grid=np.linspace(0,1,200001);r_grid=1-.5*np.sqrt(1-v2_grid)
lam_grid=3*r_grid;e_grid=lam_grid/2+2*(3-lam_grid)**3/27
rho_grid=lam_grid*v2_grid/2+e_grid
def speed(energy):
    if energy<=1:return 0.
    return float(np.sqrt(np.interp(energy,rho_grid,v2_grid)))

def run(available,dt=.01,n=12000,theta=1e-6,seed=95177):
    rng=np.random.default_rng(seed);r=np.full(n,np.sqrt(L));p=rng.normal(0,.04,n)
    energy=1+available;heat=0.;work=0.;attempted=0;accepted=0;unaffordable=0
    E0=float(np.mean(p*p/2+U(r)));total0=energy+E0;nu=2.;end=60.;history=[]
    for k in range(round(end/dt)):
        p+=.5*dt*force(r);r+=dt*p
        if np.any(r<=0):raise RuntimeError('Crossed L barrier')
        p+=.5*dt*force(r)
        # A rate-nu proposal is thinned by the bounded symmetric edge factor.
        hits=np.flatnonzero(rng.random(n)<-np.expm1(-nu*dt));attempted+=len(hits)
        if len(hits):
            pot=U(r[hits]);olda=p[hits]
            logits=np.log(mix)[:,None]+.5*np.log(T)[:,None]-pot[None,:]/T[:,None]
            a=np.exp(logits-logsumexp(logits,axis=0));pick=(rng.random(len(hits))>=a[0]).astype(int)
            new=rng.normal(size=len(hits))*np.sqrt(T[pick])
            oldE=olda*olda/2+pot;newE=new*new/2+pot
            qs=theta*(logtarget(newE)-logtarget(oldE));ws=newE-oldE+qs
            uniforms=rng.random(len(hits))
            for q,index in enumerate(hits):
                newclock=energy-ws[q]/n
                if newclock<1:
                    unaffordable+=1;continue
                gate=speed(energy)*speed(newclock)
                if uniforms[q]>=gate:continue
                energy=newclock;heat+=qs[q]/n;work+=ws[q]/n;p[index]=new[q];accepted+=1
        if k%max(1,round(.25/dt))==0 or k==round(end/dt)-1:
            kin=float(np.mean(p*p/2+U(r)))
            history.append([(k+1)*dt,energy,speed(energy),kin,heat,work,energy+kin+heat-total0])
    grid=np.linspace(.015,7,10000)
    dens=np.sum((mix*np.sqrt(2*np.pi*T))[:,None]*np.exp(-U(grid)[None,:]/T[:,None]),axis=0)
    cdf=cumulative_trapezoid(dens,grid,initial=0);dens/=cdf[-1];cdf/=cdf[-1]
    ordered=np.sort(r);target=np.interp(ordered,grid,cdf)
    ks=max(np.max(abs(np.arange(1,n+1)/n-target)),np.max(abs(np.arange(n)/n-target)))
    h=np.array(history)
    report={'available_initial_clock_energy':available,'dt':dt,'particles':n,'seed':seed,
      'bath_temperature_in_orbital_units':theta,'gate':'v(U)*v(U-W/N), zero outside allowed clock spectrum',
      'final_clock_energy_above_floor':float(energy-1),'minimum_clock_energy_above_floor':float(h[:,1].min()-1),
      'final_clock_speed':speed(energy),'max_absolute_energy_ledger_error':float(abs(h[:,-1]).max()),
      'proposal_events':attempted,'accepted_events':accepted,'unaffordable_proposals':unaffordable,
      'radial_CDF_KS_from_requested_target':float(ks),'work_to_orbits':float(work),'heat_to_bath':float(heat),
      'no_density_or_energy_clipping':True,'joint_edge_amplitude_symmetric':True}
    print(json.dumps(report),flush=True)
    return report,dict(history=h,r=r,grid=grid,target=dens)

def main():
    out=HERE/'results/hermitian_contact.json';assert not out.exists()
    rows=[];data={};traces=[]
    for available,dt in [(.15,.01),(1.2,.01),(.15,.005),(1.2,.005)]:
        r,a=run(available,dt);rows.append(r);traces.append(a)
        data.update({f'a{available}_dt{dt}_{key}':value for key,value in a.items()})
    out.write_text(json.dumps({'scope':__doc__,'rows':rows,
      'limitations':['The energy-register Hamiltonian is a selected effective dilation, not a microscopic identification of the clock spectrum.',
      'The kinetic and clock energy ledger is coupled; spatial stress, self-gravity and a quantum bath spectrum are not simulated.',
      'The finite-step Poisson thinning converges as dt tends to zero; different steps have independent random histories.',
      'The target distribution, base rate, and weak-coupling/Markov validity remain physical inputs.']},indent=2),encoding='utf-8')
    np.savez_compressed(HERE/'results/hermitian_contact_traces.npz',**data)
    fig,axs=plt.subplots(1,3,figsize=(12,3.5),layout='constrained')
    for row,a in zip(rows[2:],traces[2:]):
        h=a['history'];label=f"Available energy {row['available_initial_clock_energy']}"
        axs[0].plot(h[:,0],h[:,1]-1,label=label);axs[1].semilogy(h[:,0],h[:,2],label=label)
        axs[2].hist(a['r'],bins=60,density=True,histtype='step',label=label)
    axs[2].plot(traces[-1]['grid'],traces[-1]['target'],ls='--',c='black',label='Requested target')
    axs[0].set(xlabel='Time',ylabel='Clock energy above floor');axs[1].set(xlabel='Time',ylabel='Source-clock speed')
    axs[2].set(xlabel='Radius',ylabel='Radial probability density',xlim=(0,4))
    axs[0].legend(fontsize=8);axs[2].legend(fontsize=8)
    for ax in axs:ax.grid(alpha=.2)
    fig.suptitle('Energy-conserving local contact with a symmetric clock gate')
    fig.savefig(HERE/'figures/hermitian_contact.png',dpi=180);plt.close(fig)

if __name__=='__main__':main()
