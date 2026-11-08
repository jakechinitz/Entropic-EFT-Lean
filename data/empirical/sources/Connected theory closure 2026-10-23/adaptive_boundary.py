"""Constant-energy-floor completion, with a nonnegative source-clock current.

Improves the constant-density-cutoff probe, which allowed clock reversal.
Choose K>sup V on the tested interval and L(phi)=3(K-V(phi)). The minimum
material energy is L/3, so the total minimum energy is the constant K.
The source in the current equation switches from V_phi to V_phi F(r),
F(r)=-1+6r^2-4r^3, r=lambda/L in [1/2,1]. F(r) is O(phidot^2) at depletion.

This is a selected effective action. K and the cubic constitutive form are
not derived from the microscopic action. The demonstration chooses K from
a conservative upper bound on the unreleased homogeneous stock, avoiding a
fit of K to the local solutions. It does not prove uniqueness of that choice.
"""
from pathlib import Path
import json,sys
import numpy as np
import sympy as sp
from scipy.integrate import solve_ivp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from boundary_completion import background,material,ETA,BC,WB,WR

HERE=Path(__file__).resolve().parent

def force_factor(J,L):
    vel,lam,rho,p,cs=material(J,L)
    r=lam/L
    # Factored form avoids cancellation near the nonnegative-current boundary.
    factor=1. if r>=1 else (2*r-1)*(1+2*r-2*r*r)
    return vel,lam,rho,p,cs,factor

def symbolic():
    l,L,Vp=sp.symbols('lambda L Vp',positive=True)
    e=l/2+2*(L-l)**3/(3*L*L)
    r=sp.symbols('r',real=True)
    F=-1+6*r*r-4*r**3
    speed2=1-4*(1-r)**2
    tests={
      'effective_source':sp.simplify((1-3*sp.diff(e,L)).subs(l,L*r)-F),
      'source_factorization':sp.expand(F-(2*r-1)*(1+2*r-2*r*r)),
      'velocity_factorization':sp.expand(speed2-(2*r-1)*(3-2*r)),
      'source_vanishes_at_rest':sp.simplify(F.subs(r,sp.Rational(1,2))),
      'source_matches_dust':sp.simplify(F.subs(r,1)-1),
      'source_over_speed2':sp.cancel(F/speed2-(1+2*r-2*r*r)/(3-2*r)),
      'source_derivative':sp.expand(sp.diff(F,r)-12*r*(1-r)),
    }
    assert all(v==0 for v in tests.values())
    return {k:str(v) for k,v in tests.items()}

def patch(bg,delta,K,refined=False):
    x,a,C,V,E,T,state,potential=bg
    xi=np.log(.01); ai,ci,vi,hi,ti,gi,hpi=state(xi)
    u0=1-.98071*delta/3
    curvature=ai*ai*((WB/ai**3+ci)*(1+delta)+WR/ai**4+vi-(hi*u0)**2)
    def rhs(xx,z):
        y,u,dphi,pJ=z
        aa,cc,vv,hh,tt,gg,hp=state(xx)
        b=aa*np.exp(y);J=pJ*cc
        pot,dp=potential(tt+dphi);L=3*(K-pot)
        assert L>0
        vel,lam,rho,p,cs,factor=force_factor(J,L)
        rho+=pot;p-=pot
        rb=WB*(1+delta)/b**3;rr=WR/b**4
        return [u-1.,-u*u-.5*(rb+2*rr+rho+3*p)/hh**2-u*hp,
                (vel-1.)/hh,3*(1-u)*pJ+gg*pJ-dp*factor/(hh*cc)]
    sol=solve_ivp(rhs,(xi,0),[0.,u0,0.,1+delta],method='DOP853',
                  rtol=2e-10 if refined else 2e-8,atol=2e-12 if refined else 2e-10,
                  max_step=.0008 if refined else .002,dense_output=True)
    assert sol.success,sol.message
    xx=np.linspace(xi,0,3001);zz=sol.sol(xx);samples=[]
    for n,xv in enumerate(xx):
        y,u,dphi,pJ=zz[:,n]
        aa,cc,vv,hh,tt,gg,hp=state(xv);b=aa*np.exp(y)
        pot,dp=potential(tt+dphi);L=3*(K-pot)
        vel,lam,rho,p,cs,factor=force_factor(pJ*cc,L);rho+=pot;p-=pot
        rb=WB*(1+delta)/b**3;rr=WR/b**4
        residual=((hh*u)**2-rb-rr-rho+curvature/b**2)/hh**2
        samples.append([aa,vel,lam/L,rho/K,cs,residual,(1+delta)*np.exp(-3*y),
                        pJ,tt+dphi,pot,L,factor])
    arr=np.array(samples)
    row={'initial_delta':delta,'min_lambda_over_local_cutoff':float(arr[:,2].min()),
         'min_total_dark_energy_over_floor':float(arr[:,3].min()),
         'min_clock_velocity':float(arr[:,1].min()),'min_current_over_background':float(arr[:,7].min()),
         'max_cs2':float(arr[:,4].max()),'max_friedmann_residual_over_Hbg2':float(abs(arr[:,5]).max()),
         'today_baryon_contrast':float(arr[-1,6]),'today_clock_velocity':float(arr[-1,1]),
         'today_current_over_background_stock':float(arr[-1,7]),
         'today_dark_energy_over_background':float(arr[-1,3]*K/(C[-1]+V[-1])),
         'first_departure_a':float(arr[np.flatnonzero(arr[:,1]<1-1e-9)[0],0]) if np.any(arr[:,1]<1-1e-9) else None,
         'vacuum_monotone_in_test':bool(np.min(np.diff(arr[:,9]))>=-2e-12),
         'evaluations':sol.nfev}
    return row,arr

def local_current_test():
    # Smooth nonnegative bounded potential. Empty-current state is invariant;
    # positive currents approach it without changing sign in this example.
    K=1.5
    def pot(phi):
        v=1/(1+np.exp(-phi))
        return v,v*(1-v)
    def rhs(t,z):
        phi,J=z;v,dv=pot(phi);L=3*(K-v)
        speed,lam,rho,p,cs,factor=force_factor(J,L)
        return [speed,-.15*J-dv*factor]
    t=np.linspace(0,80,4001)
    sol=solve_ivp(rhs,(0,80),[-3.,3.],t_eval=t,rtol=2e-11,atol=1e-13,max_step=.01)
    assert sol.success
    values=[]
    for phi,J in sol.y.T:
        v,dv=pot(phi);L=3*(K-v);speed,lam,rho,p,cs,factor=force_factor(J,L)
        values.append([J,speed,rho+v,v,L,cs])
    arr=np.array(values)
    empty_rhs=rhs(0,[-3.,0.])
    return {'min_current':float(arr[:,0].min()),'min_clock_velocity':float(arr[:,1].min()),
            'min_total_energy_over_floor':float(arr[:,2].min()/K),
            'empty_state_rhs':empty_rhs,'vacuum_monotone':bool(np.diff(arr[:,3]).min()>=-1e-14)},(t,arr)

def main():
    mode=sys.argv[1] if len(sys.argv)>1 else 'base';refined=mode=='refined'
    bg=background(160000 if refined else 80000)
    x,a,C,V,E,T,state,potential=bg
    # Future a>=1, F<=1 and monotone: Delta V <= BC*(survival_today-exp(-eta)).
    reserve=C[-1]-BC*np.exp(-ETA)
    K=V[-1]+reserve
    ratio=3*(K-V)/C
    assert reserve>0 and ratio.max()<1
    rows=[];traces={}
    for delta in [0.,-.1,-.35,-.6,-.9]:
        row,arr=patch(bg,delta,K,refined);rows.append(row);traces[f'd{delta}']=arr
        print(json.dumps(row),flush=True)
    local,local_trace=local_current_test()
    report={'status':'Conditional constitutive completion with action-level positivity and unchanged tested linear branch',
            'symbolic':symbolic(),'selected_energy_floor':K,'future_release_upper_bound':reserve,
            'today_density_cutoff_over_background_stock':float(ratio[-1]),
            'max_cutoff_over_background_stock_through_today':float(ratio.max()),
            'exact_linear_branch_margin':float(1-ratio.max()),
            'patches':rows,'local_current':local,
            'limitations':['K selection and cubic constitutive response are additional physical premises.',
                           'The phase field slows relative to proper time in the depleted regime.',
                           'No inhomogeneous PDE or multistream existence theorem is supplied.',
                           'The homogeneous curved patches are not compensated void predictions.',
                           'The fixed-clock action is reproduced only where lambda>L(phi).',
                           'If the native theory requires a unit proper clock in all states, this completion changes that requirement.'],
            'new_likelihood':False,'linear_fit_inheritance':'Exact local action identity on an open neighborhood of the tested homogeneous solution; nonlinear likelihoods are not inherited.'}
    out=HERE/'results'/f'adaptive_boundary_{mode}.json'
    if out.exists():raise RuntimeError('Preserve previous results')
    out.write_text(json.dumps(report,indent=2),encoding='utf-8')
    np.savez(HERE/'results'/f'adaptive_boundary_{mode}_trajectories.npz',**traces)
    if not refined:
        fig,axs=plt.subplots(1,3,figsize=(12,3.8),layout='constrained')
        for key,arr in traces.items():
            if key=='d0.0':continue
            for ax,col in zip(axs,[1,2,3]):ax.plot(arr[:,0],arr[:,col],label=key[1:])
        axs[0].set(xlabel='Background scale factor',ylabel='Clock velocity',ylim=(-.03,1.05))
        axs[1].set(xlabel='Background scale factor',ylabel='Auxiliary density / local threshold',yscale='log',ylim=(.45,1e5))
        axs[2].set(xlabel='Background scale factor',ylabel='Total dark energy / energy floor',yscale='log')
        axs[1].axhline(.5,color='black',lw=.7);axs[2].axhline(1,color='black',lw=.7)
        axs[0].legend(title='Initial density contrast',fontsize=8)
        fig.suptitle('Selected completion: positive continuation with a monotone clock')
        fig.savefig(HERE/'figures/adaptive_boundary.png',dpi=180);plt.close(fig)
    print(json.dumps({'saved':str(out),'max_cutoff_fraction':float(ratio.max()),'local_current':local}),flush=True)

if __name__=='__main__':main()
