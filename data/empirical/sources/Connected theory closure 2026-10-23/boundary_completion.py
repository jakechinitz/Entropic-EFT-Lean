"""Selected low-density constitutive completion; no empirical likelihood.

Units: densities in 3 H100^2/(8 pi G), time in H100^-1, X=-dphi^2/2.
The auxiliary density lambda is restricted to lambda >= L/2. On the
intermediate branch e=lambda/2+2(L-lambda)^3/(3L^2); above L, e=lambda/2.
At X<0 the constrained endpoint supplies P=(L/2)X-L/3-V.
Homogeneous tests only use X>=0. The scalar action is lambda X-e(lambda)-V.
"""
from pathlib import Path
import json, sys
import numpy as np
import sympy as sp
from scipy.integrate import cumulative_trapezoid, solve_ivp
from scipy.interpolate import PchipInterpolator
from scipy.optimize import brentq
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[1]
EMP=ROOT/'02 Research/Unified empirical program 2026-10-23'
ETA=.029866844393522368
WR=2.4728e-5*(1+.2271*3.044)
PARAMS=json.loads((EMP/'results/cosmology_final.json').read_text())['fit_parameters']
WB,MIX=PARAMS[:2]; BC=5.333*WB
FTAB=np.load(ROOT/'02 Research/Release zoom/Frel_table.npy')
j=min(int(MIX/.05),len(FTAB)-2); f=MIX/.05-j
zt=np.round(np.arange(30,-1e-9,-.01),4)
FS=PchipInterpolator(-np.log1p(zt),(1-f)*FTAB[j]+f*FTAB[j+1],extrapolate=False)

def background(n):
    x=np.linspace(np.log(1e-8),0,n); a=np.exp(x)
    active=x>=-np.log(31)
    F=np.zeros(n); g=np.zeros(n)
    F[active]=FS(x[active]); g[active]=ETA*FS.derivative()(x[active])
    C=BC*np.exp(-ETA*F-3*x)
    V=cumulative_trapezoid(C*g,x,initial=0)
    E=np.sqrt(WB/a**3+WR/a**4+C+V)
    T=cumulative_trapezoid(1/E,x,initial=0)
    v_of_t=PchipInterpolator(T,V)
    def state(xx):
        aa=np.exp(xx)
        ff=0. if xx<-np.log(31) else float(FS(xx))
        gg=0. if xx<-np.log(31) else float(ETA*FS.derivative()(xx))
        cc=BC*np.exp(-ETA*ff-3*xx)
        vv=float(np.interp(xx,x,V)); hh=np.sqrt(WB/aa**3+WR/aa**4+cc+vv)
        hp=-(3*(WB/aa**3+cc)+4*WR/aa**4)/(2*hh**2)
        return aa,cc,vv,hh,float(np.interp(xx,x,T)),gg,hp
    def potential(phi):
        # The tests remain inside the tabulated range. Constant continuation
        # records a bounded nonnegative extension outside that range.
        if phi<=T[0]: return float(V[0]),0.
        if phi>=T[-1]: return float(V[-1]),0.
        return float(v_of_t(phi)),float(v_of_t.derivative()(phi))
    return x,a,C,V,E,T,state,potential

def material(J,L):
    q=abs(J)/L
    if q>=1:
        v=float(np.sign(J)); lam=abs(J); e=lam/2; cs=0.
    elif q==0:
        v=0.;lam=L/2;e=L/3;cs=1.
    else:
        va=brentq(lambda u:u*(1-.5*np.sqrt(max(0.,1-u*u)))-q,
                  0.,1.,xtol=5e-15)
        v=float(np.copysign(va,J));lam=L*(1-.5*np.sqrt(max(0.,1-v*v)))
        e=lam/2+2*(L-lam)**3/(3*L*L)
        epp=4*(L-lam)/L**2
        cs=lam*epp/(lam*epp+v*v)
    X=v*v/2
    return v,lam,lam*X+e,lam*X-e,cs

def symbolic():
    l,L,X,V,td,grad=sp.symbols('lambda L X V td grad',positive=True)
    e=l/2+2*(L-l)**3/(3*L**2)
    ep=sp.diff(e,l); epp=sp.diff(e,l,2)
    tests={
        'value_matching':sp.simplify(e.subs(l,L)-L/2),
        'first_derivative_matching':sp.simplify(ep.subs(l,L)-sp.Rational(1,2)),
        'second_derivative_matching':sp.simplify(epp.subs(l,L)),
        'lower_endpoint_X':sp.simplify(ep.subs(l,L/2)),
        'lower_endpoint_energy':sp.simplify(e.subs(l,L/2)-L/3),
        'stress_energy_identity':sp.simplify(l*td**2-(l*(td**2-grad)/2-e-V)
                                        -(l*(td**2+grad)/2+e+V)),
    }
    assert all(v==0 for v in tests.values())
    y=sp.symbols('y',real=True)
    numerator=sp.expand((l*epp).subs(l,L*y))
    denominator=sp.expand((l*epp+2*ep).subs(l,L*y))
    return {'zero_residuals':{k:str(v) for k,v in tests.items()},
            'normalized_cs_numerator':str(numerator),
            'normalized_cs_denominator':str(denominator),
            'sound_speed_range':'0 <= c_s^2 <= 1 for 1/2 <= lambda/L <= 1; endpoints by continuity',
            'scope':'Algebra and timelike principal symbol; no global inhomogeneous existence theorem.'}

def parcel_test():
    L=1.; q=.2; J0=2.; V0=1.; grid=np.linspace(0,18,3601)
    # Constant potential slope in a fixed, non-expanding local cell.
    sol=solve_ivp(lambda t,z:[material(J0-q*t,L)[0]],(grid[0],grid[-1]),[0.],
                  t_eval=grid,rtol=2e-11,atol=2e-13,max_step=.0025)
    assert sol.success
    phi=sol.y[0]; out=np.array([material(J0-q*t,L) for t in grid])
    v,lam,rho,p,cs=out.T
    V=V0+q*phi
    total=rho+V
    expected=J0+V0
    return {'min_auxiliary_density':float(lam.min()),
            'min_material_energy':float(rho.min()),
            'min_total_energy':float(total.min()),
            'relative_energy_drift':float(np.max(abs(total-expected))/expected),
            'old_dust_density_at_end':float(J0-q*grid[-1]),
            'clock_turnaround_time':J0/q,
            'clock_reverses':bool(np.any(v<0)),
            'cs2_min':float(cs.min()),'cs2_max':float(cs.max())},(grid,phi,v,lam,rho,V,cs)

def patch_test(bg,delta,Lfrac,refined=False):
    x,a,C,V,E,T,state,potential=bg
    xi=np.log(.01); ai,ci,vi,hi,ti,gi,hpi=state(xi)
    L=Lfrac*C[-1]
    u0=1-.98071*delta/3
    # This is a homogeneous curved FRW patch, with its radiation conserved
    # locally. It is not an embedded compensated void or a survey likelihood.
    K=ai**2*((WB/ai**3+ci)*(1+delta)+WR/ai**4+vi-(hi*u0)**2)
    def rhs(xx,z):
        y,u,dphi,pJ=z
        aa,cc,vv,hh,tt,gg,hp=state(xx)
        b=aa*np.exp(y); J=pJ*cc
        velocity,lam,material_rho,material_p,cs=material(J,L)
        pot,dp=potential(tt+dphi)
        rho=material_rho+pot; press=material_p-pot
        rb=WB*(1+delta)/b**3; rr=WR/b**4
        return [u-1.,-u*u-.5*(rb+2*rr+rho+3*press)/hh**2-u*hp,
                (velocity-1.)/hh,
                3*(1-u)*pJ+gg*pJ-dp/(hh*cc)]
    sol=solve_ivp(rhs,(xi,0),[0.,u0,0.,1+delta],method='DOP853',
                  rtol=2e-10 if refined else 2e-8,
                  atol=2e-12 if refined else 2e-10,
                  max_step=.0008 if refined else .002,dense_output=True)
    assert sol.success,sol.message
    xx=np.linspace(xi,0,3001); zz=sol.sol(xx); samples=[]
    for n,xv in enumerate(xx):
        y,u,dphi,pJ=zz[:,n]
        aa,cc,vv,hh,tt,gg,hp=state(xv)
        b=aa*np.exp(y); vel,lam,rho,p,cs=material(pJ*cc,L)
        pot,dp=potential(tt+dphi); rho+=pot; p-=pot
        rb=WB*(1+delta)/b**3;rr=WR/b**4
        fried=(hh*u)**2-(rb+rr+rho)+K/b**2
        samples.append([np.exp(xv),vel,lam,rho,cs,fried/(hh*hh),
                        (1+delta)*np.exp(-3*y),pJ,tt+dphi])
    arr=np.array(samples)
    row={'initial_delta':delta,'cutoff_over_today_background_stock':Lfrac,
         'min_lambda_over_cutoff':float(np.min(arr[:,2])/L),
         'min_total_dark_energy':float(np.min(arr[:,3])),
         'min_clock_velocity':float(np.min(arr[:,1])),
         'max_cs2':float(np.max(arr[:,4])),
         'max_friedmann_residual_over_Hbg2':float(np.max(abs(arr[:,5]))),
         'today_baryon_contrast':float(arr[-1,6]),
         'today_current_over_background_stock':float(arr[-1,7]),
         'today_dark_energy_over_background':float(arr[-1,3]/(C[-1]+V[-1])),
         'first_departure_a':float(arr[np.flatnonzero(arr[:,1]<1-1e-9)[0],0]) if np.any(arr[:,1]<1-1e-9) else None,
         'min_phi':float(arr[:,8].min()),'evaluations':sol.nfev}
    return row,arr

def main():
    mode=sys.argv[1] if len(sys.argv)>1 else 'base'
    refined=mode=='refined'; n=160000 if refined else 80000
    bg=background(n)
    sym=symbolic(); parcel,trace=parcel_test()
    rows=[]; traces={}
    for delta,frac in [(0.,.01),(-.1,.01),(-.35,.01),(-.6,.01),(-.9,.01),(-.6,.001),(-.6,.03)]:
        row,arr=patch_test(bg,delta,frac,refined)
        rows.append(row);traces[f'd{delta}_f{frac}']=arr
        print(json.dumps(row),flush=True)
    report={'status':'Conditional selected effective completion; nonlinear observations and multistream extension open',
            'symbolic':sym,'parcel':parcel,'patches':rows,
            'background_grid':n,'fit_inheritance':'Exact action identity for lambda>L; threshold below minimum homogeneous stock through today. No new likelihood is claimed.',
            'extra_choices':['positive density cutoff L','cubic transition with lower endpoint L/2',
                             'canonical constrained continuation at spacelike X','continuation of V outside reconstructed clock range'],
            'limitations':['Clock can reverse locally; universal monotonic clock is relinquished in the depleted phase.',
                           'Single potential flow does not resolve multistream caustics.',
                           'Positive energy and causal principal symbol do not prove nonlinear PDE stability or observational agreement.',
                           'Patch test uses locally conserved radiation and has no compensating exterior.']}
    out=HERE/'results'/f'boundary_{mode}.json'
    if out.exists(): raise RuntimeError('Refusing to overwrite existing results')
    out.write_text(json.dumps(report,indent=2),encoding='utf-8')
    np.savez(HERE/'results'/f'boundary_{mode}_trajectories.npz',**traces)
    if not refined:
        t,phi,vel,lam,rho,pot,cs=trace
        fig,axs=plt.subplots(1,3,figsize=(12,3.7),layout='constrained')
        axs[0].plot(t,2-.2*t,label='Uniform-drain dust');axs[0].plot(t,lam,label='Auxiliary density')
        axs[0].plot(t,rho,label='Material energy');axs[0].axhline(0,color='gray',lw=.6)
        axs[0].set(xlabel='Time (chosen local units)',ylabel='Density / cutoff',title='Continuation through depletion');axs[0].legend(fontsize=8)
        axs[1].plot(t,vel,label='Clock velocity');axs[1].plot(t,cs,label='Sound speed squared')
        axs[1].set(xlabel='Time',title='The clock turns; energy stays positive');axs[1].legend(fontsize=8)
        axs[2].plot(t,rho+pot,label='Total energy');axs[2].plot(t,pot,label='Prescribed potential evaluated on field')
        axs[2].set(xlabel='Time',title='Local energy ledger');axs[2].legend(fontsize=8)
        fig.savefig(HERE/'figures/boundary_completion.png',dpi=180);plt.close(fig)
    print(json.dumps({'saved':str(out),'parcel':parcel}),flush=True)

if __name__=='__main__':main()
