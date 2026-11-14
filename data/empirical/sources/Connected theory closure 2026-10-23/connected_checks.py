"""Analytic/small numerical checks of the five connections. No new data fit."""
from pathlib import Path
import json
import numpy as np
import sympy as sp
from scipy.integrate import quad, solve_ivp
from scipy.linalg import expm
from scipy.interpolate import PchipInterpolator
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from boundary_completion import background, ETA

HERE=Path(__file__).resolve().parent
G=6.67428908131e-11; MSUN=1.98847e30; KPC=3.0856775814913673e19
H100_GYR=1/9.7779222168

def noise_factor(r,s):
    # x=omega/gamma; H=1. Spectrum convention exactly matches paper N.8.
    k=s/r
    def integrand(x):
        if x==0: return 2*(1+k)/(np.pi*k)
        coth=1/np.tanh(np.pi*r*x)
        return 2*r*k*(1+k)*x*coth/((1+x*x)*(k*k+x*x))
    val,err=quad(integrand,0,np.inf,epsabs=2e-10,epsrel=2e-10,limit=300)
    f0=2*r if abs(r-s)<1e-14 else 2*r*s*np.log(s/r)/(s-r)
    return val,err,f0

def noise_tests():
    rows=[]
    for r in [.01,.1,1.,10.,50.,100.]:
        for ratio in [1.,3.,10.]:
            s=r*ratio;F,err,F0=noise_factor(r,s);delay=1/r+1/s
            rows.append({'gamma_over_H':r,'Omega_over_H':s,'variance_factor':F,
                         'quadrature_error':err,'zero_temperature_lower_bound':F0,
                         'mean_delay_times_H':delay,'F_times_delay_times_H':F*delay})
    requirements=[]
    for x in [.1,1.,3.]:
        sensitivity=x/(2*(-np.expm1(-x)))
        log_drift=1.5*sensitivity # matter-dominated epoch, fixed baryonic force
        tolerance=.03
        max_delay=tolerance/log_drift
        Fmin=4/max_delay
        nmin=Fmin*np.exp(-x)/(.03**2)
        requirements.append({'bose_argument':x,'assumed_abs_dlnH_dlna':1.5,
                             'occupation_tracking_tolerance':tolerance,
                             'max_mean_delay_H_adiabatic':max_delay,
                             'variance_factor_lower_bound':Fmin,
                             'Neff_for_3percent_instantaneous_force_rms':nmin})
    return {'two_pole_rows':rows,'adiabatic_requirements':requirements,
            'scope':'Exact two-pole noise-delay inequality; tracking estimate is adiabatic. Temporal averaging can reduce measured noise. No observed noise likelihood.'}

def rate_counterexample():
    p=np.array([.15,.35,.5]);L=p[:,None]-np.eye(3);w=np.array([1.,0.,0.]);rows=[]
    for rate in [.1,1.,10.]:
        generator=rate*L; out=expm(generator)@w
        flux=generator*p[None,:]
        rows.append({'rate':rate,'stationary_residual':float(np.max(abs(generator@p))),
                     'detailed_balance_residual':float(np.max(abs(flux-flux.T))),
                     'state_at_time_one':out.tolist(),'L1_distance_to_equilibrium':float(abs(out-p).sum())})
    return rows

def lag_tests(bg):
    x,a,C,V,H,T,state,potential=bg
    start=-np.log(7); sel=x>=start;xx=x[sel];tt=T[sel]/H100_GYR
    tt=tt-tt[0]; hh=H[sel]; h0=H[-1]
    a0today=1.258826956399366e-10
    gb=2e-10; target=1/np.expm1(np.sqrt(gb/(a0today*hh/h0)))
    ts=PchipInterpolator(tt,target); rows=[];tracks=[]
    for tau in [.1,.5,2.]:
        for initial in ['equilibrated','unoccupied']:
            n0=target[0] if initial=='equilibrated' else 0.
            sol=solve_ivp(lambda t,n:[(ts(t)-n[0])/tau,(n[0]-n[1])/tau],
                          (tt[0],tt[-1]),[n0,n0],t_eval=tt,rtol=2e-10,atol=2e-12,max_step=.01)
            assert sol.success
            total_ratio=(1+sol.y[1])/(1+target)
            row={'two_equal_pole_time_Gyr':tau,'initial_condition':initial,
                 'min_total_force_over_instantaneous_equilibrium':float(total_ratio.min()),
                 'max_total_force_over_instantaneous_equilibrium':float(total_ratio.max()),
                 'today_force_ratio':float(total_ratio[-1]),
                 'force_ratio_z23':float(np.interp(-np.log(3.3),xx,total_ratio))}
            rows.append(row);tracks.append((tau,initial,np.exp(-xx)-1,total_ratio))
    fig,ax=plt.subplots(figsize=(7.8,4.4),layout='constrained')
    for tau,initial,z,ratio in tracks:
        ax.plot(z,ratio,label=f'{tau:g} Gyr; {initial}',ls='-' if initial=='equilibrated' else '--')
    ax.axhline(1,color='black',lw=.7);ax.set(xlim=(0,6),xlabel='Redshift',ylabel='Force / instantaneous equilibrium force',
        title='A passive lag depends on the initial occupation')
    ax.legend(fontsize=8,ncol=2);fig.savefig(HERE/'figures/response_history.png',dpi=170);plt.close(fig)
    return {'rows':rows,'scope':'Fixed baryonic acceleration, positive equal-pole kernel, formation at z=6. A sign result and illustrative histories, not a galaxy fit.'}

def stock_budget(bg):
    a0=1.258826956399366e-10;rows=[]
    for mb in [1e9,1e10,6e10,1e11]:
        rm=np.sqrt(G*mb*MSUN/a0)/KPC
        for k in [5.1761,14.,30.]:
            rt=rm/np.log1p(1/k)
            rows.append({'present_baryon_mass_Msun':mb,'stock_budget_per_present_baryon':k,
                         'rM_kpc':rm,'latest_exact_RAR_radius_kpc':rt,
                         'RAR_stock_per_present_baryon_at_1Mpc':float(1/np.expm1(rm/1000))})
    # Same baryons and stock mass, different positive spherical stationary targets.
    # Circular-shell kinetic witnesses exist as in O.3; collective stability is open.
    profiles=[]
    for scale in [10.,40.]:
        radius=20.;mass=14*6e10*radius**3/(radius**2+scale**2)**1.5
        profiles.append({'plummer_scale_kpc':scale,'enclosed_stock_Msun_at_20kpc':mass,
                         'stock_acceleration_m_s2_at_20kpc':G*mass*MSUN/(radius*KPC)**2})
    return {'point_source_budget_rows':rows,'equilibrium_counterexamples':profiles,
            'scope':'The cap uses the whole specified Lagrangian stock budget, not a universal bound per present baryon. This reproduces a known cap principle and makes its cross-sector restriction explicit.'}

def receiver_tradeoff(bg):
    x,a,C,V,H,T,state,potential=bg
    sel=a>=1/31;x=x[sel];a=a[sel];C=C[sel];V=V[sel];H=H[sel]
    g=np.array([state(t)[5] for t in x]); oc=C/H**2
    product=2*g*g/(3*oc); ix=int(np.argmax(product));rows=[]
    for f in [.001,.005,.01,.03]:
        psiN=np.sqrt(3*f*oc);alpha=-g/psiN
        B=2*alpha**2;D=(1-f)*C;W=f*C;U=V+W/2
        rows.append({'receiver_fraction_of_capacity_enthalpy':f,
                     'max_unscreened_stock_force_enhancement':float(B.max()),
                     'max_product_residual':float(np.max(abs(f*B-product))),
                     'background_density_identity_max_relerr':float(np.max(abs((D+W/2+U)/(C+V)-1))),
                     'background_pressure_identity_max_abserr':float(np.max(abs(W/2-U+V)))})
    return {'max_f_times_force_enhancement':float(product[ix]),'redshift_at_max':float(1/a[ix]-1),
            'rows':rows,'scope':'Constant-f canonical family and unscreened subhorizon force. Scalar mass, screening and observational transfer functions remain relevant.'}

def symbolic_checks():
    C,V,W,Cp,Vp,Wp,H,alpha,speed=sp.symbols('C V W Cp Vp Wp H alpha speed',real=True)
    D=C-W;U=V+W/2
    exchange=Cp-Wp+3*H*(C-W)
    scalar_energy_deriv=Vp+Wp+3*H*W
    checks={'density_split':sp.expand(D+W/2+U-C-V),
            'pressure_split':sp.expand(W/2-U+V),
            'total_exchange':sp.expand(exchange+scalar_energy_deriv-(Cp+3*H*C+Vp))}
    # GR TT matrix for propagation in the z direction.
    hp,hc,k,w,Z=sp.symbols('hplus hcross k omega Z',real=True)
    mat=sp.Matrix([[hp,hc,0],[hc,-hp,0],[0,0,0]])
    checks['TT_trace']=sp.trace(mat)
    checks['TT_transverse']=sum((mat*sp.Matrix([0,0,1])))
    checks['TT_norm']=sp.expand(sp.trace(mat.T*mat)-2*(hp**2+hc**2))
    action=Z*sp.Rational(1,4)*(w*w-k*k)*(hp*hp+hc*hc)
    hessian=sp.hessian(action,(hp,hc))
    checks['TT_equal_principal_coefficients']=sp.simplify(hessian[0,0]-hessian[1,1])
    checks['TT_offdiagonal']=hessian[0,1]
    r=sp.symbols('r',positive=True)
    checks['noise_delay_log_derivative']=sp.simplify(sp.diff(sp.log(r)-2*(r-1)/(r+1),r)
                                              -(r-1)**2/(r*(r+1)**2))
    assert all(v==0 for v in checks.values())
    return {k:str(v) for k,v in checks.items()}

def main():
    bg=background(80000)
    results={'symbolic':symbolic_checks(),'stock':stock_budget(bg),'rates':rate_counterexample(),
             'response':lag_tests(bg),'noise':noise_tests(),'receiver':receiver_tradeoff(bg),
             'new_empirical_fit':False}
    out=HERE/'results/connected_checks.json'
    if out.exists():raise RuntimeError('Preserve previous result before rerunning')
    out.write_text(json.dumps(results,indent=2),encoding='utf-8')
    print(json.dumps({'saved':str(out),'noise_requirements':results['noise']['adiabatic_requirements'],
                      'receiver':results['receiver'],'lag_rows':results['response']['rows']}),flush=True)

if __name__=='__main__':main()
