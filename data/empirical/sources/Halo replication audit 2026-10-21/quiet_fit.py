"""Entropy phase quadrature at fixed positive orbit totals; no orbit refit."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['NUMBA_NUM_THREADS']='1'
from smooth_field import *
from pathlib import Path
import json,time,argparse
from scipy.optimize import minimize
from scipy.special import roots_legendre
sys.path.insert(0,str(HERE.parent/'Halo and growth followup 2026-10-21'))
from precessing_equilibrium import radial_tables,stock_target,MD,AD,TU
from halo_quadrupole import interp,field as analytic_field
from fast_external import accel
from weak_endpoints import observables
HERE=Path(__file__).resolve().parent
os.environ['NUMBA_NUM_THREADS']='1'  # Legacy phase imports set this to four.

@njit(cache=True)
def force_rows(X,radii,grid,eps,ms):
    out=np.zeros((len(radii)*30,len(X)))
    for i in range(len(X)):
        r=np.sqrt(np.dot(X[i],X[i]));q=values(X[i,0]/r,X[i,1]/r,X[i,2]/r)
        j,w,dw,s=assignment(r,grid,eps)
        for k in range(len(radii)):
            R=radii[k];h,v,dv,S=assignment(R,grid,eps)
            for c in range(15):
                l=ELL[c];f=(R/S)**l;df=l*f*eps*eps/(R*S*S);ks=0.;kd=0.
                for a in range(4):
                    for b in range(4):
                        ra=grid[h+a];rb=grid[j+b];ker=min(ra,rb)**l/max(ra,rb)**(l+1)
                        ks+=v[a]*w[b]*ker;kd+=dv[a]*w[b]*ker
                out[k*30+c,i]=-G*ms*q[c]*(r/s)**l*f*ks
                out[k*30+15+c,i]=-G*ms*q[c]*(r/s)**l*(df*ks+f*kd)
    return out

@njit(cache=True)
def mechanical_rows(X,V,om):
    out=np.zeros((11,len(X)))
    for i in range(len(X)):
        x,y,z=X[i];vx,vy,vz=V[i]
        out[:3,i]=np.array([y*vz-z*vy,z*vx-x*vz,x*vy-y*vx])
        ax,ay,az=accel(x,y,z,0.,0.,1.)
        out[3,i]=y*az-z*ay;out[4,i]=z*ax-x*az
        out[5:,i]=observables(x,y,z,vx,vy,vz,om)[9:]
    return out

def diagnostics(X,V,w,grid,eps,om,ms):
    nodes=deposit(X,ms*w,grid,eps);mu,wm=roots_legendre(12);ph=np.arange(24)*2*np.pi/24
    mm,pp=np.meshgrid(mu,ph,indexing='ij');dirs=np.c_[np.sqrt(1-mm.ravel()**2)*np.cos(pp.ravel()),np.sqrt(1-mm.ravel()**2)*np.sin(pp.ravel()),mm.ravel()]
    wa=np.repeat(wm,24)/48;lr,tab,*_=radial_tables();ct=np.cos(np.radians(43));st=np.sin(np.radians(43));rows=[]
    for R in [6.,8.2,10.,12.,15.,20.,28.,40.,50.,60.,80.]:
        query=R*dirs;a,_=evaluate(query,nodes,grid,eps,np.zeros(len(query)))
        exact=np.array([np.array(analytic_field(*x,.3,ct,st,lr,tab))-np.array(accel(*x,0.,0.,1.)) for x in query])
        trans=lambda u:u-np.sum(u*dirs,axis=1)[:,None]*dirs
        rms=lambda u:np.sqrt(np.sum(wa*np.sum(u*u,axis=1)))
        rows.append({'r_kpc':R,'total_force_error':float(rms(a-exact)/rms(exact)),
            'transverse_force_error':float(rms(trans(a-exact))/rms(trans(exact)))})
    mech=mechanical_rows(X,V,om)@w;Ld=MD*2*AD*220;J=mech[:3]*ms/Ld+np.array([0,0,1])
    return {'force_errors':rows,'J_over_Ldisk':J.tolist(),'J_direction_error_deg':float(np.degrees(np.arctan2(np.linalg.norm(J[1:]),J[0]))),
        'torque_over_required':(mech[3:5]*ms/(om*Ld)).tolist(),'shape_flow':mech[5:].tolist()}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--suffix',default='');args=ap.parse_args()
    assert not (HERE/f'quiet_seed{args.suffix}.npz').exists(),'Preserve the existing seed; use a new suffix.'
    start=time.time();d=np.load(HERE/f'phase_bank{args.suffix}.npz');X=d['X'];V=d['V'];prior=d['prior'];group=d['group'];wg=d['orbit_weights'];offset=d['offsets'];om=float(d['Omega'])
    grid=np.geomspace(.001,1e5,181);eps=.2;tar,ms=stock_target();lr,tab,*_=radial_tables()
    radii=np.array([6.,8.2,10.,15.,20.,40.,60.,80.]);F=force_rows(X,radii,grid,eps,ms)
    qe=values(np.cos(np.radians(43)),0.,np.sin(np.radians(43)));goal=[]
    for R in radii:
        t=interp(R,lr,tab);p=np.zeros(15);dp=p.copy();p[0]=t[1];dp[0]=t[0];p[1:6]=.3*t[2]*qe[1:6];dp[1:6]=.3*t[3]*qe[1:6]
        goal.extend(np.r_[p,dp])
    lib=np.load(HERE.parent/'Halo and growth followup 2026-10-21/precession_extension_stock/library.npz')
    Lx=wg@lib['moments'][:3,d['orbit_indices'],0].mean(0);Ld=MD*2*AD*220
    F=np.vstack([F,mechanical_rows(X,V,om)]);goal=np.r_[goal,Lx,0.,-Ld/ms,0.,om*Ld/ms,np.zeros(6)]
    # Whiten within-orbit covariance; per-orbit constants cannot be adjusted.
    means=np.array([F[:,offset[i]:offset[i+1]]@prior[offset[i]:offset[i+1]]/wg[i] for i in range(len(wg))]).T
    scales=np.sqrt(np.sum(F*F*prior,axis=1))
    scales=np.maximum(scales,1e-10);F/=scales[:,None];goal/=scales;means/=scales[:,None]
    cov=(F*prior)@F.T-(means*wg)@means.T;ev,U=np.linalg.eigh(cov);keep=ev>ev[-1]*1e-10
    T=(U[:,keep]/np.sqrt(ev[keep])).T;B=np.ascontiguousarray(T@F);b=T@goal
    calls=[0]
    def fun(lam):
        z=lam@B;zm=np.maximum.reduceat(z,offset[:-1]);e=prior*np.exp(z-zm[group]);s=np.add.reduceat(e,offset[:-1]);w=e*wg[group]/s[group]
        value=wg@(np.log(s/wg)+zm)-lam@b;grad=B@w-b;calls[0]+=1
        if calls[0]%100==0:print('eval',calls[0],'dual',value,'gradient',np.max(abs(grad)),flush=True)
        return value,grad
    before=diagnostics(X,V,prior,grid,eps,om,ms);print('Fitting',B.shape,'whitened phase constraints',flush=True)
    res=minimize(fun,np.zeros(len(b)),jac=True,method='L-BFGS-B',options={'maxiter':2000,'gtol':1e-9,'ftol':1e-14,'maxcor':40,'maxls':50})
    z=res.x@B;zm=np.maximum.reduceat(z,offset[:-1]);e=prior*np.exp(z-zm[group]);s=np.add.reduceat(e,offset[:-1]);w=e*wg[group]/s[group]
    after=diagnostics(X,V,w,grid,eps,om,ms)
    np.savez_compressed(HERE/f'quiet_seed{args.suffix}.npz',X=np.r_[X,-X],V=np.r_[V,-V],weights=np.r_[w,w]/2,prior=np.r_[prior,prior]/2,Omega=om,grid=grid,eps=eps)
    result={'success':bool(res.success),'message':str(res.message),'iterations':int(res.nit),'retained_rank':int(keep.sum()),'rows':len(goal),
        'max_scaled_row_residual':float(abs(F@w-goal).max()),'max_whitened_residual':float(abs(B@w-b).max()),
        'orbit_mass_error':float(abs(np.bincount(group,weights=w)-wg).max()),'weight_ratio_quantiles':np.quantile(w/prior,[0,.01,.1,.5,.9,.99,1]).tolist(),
        'KL':float(np.sum(w*np.log(w/prior))),'effective_paired_particles':float(2/(w@w)),
        'before':before,'after':after,'seconds':time.time()-start,
        'qualification':'Initial phase quadrature; per-orbit totals unchanged. Reweighted finite phases are not proven stationary.'}
    (HERE/f'quiet_fit{args.suffix}.json').write_text(json.dumps(result,indent=2));print(json.dumps({k:v for k,v in result.items() if k not in ['before','after']},indent=2),flush=True)
