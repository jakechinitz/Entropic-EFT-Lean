"""Audit positivity of the effective density of the numerical force kernel.

Positive particle masses do not imply positivity of a finite multipole / radial
spline reconstruction. This differentiates that potential analytically and
checks the result against a divergence of the force at independent points.
The evolved masses themselves remain strictly positive.
"""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['NUMBA_NUM_THREADS']='1'
import sys,json,argparse
import numpy as np
from scipy.special import roots_legendre
HERE=Path(__file__).resolve().parent;QUIET=HERE.parent/'Halo quiet realization 2026-10-21'
sys.path.insert(0,str(QUIET))
from fast_smooth_field import deposit,evaluate,assignment,values,ELL,G,njit
from live_quiet_fast import stock_target
from numba import set_num_threads
set_num_threads(1)

def density_coefficients(R,nodes,grid,eps):
    result=[];dl=np.log(grid[1]/grid[0])
    for r in R:
        j,w,dw,s=assignment(r,grid,eps);u=np.log(s/grid[j+1])/dl
        Wd=np.array([-.5*(1-u)**2,1.5*u*u-2*u,-1.5*u*u+u+.5,.5*u*u])
        Wdd=np.array([1-u,3*u-2,1-3*u,u])
        up=r/(s*s*dl);upp=(eps*eps-r*r)/(s**4*dl)
        ddw=Wdd*up*up+Wd*upp
        v=w@nodes[j:j+4];dv=dw@nodes[j:j+4];ddv=ddw@nodes[j:j+4]
        f=(r/s)**ELL;g=ELL*eps*eps/(r*s*s)
        gp=-ELL*eps*eps*(3*r*r+eps*eps)/(r*r*s**4)
        fp=f*g;fpp=f*(g*g+gp)
        result.append((fpp*v+2*fp*dv+f*ddv+2/r*(fp*v+f*dv)-ELL*(ELL+1)/r**2*f*v)/(4*np.pi*G))
    return np.array(result)

def diagnose(X,w,grid,eps,ms):
    nodes=deposit(X,w*ms,grid,eps)
    mu,wm=roots_legendre(16);phi=np.arange(32)*2*np.pi/32
    mm,pp=np.meshgrid(mu,phi,indexing='ij');dirs=np.c_[np.sqrt(1-mm.ravel()**2)*np.cos(pp.ravel()),np.sqrt(1-mm.ravel()**2)*np.sin(pp.ravel()),mm.ravel()]
    basis=np.array([values(*x) for x in dirs]);wa=np.repeat(wm,32)/64
    shells=[]
    for lo,hi in [(.2,5.),(5.,60.),(60.,160.)]:
        # Eight samples per log-grid interval, positive Gauss integration weights.
        edges=np.geomspace(lo,hi,int(np.ceil(np.log(hi/lo)/np.log(grid[1]/grid[0])*8))+1)
        u,wu=roots_legendre(3);R=(edges[:-1,None]+edges[1:,None])/2+(edges[1:,None]-edges[:-1,None])/2*u
        wr=(edges[1:,None]-edges[:-1,None])/2*wu;R=R.ravel();wr=wr.ravel()
        rho=density_coefficients(R,nodes,grid,eps)@basis.T
        neg=np.maximum(-rho,0)@wa;pos=np.maximum(rho,0)@wa
        mn=float(4*np.pi*np.sum(wr*R**2*neg));mp=float(4*np.pi*np.sum(wr*R**2*pos))
        shells.append({'radial_range_kpc':[lo,hi],'negative_effective_mass_Msun':mn,
            'negative_fraction_of_total_stock':mn/ms,'negative_fraction_of_positive_effective_mass':mn/mp,
            'signed_effective_mass_Msun':mp-mn,'minimum_density_Msun_kpc3':float(rho.min())})
    Q=np.array([[8.1,1.1,2.7],[18.2,-3.5,6.3],[43.2,7.8,-15.1]])
    rr=np.linalg.norm(Q,axis=1);coeff=density_coefficients(rr,nodes,grid,eps)
    exact=np.sum(coeff*np.array([values(*(x/r)) for x,r in zip(Q,rr)]),axis=1)
    h=rr*1e-5;div=np.zeros(len(Q))
    for k in range(3):
        plus=Q.copy();minus=Q.copy();plus[:,k]+=h;minus[:,k]-=h
        ap,_=evaluate(plus,nodes,grid,eps,np.zeros(len(Q)));am,_=evaluate(minus,nodes,grid,eps,np.zeros(len(Q)))
        div+=(ap[:,k]-am[:,k])/(2*h)
    numerical=-div/(4*np.pi*G);err=np.max(abs(numerical-exact)/np.maximum(abs(exact),1.))
    assert err<1e-4,(err,numerical,exact)
    return {'shells':shells,'force_divergence_relative_error_max':float(err)}

def run(root,folder,seedfile,label,initial=False):
    sd=np.load(root/seedfile);n=len(sd['X'])//2;w=2*sd['weights'][:n]
    X=sd['X'][:n] if initial else np.load(root/folder/'state_08.0.npz')['X']
    _,ms=stock_target()
    return {'label':label,'time_Gyr':0 if initial else 8,**diagnose(X,w,sd['grid'],float(sd['eps']),ms)}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--reference-only',action='store_true');a=p.parse_args()
    old=(QUIET,'live_131072_eps02_dt05_continue8','quiet_seed_131072.npz','Original')
    if a.reference_only:out=[run(*old,initial=True),run(*old)];name='density_reconstruction_reference.json'
    else:
        out=[run(HERE,f'live_seed{s}_8',f'quiet_seed_{s}.npz',f'Replica {i}') for i,s in enumerate([211034,211035],1)];name='density_reconstruction_final.json'
    result={'runs':out,'qualification':'Density inferred from the numerical kernel Laplacian, not negative particle mass. Finite l and radial spline errors are included; no central r<0.2 kpc or outer r>160 kpc positivity claim.'}
    assert not (HERE/name).exists();(HERE/name).write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
