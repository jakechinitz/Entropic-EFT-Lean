"""Necessary moment stationarity, separate from initial force matching.

This is a diagnostic only. It does not alter the registered live realizations.
For rotating coordinates w=v-Omega cross x and
wdot=a-2 Omega cross v+Omega cross (Omega cross x).
For Q=<q(r) xx^T>, differentiate q as well as xx^T. A smooth radial
envelope avoids mistaking flux through a sharp radial cut for nonstationarity.
"""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['NUMBA_NUM_THREADS']='1'
import sys,json
import numpy as np
HERE=Path(__file__).resolve().parent;QUIET=HERE.parent/'Halo quiet realization 2026-10-21'
sys.path.insert(0,str(QUIET))
from fast_smooth_field import deposit,evaluate,njit
from live_quiet_fast import baryon  # Initializes the preserved orbit-module paths.
from precessing_equilibrium import radial_tables,stock_target,TU
from halo_quadrupole import field
from fast_external import accel
from numba import set_num_threads
set_num_threads(1)

@njit(cache=True)
def forces(X,lr,tab):
    aa=np.zeros_like(X);ab=np.zeros_like(X)
    for i in range(len(X)):
        x,y,z=X[i]
        aa[i]=field(x,y,z,.3,np.cos(np.radians(43.)),np.sin(np.radians(43.)),lr,tab)
        ab[i]=accel(x,y,z,0.,0.,1.)
    return aa,ab

def moments(X,V,a,weights,om,R=None):
    omega=np.array([om,0.,0.]);w=V-np.cross(omega,X)
    dw=a-2*np.cross(omega,V)+np.cross(omega,np.cross(omega,X))
    r=np.linalg.norm(X,axis=1);rd=np.sum(X*w,axis=1)/r
    rdd=(np.sum(w*w+X*dw,axis=1)-rd*rd)/r
    if R is None:q=np.ones(len(X));qd=np.zeros(len(X));qdd=qd.copy()
    else:
        u=(r/R)**4;q=1/(1+u)
        qp=-4*r**3/R**4/(1+u)**2
        qpp=-12*r**2/R**4/(1+u)**2+32*r**6/R**8/(1+u)**3
        qd=qp*rd;qdd=qpp*rd**2+qp*rdd
    cross=lambda A,B,c:(A.T*(weights*c))@B
    Q=cross(X,X,q)
    Qd=cross(w,X,q)+cross(X,w,q)+cross(X,X,qd)
    Qdd=(cross(dw,X,q)+cross(X,dw,q)+2*cross(w,w,q)
         +2*cross(w,X,qd)+2*cross(X,w,qd)+cross(X,X,qdd))
    dev=lambda M:M-np.eye(3)*np.trace(M)/3
    norm=lambda M:float(np.linalg.norm(M))
    anis=norm(dev(Q));flow=norm(dev(Qd));curv=norm(dev(Qdd))
    return {'envelope_R_kpc':R,'Q':Q.tolist(),'Qdot_rotating':Qd.tolist(),
            'Qddot_rotating':Qdd.tolist(),
            'fractional_anisotropy_flow_per_Gyr':flow/anis/TU,
            'fractional_anisotropy_curvature_per_Gyr2':curv/anis/TU**2,
            'Qdot_trace_per_Gyr':float(np.trace(Qd)/np.trace(Q)/TU),
            'Qddot_trace_per_Gyr2':float(np.trace(Qdd)/np.trace(Q)/TU**2),
            'curvature_over_kinetic_moment':curv/norm(2*cross(w,w,q))}

if __name__=='__main__':
    lr,tab,*_=radial_tables();_,ms=stock_target();out=[]
    for root,filename,label in [(QUIET,'quiet_seed_131072.npz','Original'),
          (HERE,'quiet_seed_211034.npz','Replica 1'),(HERE,'quiet_seed_211035.npz','Replica 2')]:
        sd=np.load(root/filename);n=len(sd['X'])//2;X=sd['X'][:n];V=sd['V'][:n]
        w=2*sd['weights'][:n];om=float(sd['Omega']);aa,ab=forces(X,lr,tab)
        nodes=deposit(X,ms*w,sd['grid'],float(sd['eps']))
        astock,_=evaluate(X,nodes,sd['grid'],float(sd['eps']),ms*w/2)
        out.append({'label':label,'analytic':[moments(X,V,aa,w,om,R) for R in [None,20.,40.]],
                    'live_initial':[moments(X,V,astock+ab,w,om,R) for R in [None,20.,40.]]})
    result={'runs':out,'qualification':
        'Necessary finite-sample moment diagnostics. Nonzero curvature can be sampling noise, finite orbit-time bias, or force approximation. It is not a measured instability growth rate. R is a smooth envelope, not the 10-40 kpc reported shape cut.'}
    assert not (HERE/'initial_stationarity.json').exists()
    (HERE/'initial_stationarity.json').write_text(json.dumps(result,indent=2))
    print(json.dumps([{'label':r['label'],'analytic_curvatures':[v['fractional_anisotropy_curvature_per_Gyr2'] for v in r['analytic']],
          'live_curvatures':[v['fractional_anisotropy_curvature_per_Gyr2'] for v in r['live_initial']]} for r in out],indent=2))
