"""Conservative finite-N spherical gravity for a numerical cross-check.

The particle part is exactly the gradient of W=-G*m^2*sum(i/r_sorted[i]).
The baryonic force is exactly the derivative of the same interpolated potential
used in the energy diagnostic. This removes the archived grid-force / exact-
shell-energy mismatch. It changes no contact rule or continuum force law.
The instantaneous contact potential remains Claude's radial grid potential.
"""
import numpy as np,math
from numba import njit
from scipy.integrate import cumulative_trapezoid
G=4.30091e-6;C=1.0227e-3

def baryon_potential(rg,mb):
    gb=G*mb/rg**2
    phi=-cumulative_trapezoid(gb[::-1],-rg[::-1],initial=0)[::-1]-G*mb[-1]/rg[-1]
    return phi

@njit(cache=True)
def bphi(r,rg,pb):
    if r<rg[0]:
        slope=(pb[1]-pb[0])/(rg[1]-rg[0])
        return pb[0]+slope*(r-rg[0]),slope
    if r>=rg[-1]:return pb[-1]*rg[-1]/r,-pb[-1]*rg[-1]/(r*r)
    i=np.searchsorted(rg,r)-1
    slope=(pb[i+1]-pb[i])/(rg[i+1]-rg[i])
    return pb[i]+slope*(r-rg[i]),slope

@njit(cache=True)
def kick(x,v,rg,pb,m,h,softening=0.):
    r=np.sqrt(np.sum(x*x,axis=1)); order=np.argsort(r)
    for rank in range(len(r)):
        i=order[rank]; rr=r[i];_,ab=bphi(rr,rg,pb)
        aa=-G*rank*m/(rr*rr+softening*softening)**1.5-ab/rr
        for j in range(3):v[i,j]+=h*C*aa*x[i,j]

@njit(cache=True)
def energy(x,v,m,rg,pb,softening=0.):
    r=np.sqrt(np.sum(x*x,axis=1));order=np.argsort(r)
    e=.5*m*np.sum(v*v)
    for rank in range(len(r)):
        rr=r[order[rank]];phi,_=bphi(rr,rg,pb)
        e+=m*phi-G*m*m*rank/math.sqrt(rr*rr+softening*softening)
    return e
