"""Hamiltonian constitutive inversion for the existing selected clock action."""
import numpy as np

def clock_state(J,s=0.,L=3.,V=0.,iterations=42):
    J,s=np.broadcast_arrays(np.asarray(J),np.asarray(s))
    q=np.abs(J)/L;sgn=np.sign(J)
    canonical=q<=.5*np.abs(s);dust=q>=np.sqrt(1+s*s)
    lo=np.full(J.shape,.5);hi=np.ones(J.shape)
    for _ in range(iterations):
        r=(lo+hi)/2
        val=r*np.sqrt(np.maximum(0,s*s+1-4*(1-r)**2))
        below=val<q;lo=np.where(below,r,lo);hi=np.where(below,hi,r)
    r=(lo+hi)/2;lam=L*r
    v=sgn*np.sqrt(np.maximum(0,s*s+1-4*(1-r)**2))
    lam=np.where(canonical,L/2,lam);v=np.where(canonical,2*J/L,v)
    v=np.where(dust,sgn*np.sqrt(1+s*s),v)
    lam=np.where(dust,np.abs(J)/np.sqrt(1+s*s),lam)
    e=lam/2+2*np.maximum(L-lam,0.)**3/(3*L*L)
    e=np.where(canonical,L/3,e)
    X=(v*v-s*s)/2;P=lam*X-e-V;rho=J*v-P
    return v,lam,X,P,rho

def clock_homogeneous(J,L=3.):
    # Solve in velocity, avoiding cancellation in X at very small current.
    J=float(J)
    if J>=L:return 1.,J,J
    if J==0:return 0.,L/2,L/3
    lo=0.;hi=min(1.,2*J/L)
    for _ in range(48):
        v=(lo+hi)/2;r=1-.5*np.sqrt(max(0.,1-v*v))
        if L*r*v<J:lo=v
        else:hi=v
    v=(lo+hi)/2;r=1-.5*np.sqrt(max(0.,1-v*v));lam=L*r
    e=lam/2+2*(L-lam)**3/(3*L*L)
    return v,lam,lam*v*v/2+e
