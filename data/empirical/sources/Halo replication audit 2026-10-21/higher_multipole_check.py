"""Frozen-snapshot l=4 -> 6 -> 8 force comparison, same radial kernel.

Complete normalized real harmonic multiplets satisfy sum_m q_lm(n)q_lm(n')
=P_l(n dot n'). No evolved run is changed by this diagnostic. It is not a
replacement for actually evolving a converged angular expansion.
"""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['NUMBA_NUM_THREADS']='1'
import sys,json,argparse,math
import numpy as np
from scipy.special import lpmv,roots_legendre
HERE=Path(__file__).resolve().parent;QUIET=HERE.parent/'Halo quiet realization 2026-10-21'
sys.path.insert(0,str(QUIET))
from fast_smooth_field import deposit,evaluate,G
from live_quiet_fast import stock_target

def basis(X,lmax):
    r=np.linalg.norm(X,axis=1);mu=X[:,2]/r;phi=np.arctan2(X[:,1],X[:,0]);cols=[];ells=[]
    for l in range(0,lmax+1,2):
        cols.append(lpmv(0,l,mu));ells.append(l)
        for m in range(1,l+1):
            p=math.sqrt(2*math.factorial(l-m)/math.factorial(l+m))*lpmv(m,l,mu)
            cols.extend([p*np.cos(m*phi),p*np.sin(m*phi)]);ells.extend([l,l])
    return np.array(cols).T,np.array(ells)

def assign(r,grid,eps):
    s=np.sqrt(r*r+eps*eps);a=np.log(s/grid[0])/np.log(grid[1]/grid[0]);j=np.floor(a).astype(int);u=a-j
    w=np.array([(1-u)**3/6,(3*u**3-6*u*u+4)/6,(-3*u**3+3*u*u+3*u+1)/6,u**3/6]).T
    assert j.min()>=1 and j.max()+2<len(grid)
    return j-1,w,s

def expanded_nodes(X,mass,grid,eps,lmax=8):
    q,ell=basis(X,lmax);r=np.linalg.norm(X,axis=1);j,w,s=assign(r,grid,eps)
    source=mass[:,None]*q*(r/s)[:,None]**ell;dep=np.zeros((len(grid),len(ell)))
    for a in range(4):np.add.at(dep,j+a,w[:,a,None]*source)
    nodes=np.zeros_like(dep)
    for c,l in enumerate(ell):
        v=dep[:,c]*grid**l;nodes[:,c]=-G*(np.cumsum(v)-.5*v)/grid**(l+1)
        v=dep[:,c]/grid**(l+1);nodes[:,c]+=-G*(np.cumsum(v[::-1])[::-1]-.5*v)*grid**l
    return nodes,ell

def potential(Q,nodes,grid,eps,lmax):
    q,ell=basis(Q,lmax);r=np.linalg.norm(Q,axis=1);j,w,s=assign(r,grid,eps)
    v=sum(w[:,a,None]*nodes[j+a,:len(ell)] for a in range(4))
    return np.sum(q*(r/s)[:,None]**ell*v,axis=1)

def force(Q,nodes,grid,eps,lmax):
    h=np.linalg.norm(Q,axis=1)*1e-5;out=np.zeros_like(Q)
    for k in range(3):
        plus=Q.copy();minus=Q.copy();plus[:,k]+=h;minus[:,k]-=h
        out[:,k]=-(potential(plus,nodes,grid,eps,lmax)-potential(minus,nodes,grid,eps,lmax))/(2*h)
    return out

def check(root,folder,seedfile,label,initial=False):
    d=np.load(root/seedfile);n=len(d['X'])//2;w=2*d['weights'][:n];X=d['X'][:n] if initial else np.load(root/folder/'state_08.0.npz')['X']
    grid=d['grid'];eps=float(d['eps']);_,ms=stock_target();nodes,ell=expanded_nodes(X,ms*w,grid,eps)
    oldnodes=deposit(X,ms*w,grid,eps)
    mu,wm=roots_legendre(12);phi=np.arange(24)*2*np.pi/24;mm,pp=np.meshgrid(mu,phi,indexing='ij')
    dirs=np.c_[np.sqrt(1-mm.ravel()**2)*np.cos(pp.ravel()),np.sqrt(1-mm.ravel()**2)*np.sin(pp.ravel()),mm.ravel()];wa=np.repeat(wm,24)/48
    rms=lambda a:float(np.sqrt(np.sum(wa*np.sum(a*a,axis=1))))
    trans=lambda a:a-np.sum(a*dirs,axis=1)[:,None]*dirs
    rows=[]
    for R in [8.2,10.,20.,40.,60.]:
        Q=R*dirs;aold,_=evaluate(Q,oldnodes,grid,eps,np.zeros(len(Q)))
        aa={l:force(Q,nodes,grid,eps,l) for l in [4,6,8]}
        validation=rms(aa[4]-aold)/rms(aold);assert validation<1e-6,validation
        rows.append({'radius_kpc':R,'l4_implementation_relative_error':validation,
             'l4_to_l6_total_fraction':rms(aa[6]-aa[4])/rms(aa[4]),
             'l4_to_l6_transverse_fraction':rms(trans(aa[6]-aa[4]))/rms(trans(aa[4])),
             'l6_to_l8_total_fraction':rms(aa[8]-aa[6])/rms(aa[6]),
             'l6_to_l8_transverse_fraction':rms(trans(aa[8]-aa[6]))/rms(trans(aa[6]))})
    return {'label':label,'time_Gyr':0 if initial else 8,'rows':rows}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--reference-only',action='store_true');a=p.parse_args()
    old=(QUIET,'live_131072_eps02_dt05_continue8','quiet_seed_131072.npz','Original')
    if a.reference_only:out=[check(*old,initial=True),check(*old)];name='higher_multipole_reference.json'
    else:out=[check(HERE,f'live_seed{s}_8',f'quiet_seed_{s}.npz',f'Replica {i}') for i,s in enumerate([211034,211035],1)];name='higher_multipole_final.json'
    result={'runs':out,'qualification':'Frozen snapshots with the same radial smoothing. Higher modes include finite-particle noise and physical deformation. Small instantaneous increments do not prove long-term trajectory convergence.'}
    assert not (HERE/name).exists();(HERE/name).write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
