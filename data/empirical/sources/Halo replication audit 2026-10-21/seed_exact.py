"""Positive variable-mass phases, preserving the strengthened orbit totals."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
os.environ['NUMBA_NUM_THREADS']='4'
from pathlib import Path
import sys,json,time
HERE=Path(__file__).resolve().parent
BRIDGE=HERE.parent/'Halo stock director bridge 2026-10-21'
sys.path.insert(0,str(BRIDGE))
from weak_endpoints import *
HERE=Path(__file__).resolve().parent

@njit(parallel=True,cache=True)
def exact_phases(X,V,offsets,ticks,lr,tab,om):
    out=np.zeros((len(ticks),6));errs=np.zeros(len(X))
    ct=np.cos(43*np.pi/180);st=np.sin(43*np.pi/180)
    for i in prange(len(X)):
        x,y,z=X[i];vx,vy,vz=V[i];t=0.;j=offsets[i]
        e0=.5*(vx*vx+vy*vy+vz*vz)+potential(x,y,z,.3,ct,st,lr,tab)-om*(y*vz-z*vy)
        for m in range(1,ticks[offsets[i+1]-1]+1):
            end=m*.005/TU
            while t<end-1e-14:
                ax,ay,az=field(x,y,z,.3,ct,st,lr,tab)
                r=np.sqrt(x*x+y*y+z*z);v=np.sqrt(vx*vx+vy*vy+vz*vz);ac=np.sqrt(ax*ax+ay*ay+az*az)
                dt=min(.00025/TU,.025*r/max(v+om*r,1.),.025*np.sqrt(r/max(ac,1.)),end-t)
                x,y,z=rotate(x,y,z,1.,0.,-.5*om*dt);vx,vy,vz=rotate(vx,vy,vz,1.,0.,-.5*om*dt)
                ax,ay,az=field(x,y,z,.3,ct,st,lr,tab)
                vx+=.5*dt*ax;vy+=.5*dt*ay;vz+=.5*dt*az
                x+=dt*vx;y+=dt*vy;z+=dt*vz
                ax,ay,az=field(x,y,z,.3,ct,st,lr,tab)
                vx+=.5*dt*ax;vy+=.5*dt*ay;vz+=.5*dt*az
                x,y,z=rotate(x,y,z,1.,0.,-.5*om*dt);vx,vy,vz=rotate(vx,vy,vz,1.,0.,-.5*om*dt);t+=dt
            while j<offsets[i+1] and ticks[j]==m:
                out[j]=np.array([x,y,z,vx,vy,vz])
                ee=.5*(vx*vx+vy*vy+vz*vz)+potential(x,y,z,.3,ct,st,lr,tab)-om*(y*vz-z*vy)
                errs[i]=max(errs[i],abs(ee-e0)/max(abs(e0),1000.));j+=1
    return out,errs

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--base',type=int,default=32768);ap.add_argument('--suffix',default='');ap.add_argument('--minimum',type=int,default=12);ap.add_argument('--seed',type=int,default=211031);args=ap.parse_args()
    assert not (HERE/f'phase_bank{args.suffix}.npz').exists(),'Preserve the existing bank; use a new suffix.'
    start=time.time();wd=np.load(BRIDGE/'weak_stationarity_weights.npz')
    sel=wd['weights']>0;ids=wd['indices'][sel];w=wd['weights'][sel];w/=w.sum()
    n=args.base;minimum=args.minimum;raw=(n-minimum*len(w))*w;count=minimum+np.floor(raw).astype(int)
    count[np.argsort(-(raw-np.floor(raw)))[:n-count.sum()]]+=1
    offsets=np.r_[0,np.cumsum(count)];rng=np.random.default_rng(args.seed)
    ticks=np.concatenate([np.ceil(9600*(np.arange(k)+rng.random(k))/k).astype(np.int64) for k in count])
    lib=np.load(PREV/'precession_extension_stock/library.npz');lr,tab,*_=radial_tables()
    om=json.loads((PREV/'precession_validation/results.json').read_text())['Omega_internal'][0]
    print('Integrating exact phases for',len(ids),'orbits;',n,'base points',flush=True)
    points,errors=exact_phases(lib['X'][ids],lib['V'][ids],offsets,ticks,lr,tab,om)
    prior=np.repeat(w/count,count);group=np.repeat(np.arange(len(w)),count)
    np.savez_compressed(HERE/f'phase_bank{args.suffix}.npz',X=points[:,:3],V=points[:,3:],prior=prior,
        group=group,orbit_indices=ids,orbit_weights=w,offsets=offsets,ticks=ticks,errors=errors,Omega=om)
    result={'base_points':n,'paired_particles':2*n,'orbits':len(w),'minimum_phases':int(count.min()),
        'orbit_mass_error':float(np.max(abs(np.bincount(group,weights=prior)-w))),
        'effective_paired_particles':float(2/np.sum(prior**2)),
        'jacobi_error_quantiles':np.quantile(errors,[.5,.9,.99,1]).tolist(),'seconds':time.time()-start}
    result['settings']=vars(args)
    (HERE/f'phase_bank{args.suffix}.json').write_text(json.dumps(result,indent=2));print(json.dumps(result),flush=True)
