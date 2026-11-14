"""Unfitted future phases: force noise and moment residuals in fixed field."""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['NUMBA_NUM_THREADS']='1'
import sys,json,argparse,time
HERE=Path(__file__).resolve().parent;QUIET=HERE.parent/'Halo quiet realization 2026-10-21'
sys.path.insert(0,str(QUIET))
from quiet_fit import diagnostics
from live_quiet_fast import rigid_advance,radial_tables,stock_target,TU
from numba import set_num_threads
import numpy as np
set_num_threads(1)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--seed',type=int,choices=[211034,211035],required=True);a=p.parse_args()
    path=HERE/f'temporal_diagnostics_{a.seed}.json';assert not path.exists()
    d=np.load(HERE/f'quiet_seed_{a.seed}.npz');n=len(d['X'])//2;X=d['X'][:n].copy();V=d['V'][:n].copy()
    w=2*d['weights'][:n];prior=2*d['prior'][:n];om=float(d['Omega']);grid=d['grid'];eps=float(d['eps'])
    lr,tab,*_=radial_tables();_,ms=stock_target();last=0.;rows=[];start=time.time()
    for t in [0.,.025,.1,.25,.5,1.]:
        if t:rigid_advance(X,V,(t-last)/TU,om,lr,tab)
        row={'time_Gyr':t,'quiet':diagnostics(X,V,w,grid,eps,om,ms),
             'prior':diagnostics(X,V,prior,grid,eps,om,ms)}
        rows.append(row);last=t
        path.write_text(json.dumps({'seed':a.seed,'rows':rows,'seconds':time.time()-start,
            'qualification':'Prescribed-field transport of frozen phase weights. These future times were not used to select phases or fit weights; they are not live trajectories.'},indent=2))
        print(a.seed,t,max(r['transverse_force_error'] for r in row['quiet']['force_errors']),flush=True)
    np.savez_compressed(HERE/f'rigid_phases_1Gyr_{a.seed}.npz',X=X,V=V,weights=w)
