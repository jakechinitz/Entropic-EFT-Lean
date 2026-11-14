"""Torque on thin test rings: diagnose what the rigid-disk closure omits.

The ring rate is n cross tau / (R vc), with vc a radial-force proxy.
This is an uncoupled-ring initial tendency, not a warp solution. Disk
self-gravity, velocity stress and bending communication are not included.
"""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['NUMBA_NUM_THREADS']='1'
import sys,json,argparse
import numpy as np
HERE=Path(__file__).resolve().parent;QUIET=HERE.parent/'Halo quiet realization 2026-10-21'
sys.path.insert(0,str(QUIET))
from fast_smooth_field import deposit,evaluate
from live_quiet_fast import baryon,stock_target,MD,AD,TU
from fast_external import accel
from analysis_common import load_run

def check(root,run,seed,label,initial=False):
    d=load_run(run) if root==QUIET else json.loads((root/run/'results.json').read_text())
    sd=np.load(root/seed);n=len(sd['X'])//2;w=2*sd['weights'][:n];_,ms=stock_target()
    if initial:X=sd['X'][:n];L=MD*2*AD*220
    else:
        ss=np.load(root/run/'state_08.0.npz');normal=ss['L']/np.linalg.norm(ss['L']);J=np.array(d['J0'])
        xx=J-(J@normal)*normal;xx/=np.linalg.norm(xx);B=np.array([xx,np.cross(normal,xx),normal]);X=ss['X']@B.T;L=np.linalg.norm(ss['L'])
    nodes=deposit(X,w*ms,sd['grid'],float(sd['eps']));_,taustock=baryon(X,w*ms,np.array([0.,0.,1.]))
    bulk=np.cross(np.array([0.,0.,1.]),-taustock)/L/TU
    phi=np.arange(144)*2*np.pi/144;directions=np.c_[np.cos(phi),np.sin(phi),np.zeros(len(phi))];rows=[]
    for R in [2.,4.,6.,8.2,10.,15.,20.]:
        Q=R*directions;astock,_=evaluate(Q,nodes,sd['grid'],float(sd['eps']),np.zeros(len(Q)))
        total=astock+np.array([accel(*x,0.,0.,1.) for x in Q]);vc=np.sqrt(np.mean(-R*np.sum(total*directions,axis=1)))
        tau=np.cross(Q,astock).mean(0);rate=np.cross(np.array([0.,0.,1.]),tau)/(R*vc)/TU
        rows.append({'radius_kpc':R,'vc_proxy_kms':float(vc),'ring_rate_vector_rad_Gyr':rate.tolist(),
                     'ring_rate_magnitude_rad_Gyr':float(np.linalg.norm(rate)),
                     'rate_difference_from_rigid_bulk_rad_Gyr':float(np.linalg.norm(rate-bulk))})
    return {'label':label,'time_Gyr':0 if initial else 8,'bulk_rate_vector_rad_Gyr':bulk.tolist(),'rings':rows}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--reference-only',action='store_true');a=p.parse_args()
    old=(QUIET,'live_131072_eps02_dt05_continue8','quiet_seed_131072.npz','Original')
    if a.reference_only:out=[check(*old,initial=True),check(*old)];name='disk_torque_reference.json'
    else:out=[check(HERE,f'live_seed{s}_8',f'quiet_seed_{s}.npz',f'Replica {i}') for i,s in enumerate([211034,211035],1)];name='disk_torque_final.json'
    result={'runs':out,'qualification':'Uncoupled thin test-ring tendency. No live disk, warp amplitude, instability rate or observational exclusion is inferred.'}
    assert not (HERE/name).exists();(HERE/name).write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
