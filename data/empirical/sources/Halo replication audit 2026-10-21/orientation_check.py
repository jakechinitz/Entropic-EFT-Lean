"""Check the third orientation degree of freedom omitted by tilt alone."""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import sys,json,argparse
import numpy as np
HERE=Path(__file__).resolve().parent;QUIET=HERE.parent/'Halo quiet realization 2026-10-21'
sys.path.insert(0,str(QUIET))
from analysis_common import load_run
ref=json.loads((HERE/'matched_shape_reference.json').read_text())

def check(root,folder,label):
    d=load_run(folder) if root==QUIET else json.loads((root/folder/'results.json').read_text())
    ss=np.load(root/folder/'state_08.0.npz');n=ss['L']/np.linalg.norm(ss['L']);J=np.array(d['J0'])
    xx=J-(J@n)*n;xx/=np.linalg.norm(xx);B=np.array([xx,np.cross(n,xx),n]);X=ss['Xs']@B.T
    r=np.linalg.norm(X,axis=1);X=X[(r>=6)&(r<60)];ev,e=np.linalg.eigh(X.T@X/len(X))
    major=e[:,-1];major*=1 if major[2]>=0 else -1
    alpha=np.arctan2(major[1],major[0]);c=np.cos(alpha);s=np.sin(alpha)
    R=np.array([[c,s,0],[-s,c,0],[0,0,1]])
    minor=R@e[:,0];minor*=1 if minor[2]>=0 else -1
    target=np.array([-np.sin(np.radians(ref['tilt_deg'])),0.,np.cos(np.radians(ref['tilt_deg']))])
    angle=np.degrees(np.arccos(np.clip(minor@target,-1,1)))
    pq=np.sqrt(ev[[1,0]]/ev[2]);z=(pq-ref['mapped_mean_pq'])/ref['mapped_sigma_pq']
    return {'label':label,'time_Gyr':8,'independent_pair_representatives':len(X),
       'major_tilt_deg':float(np.degrees(np.arcsin(major[2]))),
       'minor_axis_angle_to_target_after_major_azimuth_alignment_deg':float(angle),
       'intermediate_axis_elevation_deg':float(np.degrees(np.arcsin(abs(e[2,1])))),
       'tilt_only_D':float(((np.degrees(np.arcsin(major[2]))-ref['tilt_deg'])/ref['tilt_sigma_deg'])**2+z@z),
       'orientation_sensitive_D':float((angle/ref['tilt_sigma_deg'])**2+z@z),
       'minor_axis_after_azimuth_alignment':minor.tolist(),'pq':pq.tolist()}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--reference-only',action='store_true');a=p.parse_args()
    out=[check(QUIET,'live_131072_eps02_dt05_continue8','Original')]
    if not a.reference_only:out += [check(HERE,f'live_seed{s}_8',f'Replica {i}') for i,s in enumerate([211034,211035],1)]
    result={'runs':out,'qualification':'Final instantaneous snapshot, 6-60 kpc. Overall azimuth is aligned to the stellar major axis because the disk model is axisymmetric. The minor-axis angle additionally sees departure from coplanarity. D remains a summary diagnostic, not a calibrated observational probability.'}
    name='orientation_reference.json' if a.reference_only else 'orientation_final.json'
    assert not (HERE/name).exists();(HERE/name).write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
