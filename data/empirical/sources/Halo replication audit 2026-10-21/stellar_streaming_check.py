"""Check whether reported raw beta hides coherent stellar streaming.

Only one representative of each inversion pair is counted. Fold onto the
northern hemisphere, then estimate local velocity dispersions in 8 and 32
angular cells. This is a coarse-bin diagnostic, not a fitted observational
likelihood or a claim that fine streaming is fully resolved.
"""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import sys,json,argparse
import numpy as np
HERE=Path(__file__).resolve().parent;QUIET=HERE.parent/'Halo quiet realization 2026-10-21'
sys.path.insert(0,str(QUIET))
from analysis_common import load_run

def beta(m):return float(1-(m[1]+m[2])/(2*m[0]))

def diagnose(X,V,low,high):
    r=np.linalg.norm(X,axis=1);ok=(r>=low)&(r<high);X=X[ok].copy();V=V[ok].copy();r=r[ok]
    sign=np.where(X[:,2]<0,-1.,1.);X*=sign[:,None];V*=sign[:,None]
    mu=X[:,2]/r;phi=np.mod(np.arctan2(X[:,1],X[:,0]),2*np.pi);st=np.sqrt(np.maximum(0,1-mu*mu))
    er=X/r[:,None];et=np.c_[mu*np.cos(phi),mu*np.sin(phi),-st]
    ep=np.c_[-np.sin(phi),np.cos(phi),np.zeros(len(phi))]
    vel=np.c_[np.sum(V*er,axis=1),np.sum(V*et,axis=1),np.sum(V*ep,axis=1)]
    raw=np.mean(vel**2,axis=0);out=[]
    for nphi,nmu in [(4,2),(8,4)]:
        nc=nphi*nmu;cell=np.minimum((phi*nphi/(2*np.pi)).astype(int),nphi-1)*nmu+np.minimum((mu*nmu).astype(int),nmu-1)
        num=np.bincount(cell,minlength=nc);summ=np.array([np.bincount(cell,weights=vel[:,i],minlength=nc) for i in range(3)]).T
        sq=np.array([np.bincount(cell,weights=vel[:,i]**2,minlength=nc) for i in range(3)]).T
        sufficient=bool(np.min(num)>=5)
        stream=np.sum(summ*summ/np.maximum(num,1)[:,None],axis=0)/len(X)
        central=np.sum(sq-summ*summ/np.maximum(num,1)[:,None],axis=0)/len(X)
        # A finite-cell count correction is displayed separately; samples are
        # correlated orbit phases, so it is not used for uncertainty estimates.
        corrected=np.sum((sq-summ*summ/np.maximum(num,1)[:,None])*num[:,None]/np.maximum(num-1,1)[:,None],axis=0)/len(X)
        out.append({'angular_cells':nc,'minimum_occupancy':int(num.min()),'adequate_occupancy':sufficient,
            'beta_local_central':beta(central),'beta_count_corrected':beta(corrected),
            'streaming_fraction_of_raw_components':(stream/raw).tolist()})
    return {'radial_cut_kpc':[low,high],'independent_inversion_representatives':len(X),
            'beta_raw':beta(raw),'local_estimates':out}

def check(root,run,seedfile,label,initial=False):
    if root==QUIET:d=load_run(run)
    else:d=json.loads((root/run/'results.json').read_text())
    t=0. if initial else d['rows'][-1]['time']
    if initial:
        sd=np.load(QUIET.parent/'Halo stock director bridge 2026-10-21/stars_seed_8192.npz');n=len(sd['X'])//2
        X=sd['X'][:n].copy();V=sd['V'][:n].copy()
    else:
        ss=np.load(root/run/f'state_{t:04.1f}.npz');normal=ss['L']/np.linalg.norm(ss['L']);J=np.array(d['J0'])
        xx=J-(J@normal)*normal;xx/=np.linalg.norm(xx);B=np.array([xx,np.cross(normal,xx),normal])
        X=ss['Xs']@B.T;V=ss['Vs']@B.T
    return {'label':label,'time_Gyr':t,'cuts':[diagnose(X,V,lo,hi) for lo,hi in [(6,24),(10,20),(10,40)]]}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--initial-only',action='store_true');a=p.parse_args()
    old=(QUIET,'live_131072_eps02_dt05_continue8','quiet_seed_131072.npz','Original')
    initial=check(*old,initial=True)
    if a.initial_only:out={'initial':initial,'old_final':check(*old)};name='stellar_streaming_reference.json'
    else:
        out={'initial':initial,'final':[check(*old)]+[check(HERE,f'live_seed{s}_8',f'quiet_seed_{s}.npz',f'Replica {i}') for i,s in enumerate([211034,211035],1)]}
        assert all(r['time_Gyr']==8 for r in out['final']);name='stellar_streaming_final.json'
    out['qualification']='Coarse spatial-bin streaming subtraction. Counts exclude duplicated inversion partners. No errors or observational likelihood are inferred from these correlated orbit samples.'
    assert not (HERE/name).exists();(HERE/name).write_text(json.dumps(out,indent=2))
    print(json.dumps(out,indent=2))
