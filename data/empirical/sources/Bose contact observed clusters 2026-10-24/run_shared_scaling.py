"""Test the dimensionless work scaling actually common to Claude's galaxy runs.

The initial small-reserve suite reused the Milky Way's dimensional allowance.
Inspection establishes D/Vf^2 = 0.447, 0.452, 0.450 in the three galaxy cases.
This suite applies D=0.45*sqrt(G*M_b,total*a0) without per-cluster adjustment.
M_b,total is the finite completed baryon profile's limit, explicitly assumed.
"""
from pathlib import Path
import subprocess,sys,json,time,shutil
from concurrent.futures import ThreadPoolExecutor,as_completed
from datetime import datetime
import numpy as np
HERE=Path(__file__).resolve().parent
out=HERE/('shared_scaling_suite_'+datetime.now().strftime('%Y%m%d_%H%M%S'));out.mkdir()
shutil.copy2(__file__,out/'executed.py')
meta=json.loads((HERE/'inputs/summary.json').read_text());G=4.30091e-6;A0=1.2307e-10*3.0857e19/1e6
jobs=[];allocations={}
for name,d in meta.items():
    a=np.load(HERE/'inputs'/f'{name}.npz');btot=a['observed_b'][-1]*(1+d['completion']['outer_added_mass_over_join_mass'])
    supply=.45*np.sqrt(G*btot*A0)
    lower=.45*np.sqrt(G*d['observed_baryon_M500']*A0)
    allocations[name]=dict(completed_baryon_total_Msun=float(btot),shared_specific_work=float(supply),specific_work_using_only_R500_baryons=float(lower))
    for k in [1,3]:
        jobs.append(dict(cluster=name,k=k,N=2000,seed=1,regspec=float(supply),dt=.1,softening=5,label='shared_scaling'))
(out/'allocations.json').write_text(json.dumps(allocations,indent=2))
(out/'jobs.json').write_text(json.dumps(jobs,indent=2))
def one(job):
    cmd=[sys.executable,str(HERE/'evolve.py'),job['cluster'],'--force','conservative']
    for key,value in job.items():
        if key!='cluster':cmd+=['--'+key,str(value)]
    with (out/f"{job['cluster']}_k{job['k']}.log").open('w') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
    return dict(**job,exit_code=r.returncode)
if __name__=='__main__':
    rows=[];start=time.time()
    with ThreadPoolExecutor(max_workers=3) as pool:
        for fut in as_completed([pool.submit(one,j) for j in jobs]):
            row=fut.result();rows.append(row);print(row,'elapsed',round(time.time()-start),flush=True)
            (out/'status.json').write_text(json.dumps(rows,indent=2))
    assert all(r['exit_code']==0 for r in rows)
    print('SHARED SCALING COMPLETE',out,flush=True)
