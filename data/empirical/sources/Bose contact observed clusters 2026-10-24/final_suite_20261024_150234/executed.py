"""Conservative, regularized cluster runs and declared sensitivity checks."""
from pathlib import Path
import subprocess,sys,json,time,shutil
from concurrent.futures import ThreadPoolExecutor,as_completed
from datetime import datetime
HERE=Path(__file__).resolve().parent
out=HERE/('final_suite_'+datetime.now().strftime('%Y%m%d_%H%M%S'));out.mkdir()
shutil.copy2(__file__,out/'executed.py')
names=['A1795','ZW1215','A2029','A85','A2142','A2319','A644']
base=dict(N=2000,seed=1,regspec=15000,dt=.1,softening=5)
jobs=[dict(base,cluster=c,k=k,label='final') for c in names for k in [0,1,3]]
jobs += [dict(base,cluster=c,k=3,regspec=150000,label='final_reservoir') for c in ['A1795','ZW1215']]
jobs += [dict(base,cluster=c,k=k,N=8000,seed=2,softening=2.5,label='final_resolution') for c in ['A1795','ZW1215'] for k in [0,3]]
jobs += [dict(base,cluster='A1795',k=3,dt=.05,label='final_timestep')]
(out/'jobs.json').write_text(json.dumps(jobs,indent=2))
def one(job):
    cmd=[sys.executable,str(HERE/'evolve.py'),job['cluster'],'--force','conservative']
    for key,value in job.items():
        if key!='cluster':cmd += ['--'+key,str(value)]
    name=f"{job['cluster']}_k{job['k']}_{job['label']}"
    with (out/(name+'.log')).open('w') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
    return dict(**job,exit_code=r.returncode)
if __name__=='__main__':
    rows=[];start=time.time()
    with ThreadPoolExecutor(max_workers=3) as pool:
        for fut in as_completed([pool.submit(one,j) for j in jobs]):
            row=fut.result();rows.append(row);print(row,'elapsed',round(time.time()-start),flush=True)
            (out/'status.json').write_text(json.dumps(rows,indent=2))
    assert all(r['exit_code']==0 for r in rows)
    print('FINAL SUITE COMPLETE',out,flush=True)
