"""Refined gravity tests, preserving the original contact acceptance kernel."""
from pathlib import Path
import subprocess,sys,json,time,shutil
from concurrent.futures import ThreadPoolExecutor,as_completed
from datetime import datetime
HERE=Path(__file__).resolve().parent
out=HERE/('refined_suite_'+datetime.now().strftime('%Y%m%d_%H%M%S'));out.mkdir()
shutil.copy2(__file__,out/'executed.py')
names=['A1795','ZW1215','A2029','A85','A2142','A2319','A644']
jobs=[dict(cluster=c,k=k,N=2000,seed=1,regspec=15000,label='refined') for c in names for k in [0,1,3]]
# Exhaustion was found in the first pilot. The larger reservoir is a common,
# untuned sensitivity, not a preferred work capacity or extra cluster fit.
jobs += [dict(cluster=c,k=3,N=2000,seed=1,regspec=150000,label='reservoir_sensitivity') for c in ['A1795','ZW1215']]
# Resolve radial population noise in the first cluster and the largest RAR deficit.
jobs += [dict(cluster=c,k=k,N=8000,seed=2,regspec=15000,label='resolution_seed_check') for c in ['A1795','ZW1215'] for k in [0,3]]
(out/'jobs.json').write_text(json.dumps(jobs,indent=2))
def one(job):
    cmd=[sys.executable,str(HERE/'evolve.py'),job['cluster'],'--dt','0.1','--force','conservative']
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
    print('REFINED SUITE COMPLETE',out,flush=True)
