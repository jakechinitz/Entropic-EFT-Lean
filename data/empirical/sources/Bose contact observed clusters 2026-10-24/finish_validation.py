"""Dispatch the last two unchanged validation specifications concurrently."""
from pathlib import Path
import json,subprocess,sys,shutil
from concurrent.futures import ThreadPoolExecutor,as_completed
from datetime import datetime
HERE=Path(__file__).resolve().parent
out=HERE/('validation_finish_'+datetime.now().strftime('%Y%m%d_%H%M%S'));out.mkdir();shutil.copy2(__file__,out/'executed.py')
a=json.loads(next(HERE.glob('shared_scaling_suite_*/allocations.json')).read_text())
jobs=[dict(cluster='ZW1215',k=3,N=4000,seed=2,regspec=a['ZW1215']['shared_specific_work'],dt=.1,softening=2.5,label='shared_resolution'),dict(cluster='A1795',k=3,N=2000,seed=1,regspec=a['A1795']['shared_specific_work'],dt=.05,softening=5,label='shared_timestep')]
(out/'jobs.json').write_text(json.dumps(jobs,indent=2))
def one(j):
    cmd=[sys.executable,str(HERE/'evolve.py'),j['cluster'],'--force','conservative']
    for k,v in j.items():
        if k!='cluster':cmd+=['--'+k,str(v)]
    with (out/f"{j['cluster']}_{j['label']}.log").open('w') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
    return dict(**j,exit_code=r.returncode)
rows=[]
with ThreadPoolExecutor(max_workers=2) as pool:
    for fut in as_completed([pool.submit(one,j) for j in jobs]):
        r=fut.result();rows.append(r);(out/'status.json').write_text(json.dumps(rows,indent=2));print(r,flush=True)
assert all(r['exit_code']==0 for r in rows)
print('REMAINING CHECKS COMPLETE',out,flush=True)
