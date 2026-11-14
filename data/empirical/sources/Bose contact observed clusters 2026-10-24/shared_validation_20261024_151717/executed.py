"""Prioritize resolution checks on the actual cross-sector work scaling."""
from pathlib import Path
import json,subprocess,sys,shutil,time
from datetime import datetime
HERE=Path(__file__).resolve().parent
out=HERE/('shared_validation_'+datetime.now().strftime('%Y%m%d_%H%M%S'));out.mkdir();shutil.copy2(__file__,out/'executed.py')
allocation=json.loads(next(HERE.glob('shared_scaling_suite_*/allocations.json')).read_text())
jobs=[dict(cluster=c,k=k,N=4000,seed=2,regspec=allocation[c]['shared_specific_work'],dt=.1,softening=2.5,label='shared_resolution') for c in ['A1795','ZW1215'] for k in [0,3]]
jobs += [dict(cluster='A1795',k=3,N=2000,seed=1,regspec=allocation['A1795']['shared_specific_work'],dt=.05,softening=5,label='shared_timestep')]
(out/'jobs.json').write_text(json.dumps(jobs,indent=2))
start=time.time();rows=[]
for j in jobs:
    cmd=[sys.executable,str(HERE/'evolve.py'),j['cluster'],'--force','conservative']
    for key,value in j.items():
        if key!='cluster':cmd+=['--'+key,str(value)]
    with (out/f"{j['cluster']}_k{j['k']}_{j['label']}.log").open('w') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
    row=dict(**j,exit_code=r.returncode);rows.append(row);(out/'status.json').write_text(json.dumps(rows,indent=2));print(row,'elapsed',round(time.time()-start),flush=True)
assert all(r['exit_code']==0 for r in rows)
print('SHARED VALIDATION COMPLETE',out,flush=True)
