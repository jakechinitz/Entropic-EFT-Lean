"""Independent cluster jobs; every run has its own immutable result directory."""
from pathlib import Path
import subprocess,sys,json,time
from concurrent.futures import ThreadPoolExecutor,as_completed
from datetime import datetime

HERE=Path(__file__).resolve().parent
NAMES=['A1795','A2029','A85','A2142','A2319','A644','ZW1215']
out=HERE/('suite_'+datetime.now().strftime('%Y%m%d_%H%M%S'))
out.mkdir()
jobs=[(c,k) for c in NAMES for k in [0,1,3]]
(out/'jobs.json').write_text(json.dumps(jobs,indent=2))
def one(job):
    c,k=job
    with (out/f'{c}_k{k}.log').open('w') as f:
        cmd=[sys.executable,str(HERE/'evolve.py'),c,'--k',str(k)]
        result=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
    return dict(cluster=c,k=k,exit_code=result.returncode)
if __name__=='__main__':
    rows=[];start=time.time()
    with ThreadPoolExecutor(max_workers=3) as pool:
        futs=[pool.submit(one,j) for j in jobs]
        for fut in as_completed(futs):
            r=fut.result();rows.append(r);print(r,'elapsed',round(time.time()-start),flush=True)
            (out/'status.json').write_text(json.dumps(rows,indent=2))
    assert all(r['exit_code']==0 for r in rows)
    print('SUITE COMPLETE',out,flush=True)
