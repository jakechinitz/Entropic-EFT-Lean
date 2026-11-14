"""Await the current jobs, then calculate registered and supplementary outputs."""
from pathlib import Path
import subprocess,sys,time,json
from concurrent.futures import ThreadPoolExecutor
HERE=Path(__file__).resolve().parent
logs=[HERE/f'replica_{s}.log' for s in [211034,211035]]
while not all('REPLICA COMPLETE' in p.read_text() for p in logs):
    if any('Traceback (most recent call last)' in p.read_text() for p in logs):
        raise RuntimeError('A replica stopped with an error; preserve and inspect its log.')
    time.sleep(10)
print('Both registered replicas completed. Starting final diagnostics.',flush=True)
jobs=['analyze_replicas.py','stellar_streaming_check.py','matched_shape_assessment.py',
      'reconstructed_density_check.py','disk_torque_profile.py','higher_multipole_check.py']
def run(name):
    with (HERE/(name+'.final.log')).open('x',encoding='utf-8') as out:
        r=subprocess.run([sys.executable,str(HERE/name)],stdout=out,stderr=subprocess.STDOUT)
    return {'script':name,'returncode':r.returncode}
with ThreadPoolExecutor(max_workers=2) as pool:results=list(pool.map(run,jobs))
(HERE/'final_calculation_status.json').write_text(json.dumps(results,indent=2))
assert all(r['returncode']==0 for r in results),results
subprocess.run([sys.executable,str(HERE/'plot_additional.py')],check=True)
print('All final calculations and scientific figures completed.',flush=True)
