"""Apply a published-style common-cut shape residual to all registered runs.

This supplementary diagnostic was added after starting the runs. It cannot
replace the preregistered 10-40 kpc retention outcomes. Values are not p-values.
"""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import sys,json,argparse
import numpy as np
HERE=Path(__file__).resolve().parent;QUIET=HERE.parent/'Halo quiet realization 2026-10-21'
sys.path.insert(0,str(QUIET))
from analysis_common import load_run
ref=json.loads((HERE/'matched_shape_reference.json').read_text())
mean=np.r_[ref['tilt_deg'],ref['mapped_mean_pq']]
sigma=np.r_[ref['tilt_sigma_deg'],ref['mapped_sigma_pq']]

def row(s,t):
    value=np.array([s['tilt'],s['p'],s['q']]);z=(value-mean)/sigma
    return {'end':t,'tilt_p_q':value.tolist(),'standardized_residuals':z.tolist(),
            'sum_squared_standardized_residuals':float(z@z)}

def assess(d,label):
    hist=[row(a['stars']['radial'][5],a['end']) for a in d['half_Gyr_averages']]
    snapshots=[row(a['stars']['radial'][5],a['time']) for a in d['rows']]
    return {'label':label,'end':d['rows'][-1]['time'],'history':hist,'last':hist[-1],
            'instantaneous_snapshots':snapshots,'last_instantaneous':snapshots[-1]}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--reference-only',action='store_true');a=p.parse_args()
    out=[assess(load_run('live_131072_eps02_dt05_continue8'),'Original'),assess(load_run('rigid_quiet_8'),'Prescribed field')]
    if not a.reference_only:
        out += [assess(json.loads((HERE/f'live_seed{s}_8/results.json').read_text()),f'Replica {i}') for i,s in enumerate([211034,211035],1)]
        assert all(x['end']==8 for x in out)
    name='matched_shape_old_with_snapshots.json' if a.reference_only else 'matched_shape_final.json'
    result={'reference':ref,'runs':out,'qualification':'Supplementary 6-60 kpc stellar shape diagnostic. The main retention results remain the registered 10-40 kpc cut. No observational success probability is assigned; finite-tracer noise, shape-systematic uncertainties, noncoplanarity and the full selection function are not modeled.'}
    assert not (HERE/name).exists();(HERE/name).write_text(json.dumps(result,indent=2))
    print(json.dumps([{'label':x['label'],**x['last']} for x in out],indent=2))
