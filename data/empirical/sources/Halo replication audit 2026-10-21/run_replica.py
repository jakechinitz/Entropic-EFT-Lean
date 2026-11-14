"""Fixed preregistered phases -> unchanged quiet fit -> gated eight-Gyr run."""
from pathlib import Path
import argparse, json, subprocess, sys, time
import numpy as np

here = Path(__file__).resolve().parent
p = argparse.ArgumentParser()
p.add_argument('--seed', type=int, choices=[211034, 211035], required=True)
a = p.parse_args()
suffix = f'_{a.seed}'
log = here / f'replica_{a.seed}.log'
assert not log.exists(), 'Preserve prior outputs.'
start = time.time()
with log.open('x', encoding='utf-8', buffering=1) as out:
    def stage(name, *args):
        command = [sys.executable, str(here/'run_stage.py'), name, *map(str,args)]
        out.write('COMMAND '+repr(command)+'\n'); out.flush()
        subprocess.run(command, stdout=out, stderr=subprocess.STDOUT, check=True)
    stage('seed_exact.py', '--base', 65536, '--minimum', 24,
          '--suffix', suffix, '--seed', a.seed)
    stage('quiet_fit.py', '--suffix', suffix)
    fit = json.loads((here/f'quiet_fit{suffix}.json').read_text())
    bank = np.load(here/f'phase_bank{suffix}.npz')
    sd = np.load(here/f'quiet_seed{suffix}.npz')
    after = fit['after']
    gates = {
        'positive_masses': bool(np.min(sd['weights']) > 0),
        'orbit_mass': fit['orbit_mass_error'] < 1e-12,
        'phase_fit': fit['max_scaled_row_residual'] < 1e-6,
        'total_force': max(r['total_force_error'] for r in after['force_errors']) <= .02,
        'transverse_force': max(r['transverse_force_error'] for r in after['force_errors']) <= .1,
        'torque_x': abs(after['torque_over_required'][0]) <= .05,
        'torque_y': abs(after['torque_over_required'][1]-1) <= .05,
        'J_direction': after['J_direction_error_deg'] <= 1,
        'phase_Jacobi': float(np.max(bank['errors'])) < .002,
        'count': len(sd['weights']) == 131072,
    }
    gate = {'seed':a.seed, 'gates':gates, 'passed':all(gates.values()),
            'seconds_to_initial_gate':time.time()-start}
    (here/f'initial_gate{suffix}.json').write_text(json.dumps(gate,indent=2))
    out.write(json.dumps(gate)+'\n'); out.flush()
    if not gate['passed']:
        raise RuntimeError('Initial numerical gate failed; seed preserved without replacement.')
    stage('live_quiet_fast.py', '--tag', f'live_seed{a.seed}_8',
          '--seed', f'quiet_seed{suffix}.npz', '--time', 8, '--eps', .2, '--dt', .0005)
    out.write(f'REPLICA COMPLETE, seconds={time.time()-start}\n')
print(f'Replica {a.seed} completed; see {log}', flush=True)
