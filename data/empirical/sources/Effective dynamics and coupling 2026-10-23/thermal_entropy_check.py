from pathlib import Path
import json,numpy as np,sympy as s
from thermal_interfaces import run
HERE=Path(__file__).resolve().parent
out=HERE/'results/thermal_entropy.json';assert not out.exists()
row,a=run(256)
n,z,g=s.symbols('n z g',positive=True)
eth=z*n**g
checks={'thermal_pressure':s.simplify(n*s.diff(eth,n)-eth-(g-1)*eth),
 'thermal_enthalpy':s.simplify(n*s.diff(eth,n)-g*eth),
 'thermal_sound_numerator':s.simplify(n*s.diff(n*s.diff(eth,n)-eth,n)-g*(g-1)*eth)}
assert all(v==0 for v in checks.values())
assert row['minimum_sampled_entropy_increment']>=-1e-8
out.write_text(json.dumps({'purpose':'Check the entropy direction of the selected thermal closure and its thermodynamic derivatives.',
 'row':row,'symbolic':{k:str(v) for k,v in checks.items()},
 'entropy_density':'e_th^(1/gamma), with its Lorentz factor in the lab density; chosen entropy normalization',
 'roundoff':'Only the diagnostic fractional power uses max(e_th,0); negative inversion errors are retained in the evolved state and reported.'},indent=2),encoding='utf-8')
np.savez_compressed(HERE/'results/thermal_entropy_traces.npz',**a)
