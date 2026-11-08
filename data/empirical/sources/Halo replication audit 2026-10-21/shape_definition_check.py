"""Distinguish spherical-cut inertia axes from actual density contours."""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['NUMBA_NUM_THREADS']='1'
import sys,json
import numpy as np
from scipy.optimize import brentq
HERE=Path(__file__).resolve().parent;QUIET=HERE.parent/'Halo quiet realization 2026-10-21'
sys.path.insert(0,str(QUIET))
from live_quiet_fast import radial_tables,stock_target,diagnostic
lr,tab,r,rho,mass,meta=radial_tables()
positive=rho>0
def logrho(R):return np.interp(np.log(R),np.log(r[positive]),np.log(rho[positive]))
rows=[]
for R in [6.,10.,20.,30.,40.,60.]:
    rm=brentq(lambda x:logrho(x)+np.log(.85)-logrho(R)-np.log(1.3),.01*R,R)
    rows.append({'major_axis_radius_kpc':R,'minor_axis_radius_kpc':float(rm),
                 'isodensity_axis_ratio':float(rm/R)})
tar,ms=stock_target();diag=diagnostic(tar,tar)
result={'analytic_density_contours':rows,
        'spherical_cut_position_inertia_ratios':diag['radial'][4],
        'qualification':'The A=0.3 density has prolate angular structure. These iso-density intercept ratios are not a global ellipsoid fit, a potential flattening, or the final evolved density. The simulation inertia ratio must not be compared directly with a published density-axis parameter.'}
assert not (HERE/'shape_definition_check.json').exists()
(HERE/'shape_definition_check.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
