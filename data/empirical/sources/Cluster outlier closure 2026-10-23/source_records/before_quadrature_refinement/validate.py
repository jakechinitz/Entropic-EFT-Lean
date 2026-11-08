"""Independent numerical checks, including units and pressure integration."""
from pathlib import Path
import json, hashlib, sys
import numpy as np
from scipy.integrate import cumulative_trapezoid
HERE=Path(__file__).resolve().parent
PREV=HERE.parent/'Observed cluster tests 2026-10-23'
report=json.loads((HERE/'results/audit.json').read_text())
checks=dict(report['checks'])
for c in ['A1795','A2029']:
    a=np.genfromtxt(HERE/'results'/f'{c}_pressure.csv',delimiter=',',names=True)
    r=a['r_kpc'];n=a['ne_cm3'];m=a['M_lensing_target_Msun']-a['M_thermal_Msun']
    # SI evaluation: integral rho*g*dr / Pthermal; mu_e cancels.
    # Electron-equivalent pressure = mu*m_p integral ne*g*dr.
    Gsi=6.67430e-11;Msun=1.988409870698051e30;kpc=3.085677581491367e19
    integrand=.6*1.67262192595e-27*(n*1e6)*Gsi*(m*Msun)/(r*kpc)**2*kpc
    forward=cumulative_trapezoid(integrand,r,initial=0)
    J=forward[-1]-forward;minimal=J-min(0,float(J.min()))
    denominator=a['Pe_HSE_consistent_keV_cm3']*1.602176634e-16*1e6
    q=minimal/denominator
    stored=a['minimum_nonthermal_to_thermal_pressure']
    checks[c+'_SI_pressure_units']=bool(np.max(abs(q-stored))<2e-7)
    # Saved dense grid: every second point provides an independent resolution check.
    f2=cumulative_trapezoid(integrand[::2],r[::2],initial=0);J2=f2[-1]-f2
    q2=(J2-min(0,float(J2.min())))/denominator[::2]
    checks[c+'_quadrature_resolution']=bool(np.max(abs(q2-q[::2]))<2e-6)
    # An exactly integrable analytic fixture for the same integral direction.
    x=np.linspace(1,2,10001);forward=cumulative_trapezoid(x**-3,x,initial=0)
    checks['analytic_integral_direction']=bool(np.max(abs(forward-(1-x**-2)/2))<1e-8)

files=list((HERE/'results').glob('*_transport.npz'))
for p in files:
    with np.load(p) as d:
        T=d['transport'];s=d['source_baryon'];b=d['destination_baryon']
        assert np.all(T>=0) and np.all(s>=0) and np.all(b>=0)
        assert np.allclose(T.sum(1),s,rtol=1e-11,atol=.1)
        assert np.allclose(T.sum(0),b,rtol=1e-11,atol=.1)
checks['twelve_saved_transport_maps']=len(files)==12
lean=json.loads(sorted((HERE/'results').glob('lean_*.json'))[-1].read_text())
checks['lean_compiled_without_sorry']=lean['success'] and not lean['contains_sorry'] and not lean['contains_sorryAx']
manifest=[]
for c in ['A1795','A2029','A644','ZW1215','A2319','A2142','A85']:
    for suffix in ['hydro_mass','fgas_profile','mstar','density_L1','pressure']:
        p=PREV/'source_data/xcop'/c/(c+'_'+suffix+'.fits')
        if p.exists(): manifest.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
for p in [PREV/'radial_analysis.py',PREV/'source_data/lensing_table_A2.json',HERE/'formalization/ClusterOutliers.lean']:
    manifest.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
(HERE/'source_records/input_hashes.json').write_text(json.dumps(manifest,indent=2),encoding='utf-8')
out={'passed':all(checks.values()),'checks':checks,'transport_maps':len(files),'lean_theorems':lean['theorems']}
(HERE/'results/validation.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
print(json.dumps(out,indent=2))
assert out['passed']
