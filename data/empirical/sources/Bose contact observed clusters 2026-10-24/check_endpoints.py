"""Quadrature check and local-a0 sensitivity; neither is a likelihood."""
from pathlib import Path
import json,numpy as np
from scipy.interpolate import PchipInterpolator
from scipy.integrate import cumulative_trapezoid
HERE=Path(__file__).resolve().parent
G=4.30091e-6;A0=1.2307e-10*3.0857e19/1e6
meta=json.loads((HERE/'inputs/summary.json').read_text());old=json.loads((HERE/'endpoint_energy.json').read_text())['clusters'];res={}
for name,d in meta.items():
    a=np.load(HERE/'inputs'/f'{name}.npz');r0=a['r'];s0=a['stock'];b0=a['b'];M=s0[-1]
    rr=np.geomspace(r0[0],r0[-1],24000)
    b=np.exp(PchipInterpolator(np.log(r0),np.log(b0))(np.log(rr)))
    s=np.exp(PchipInterpolator(np.log(r0),np.log(s0))(np.log(rr)))
    gb=G*b/rr**2;tar=np.minimum(b/np.expm1(np.sqrt(gb/A0)),M)
    pb=-cumulative_trapezoid(gb[::-1],-rr[::-1],initial=0)[::-1]-G*b[-1]/rr[-1]
    r=.5*(rr[:-1]+rr[1:]);bm=.5*(b[:-1]+b[1:]);pm=.5*(pb[:-1]+pb[1:])
    def E(q):
        qm=.5*(q[:-1]+q[1:]);dm=np.diff(q)
        return np.sum((-.5*G*qm/r+.5*G*bm/r+pm)*dm)/M
    change=E(tar)-E(s)
    err=abs(change/old[name]['required_work_specific_km2_s2']-1)
    assert err<.001
    # Use the data reduction's flat Omega_m=.3 cosmology for this small-z check.
    hz=np.sqrt(.3*(1+d['z'])**3+.7)
    mb=d['observed_baryon_M500'];r5=d['R500_kpc'];mt=d['observed_total_M500'];x=np.sqrt(G*mb/r5**2/(A0*hz))
    res[name]=dict(endpoint_grid_refinement_relative_change=err,H_over_H0=hz,RAR_mass_over_HSE_with_a0_z=float(mb*(1+1/np.expm1(x))/mt))
(HERE/'endpoint_checks.json').write_text(json.dumps(res,indent=2));print(json.dumps(res,indent=2))
