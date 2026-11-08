"""Necessary mechanical energy to reach the finite-stock RAR endpoint.

For an isolated spherical stationary stock with no boundary pressure,
2K=G int (M_s+M_b)/r dM_s. Thus E=K+W_self+W_b.
Anisotropy does not change the scalar virial identity. This is an endpoint
requirement, not an existence proof, dynamical path barrier, or core bound.
"""
from pathlib import Path
import numpy as np,json
from scipy.integrate import cumulative_trapezoid
HERE=Path(__file__).resolve().parent
G=4.30091e-6;A0=1.2307e-10*3.0857e19/1e6

def main():
    meta=json.loads((HERE/'inputs/summary.json').read_text());rows={}
    for name in meta:
        a=np.load(HERE/'inputs'/f'{name}.npz');r=a['r'];b=a['b'];initial=a['stock'];M=initial[-1]
        gb=G*b/r**2;target=b/np.expm1(np.sqrt(gb/A0))
        assert np.all(np.diff(target)>0)
        final=np.minimum(target,M);assert final[-1]==M
        phib=-cumulative_trapezoid(gb[::-1],-r[::-1],initial=0)[::-1]-G*b[-1]/r[-1]
        def energy(s):
            # Unresolved inner mass is negligible; midpoints agree to grid order.
            dm=np.diff(s);rm=.5*(r[:-1]+r[1:]);sm=.5*(s[:-1]+s[1:]);bm=.5*(b[:-1]+b[1:]);pm=.5*(phib[:-1]+phib[1:])
            K=.5*G*np.sum((sm+bm)/rm*dm)
            Wself=-G*np.sum(sm/rm*dm);Wb=np.sum(pm*dm)
            return (K+Wself+Wb)/M
        e0=energy(initial);e1=energy(final);diff=e1-e0
        v2=G*meta[name]['observed_total_M500']/meta[name]['R500_kpc']
        rows[name]=dict(initial_stationary_energy_specific=e0,target_stationary_energy_specific=e1,required_work_specific_km2_s2=diff,
                       required_work_over_small_reserve=diff/15000,required_work_over_large_reserve=diff/150000,
                       small_reserve_over_V500_squared=15000/v2,target_stock_edge_kpc=float(r[np.argmax(final==M)]))
    result=dict(scope='Conditional isolated stationary endpoints; fixed completed baryons, finite stock, no escaped particles, no bath energy or other supply. Necessary ledger requirement only. Does not bound internal rearrangement or partial depletion, and does not prove equilibrium DF existence.',clusters=rows)
    p=HERE/'endpoint_energy.json';p.write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))

if __name__=='__main__':main()
