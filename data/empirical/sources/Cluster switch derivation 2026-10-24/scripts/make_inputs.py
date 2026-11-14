"""Reproduce support_radii.json, cell_energy_clusters.json, sim/carriers.json, sim/carriers3d.json
and the galaxy reservoir table. Usage: python3 make_inputs.py XCOP_DIR GALAXY_CODE_DIR
XCOP_DIR = '02 Research/Observed cluster tests 2026-10-23' (radial_analysis.py + source_data/xcop)
GALAXY_CODE_DIR = folder with static_analysis.py (Galaxy sector resolution 2026-10-24)."""
import sys, json, math
import numpy as np
from scipy.optimize import brentq
sys.path.insert(0, sys.argv[1]); sys.path.insert(0, sys.argv[2])
import radial_analysis as obs, static_analysis as S
G = 4.30091e-6; A0 = 1.2307e-10*3.0857e19/1e6
inp = json.load(open('sim/inputs/summary.json'))
def cell_energy(r, M):           # integral of N Theta x n* over the support, M = record mass profile
    gb = G*M/r**2; x = np.sqrt(gb/A0); ns = 1/np.expm1(x)
    return np.trapezoid(gb**2*ns*(1+ns)/(4*math.pi*G)*x*ns*4*math.pi*r**2, r)
sr, ce, car, car3 = {}, {}, {}, {}
for c in ['A85','A1795','A2029','A2142','A2319','A644','ZW1215']:
    hd, ma, ga, rg, st = obs.profile(c); r5 = float(hd['R500'])
    mg = obs.interp(rg, ga['MGAS']); s3 = lambda r: obs.stellar(st, r, r5); sp = obs.interp(st['RADIUS'], st['MSTAR'])
    lo = max(30.5, rg.min()+0.5)
    rd3 = brentq(lambda r: s3(r)-mg(r), lo, 500); rdp = brentq(lambda r: sp(r)-mg(r), lo, 500)
    sr[c] = dict(R500=r5, rd_3D=rd3, rd_proj=rdp, Mstar_rd=float(s3(rd3)), fstar_R500=float(s3(r5)/(s3(r5)+mg(r5))))
    rmin = st['RADIUS'].min()
    r = np.geomspace(rmin, rdp, 4000); M = sp(r); E = cell_energy(r, M)
    ce[c] = dict(rd=rdp, Ecell=E, per_total_stock=E/inp[c]['total_stock_Msun'])
    r = np.geomspace(0.5, rdp, 2000); rc = np.clip(r, rmin, None)
    Mp = np.where(r < rmin, sp(rc)*(r/rmin)**2, sp(rc)); M3 = np.where(r < rmin, s3(rc)*(r/rmin)**2, s3(rc))
    x = np.sqrt(G*Mp/r**2/A0); MP = Mp*(1+1/np.expm1(x)); gP = G*MP/r**2
    phi = -np.r_[np.cumsum((0.5*(gP[1:]+gP[:-1])*np.diff(r))[::-1])[::-1], 0] - G*MP[-1]/rdp
    car[c] = dict(rd=rdp, r=r.tolist(), phi=phi.tolist(), Mrec=Mp.tolist())     # law-potential binding (superseded)
    car3[c] = dict(rd=rdp, r=r.tolist(), Mrec3=np.nan_to_num(M3).tolist())     # self-consistent binding input
json.dump(sr, open('support_radii.json','w'), indent=1); json.dump(ce, open('cell_energy_clusters.json','w'), indent=1)
json.dump(car, open('sim/carriers.json','w')); json.dump(car3, open('sim/carriers3d.json','w'))
print('galaxy reservoirs E_cell/(M_stock Vf^2) to the budget edge:')
for case in ['MW','dwarf','massive_spiral','massive_spiral_heavy']:
    b = S.BENCH[case]; Mbf = S.Mb_of(b['parts']); Mbt = sum(p[1] for p in b['parts'])
    M200 = b.get('M200') or S.moster_M200(Mbt); cc, r200, rs, rhos = S.nfw_params(M200, b.get('dc', 0.0))
    Mstock = 0.84*M200; Vf2 = math.sqrt(G*Mbt*A0)
    r = np.geomspace(1e-2, 3*r200, 20000); gb = G*Mbf(r)/r**2; x = np.sqrt(gb/A0); ns = 1/np.expm1(x)
    Rcap = r[np.argmax(r**2*ns*gb/G >= Mstock)]      # budget edge: law stock reaches the budget
    dom = r <= Rcap; u = gb**2*ns*(1+ns)/(4*math.pi*G)*x*ns
    print(case, round(np.trapezoid((u*4*math.pi*r**2)[dom], r[dom])/(Mstock*Vf2), 3), 'R_cap', round(Rcap))
