"""Galaxy safety under the derived switch: Bose functional restricted to r < r_d."""
import sys, json, numpy as np
sys.path.insert(0,'/tmp/claude-0/c25')
import descent3 as D
case, kpo, reg, rd, seed = sys.argv[1], float(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5])
D.FUNC = 'D'
def psi_g(rg, gb, gs):
    xg = np.sqrt(gb/D.A0); ns = 1/np.expm1(xg); n = np.maximum(gs/gb, 1e-12)
    dpsi = gb*ns*(1+ns)*(np.log1p(1/n) - xg); dpsi = np.where(rg <= rd, dpsi, 0.0)
    psi = np.zeros_like(rg); psi[:-1] = -np.cumsum((0.5*(dpsi[1:]+dpsi[:-1])*np.diff(rg))[::-1])[::-1]
    return psi
D.psi_bose = psi_g
res = D.run(case, kpo, reg, 4000, 12.0, 175.0, seed); res['functional'] = 'D'; res['support_rd'] = rd
json.dump(res, open(f'/tmp/claude-0/c25/d3_{case}_k{kpo:g}_reg{reg:g}_N4000_sig175_s{seed}_FD_rd{rd:g}.json','w'), indent=1)
print('done')
