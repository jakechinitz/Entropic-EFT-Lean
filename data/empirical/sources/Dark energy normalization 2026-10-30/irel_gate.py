"""I_rel as a function of the pre-reionization retention gate, with the kernels measured in the zoom
(K_mix = 1 - (1-K0) exp(-tau/(f t_dyn))), and the implied Omega_Lambda and H0 for the tied abundance."""
import numpy as np, json, sys
sys.path.insert(0, '/home/claude/lam'); import o12_release as O
zg = np.round(np.arange(30.0, -1e-9, -0.01), 4)
t = np.array([O.t_of_z(z) for z in zg]); td = O.t_dyn(zg); a = 1 / (1 + zg)
def I_rel(FZ, K0, f):
    dF = np.diff(np.concatenate([[0.0], FZ])); Fr = np.zeros_like(FZ)
    for j in np.nonzero(dF > 0)[0]:
        tau = t - t[j]
        Fr += dF[j] * np.where(tau >= 0, 1 - (1 - K0) * np.exp(-np.maximum(tau, 0) / max(f * td[j], 1e-9)), 0.0)
    return float(np.sum(np.diff(np.concatenate([[0.0], Fr])) / a ** 3)), float(Fr[-1])
ETA = 0.0298668443935; wb = 0.02238; wc = 5.333 * wb; wnu = 0.06 / 93.14
def cosmo(I, F0):
    wL = ETA * wc * I; h2 = wb + wc * (1 - ETA * F0) + wnu + wL
    return dict(h=float(np.sqrt(h2)), OmL=float(wL / h2))
kernels = {'v14 shells': (0.56, 2.54), 'v14 R/2': (0.53, 2.24), 'v14 R/4': (0.58, 3.90),
           'v12 shells': (0.58, 2.85), 'v12 R/2': (0.56, 2.49), 'v12 R/4': (0.70, 4.94), 'pure exp f=0.28': (0.0, 0.28)}
out = {}
for V in (9.0, 10.0, 11.0, 12.0, 14.0, 17.0):
    FZ = O.first_entry(zg, ntraj=80000, v_pre=V)
    row = {}
    for k, (K0, f) in kernels.items():
        I, F0 = I_rel(FZ, K0, f); row[k] = dict(I_rel=I, F0=F0, **cosmo(I, F0))
    I0, F00 = I_rel(FZ, 1.0, 1.0); row['instant'] = dict(I_rel=I0, F0=F00, **cosmo(I0, F00))
    out[V] = row
    print(f"V_pre={V:4.1f}  F_Z(10)={np.interp(-10,-zg,FZ):.4f}  " + '  '.join(f"{k}: I={r['I_rel']:.1f} h={r['h']:.3f}" for k, r in row.items()), flush=True)
json.dump(out, open('irel_gate.json', 'w'), indent=1)
