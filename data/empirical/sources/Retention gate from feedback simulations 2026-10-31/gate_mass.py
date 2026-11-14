"""I_rel for a pre-reionization retention gate given as a halo MASS (constant or z-dependent), with the
post-reionization gate and z_re as before. Uses the O.12 first-entry construction and the six measured kernels."""
import numpy as np, json, sys, time
import o12_release as O
zg = np.round(np.arange(30.0, -1e-9, -0.01), 4)
t = np.array([O.t_of_z(z) for z in zg]); td = O.t_dyn(zg); a = 1 / (1 + zg)
KERNELS = {'v14 shells': (0.56, 2.54), 'v14 R/2': (0.53, 2.24), 'v14 R/4': (0.58, 3.90),
           'v12 shells': (0.58, 2.85), 'v12 R/2': (0.56, 2.49), 'v12 R/4': (0.70, 4.94)}
def Mvir(V, z): return V ** 3 / (O.G * O.Hz(z) * np.sqrt(O.delta_c_vir(z) / 2))
def Vvir(M, z): return (M * O.G * O.Hz(z) * np.sqrt(O.delta_c_vir(z) / 2)) ** (1 / 3)
def first_entry_M(lMpre, zre=7.66, v_post=30.0, ntraj=80000, seed=7):
    """lMpre: log10 gate mass before reionization (scalar or callable of z)."""
    lm = lMpre(zg) if callable(lMpre) else np.full_like(zg, lMpre)
    Mc = np.where(zg > zre, 10 ** lm, Mvir(v_post, zg))
    orig = O.M_crit
    O.M_crit = lambda z, **k: np.interp(-np.asarray(z), -zg, Mc)
    try: return O.first_entry(zg, ntraj=ntraj, seed=seed)
    finally: O.M_crit = orig
def I_rel(FZ, K0, f):
    dF = np.diff(np.concatenate([[0.0], FZ])); Fr = np.zeros_like(FZ)
    for j in np.nonzero(dF > 0)[0]:
        tau = t - t[j]
        Fr += dF[j] * np.where(tau >= 0, 1 - (1 - K0) * np.exp(-np.maximum(tau, 0) / max(f * td[j], 1e-9)), 0.0)
    return float(np.sum(np.diff(np.concatenate([[0.0], Fr])) / a ** 3)), float(Fr[-1])
ETA = 0.0298668443935; wb = 0.02238; wc = 5.333 * wb; wnu = 0.06 / 93.14
def cosmo(I, F0):
    wL = ETA * wc * I; h2 = wb + wc * (1 - ETA * F0) + wnu + wL
    return float(np.sqrt(h2)), float(wL / h2)
def irel_all(FZ):
    return {k: I_rel(FZ, *v) for k, v in KERNELS.items()}
if __name__ == '__main__':
    t0 = time.time()
    # validation: V gate 14 km/s reproduces irel_gate.json
    FZ = first_entry_M(lambda z: np.log10(Mvir(14.0, z)))
    print('V=14 check', {k: round(v[0], 1) for k, v in irel_all(FZ).items()}, round(time.time() - t0), 's')
    for z in (15, 12, 10, 8): print(z, 'M(14km/s)=%.2e  V(1e8)=%.1f  V(3e7)=%.1f' % (Mvir(14, z), Vvir(1e8, z), Vvir(3e7, z)))
