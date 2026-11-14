"""Frozen release histories F_rel(z) on the O.12 grid (z = 30..0 step 0.01): pre-reionization gate from the
Renaissance occupation (mixture of sharp mass gates), post-reionization gate 30 km/s, z_re 7.66, six measured kernels."""
import numpy as np, sys
from gate_mass import *
def Frel(FZ, K0, f):
    dF = np.diff(np.concatenate([[0.0], FZ])); Fr = np.zeros_like(FZ)
    for j in np.nonzero(dF > 0)[0]:
        tau = t - t[j]
        Fr += dF[j] * np.where(tau >= 0, 1 - (1 - K0) * np.exp(-np.maximum(tau, 0) / max(f * td[j], 1e-9)), 0.0)
    return Fr
if sys.argv[1] == 'check':
    FTAB = np.load('/home/claude/cos/ext/zoom/Frel_table.npy')
    FZ = first_entry_M(lambda z: np.log10(Mvir(17.0, z)))
    for f in (0.25, 0.30):
        fr = Frel(FZ, 0.0, f); tab = FTAB[int(round(f / .05))]
        print(f, 'max|diff|', np.abs(fr - tab).max(), 'F0', fr[-1], tab[-1], 'I', np.sum(np.diff(np.concatenate([[0], fr])) / a**3), np.sum(np.diff(np.concatenate([[0], tab])) / a**3))
    sys.exit()
zre = float(sys.argv[2]); vpost = float(sys.argv[3]); out = sys.argv[4]
import os
STEP = float(os.environ.get('STEP', '0.05')); NT = int(os.environ.get('NT', '80000'))
lMs = np.linspace(6.85, 8.5, int(round(1.65 / STEP)) + 1)
pts = np.array([(6.85, 0), (7.0, 0.1), (8.0, 0.5), (8.5, 1.0)])
cdf = np.interp(lMs, pts[:, 0], pts[:, 1]); w = np.diff(cdf); mids = 0.5 * (lMs[1:] + lMs[:-1])
H = {k: np.zeros_like(zg) for k in KERNELS}
for m, wi in zip(mids, w):
    if wi <= 0: continue
    FZ = first_entry_M(float(m), zre=zre, v_post=vpost, ntraj=NT)
    for k, (K0, f) in KERNELS.items(): H[k] += wi * Frel(FZ, K0, f)
    print(round(m, 3), round(wi, 4), flush=True)
arr = np.array([H[k] for k in KERNELS]); np.save(out, arr)
for k, h in zip(KERNELS, arr): print(k, 'F0=%.4f I=%.2f' % (h[-1], np.sum(np.diff(np.concatenate([[0], h])) / a**3)))
