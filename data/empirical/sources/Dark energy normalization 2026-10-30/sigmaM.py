"""sigma(M) for the O.12 first-entry history: Eisenstein-Hu (1998) no-wiggle transfer, Planck-like reference
(h = 0.674, Om = 0.315, Ob = 0.0493, n_s = 0.965), normalized to sigma_8 = 0.810. M in Msun (no h)."""
import numpy as np
h, Om, Ob, ns, s8 = 0.674, 0.315, 0.0493, 0.965, 0.810
def _T(k):
    om, ob = Om * h ** 2, Ob * h ** 2; fb = Ob / Om; th = 2.7255 / 2.7
    s = 44.5 * np.log(9.83 / om) / np.sqrt(1 + 10 * ob ** 0.75)
    al = 1 - 0.328 * np.log(431 * om) * fb + 0.38 * np.log(22.3 * om) * fb ** 2
    G = Om * h * (al + (1 - al) / (1 + (0.43 * k * h * s) ** 4)); q = k * th ** 2 / G
    L0 = np.log(2 * np.e + 1.8 * q); C0 = 14.2 + 731 / (1 + 62.5 * q)
    return L0 / (L0 + C0 * q ** 2)
_k = np.logspace(-5, 5, 6000)                 # h/Mpc
_P = _k ** ns * _T(_k) ** 2
def _sig_R(R):                                # R in Mpc/h
    x = np.outer(np.atleast_1d(R), _k); W = 3 * (np.sin(x) - x * np.cos(x)) / x ** 3
    W[x < 1e-3] = 1.0
    return np.sqrt(np.trapezoid(_P * W ** 2 * _k ** 3, np.log(_k), axis=1) / (2 * np.pi ** 2))
_norm = s8 / _sig_R(8.0)[0]
_lM = np.linspace(2, 17, 600)
_rho = 2.775e11 * Om                          # h^2 Msun / Mpc^3 -> with M in Msun/h
_R = (3 * (10 ** _lM * h) / (4 * np.pi * _rho)) ** (1 / 3)
_sig = _norm * _sig_R(_R)
def sigma_interp(lM): return np.interp(lM, _lM, _sig)
