"""The paper's release history (Appendix O.12), reconstructed for the cosmology fits.
(Copied from best_fit_tests/best/release.py of the independent best-fit pipeline, unchanged in substance.)

F_Z(z): fraction of the stock that has first entered a retained well (V_vir > 17 km/s before z_re = 7.66, 30 km/s
after; absorbing).  Anchors F_Z = 0.0694 (z = 6), 0.2411 (z = 3), 0.6700 (z = 0).
F_rel(t) = int K(t - t_f) dF_Z(t_f),  K(tau) = 1 - exp[-tau / (f t_dyn(z_f))].
I(a) = int_0^a a'^-3 dF_rel.  For CAMB: conserved CDM plus a fluid X = eta rho_c0 [I(a) - F_rel(a) a^-3] >= 0.
"""
import numpy as np
from scipy.special import erfc, erfcinv
from scipy.integrate import cumulative_trapezoid

ETA = 0.0298668443935
OM, H0, OB, NS, ZRE = 0.315, 67.4, 0.0493, 0.965, 7.66
G = 4.30091e-6
KM_KPC_GYR = 1.0227

def E(z): return np.sqrt(OM * (1 + z)**3 + 1 - OM)
def Hkpc(z): return H0 * 1e-3 * E(z)
def Delta_c(z):
    x = OM * (1 + z)**3 / E(z)**2 - 1
    return 18 * np.pi**2 + 82 * x - 39 * x**2
def t_dyn_gyr(z): return 1.0 / (Hkpc(z) * np.sqrt(Delta_c(z) / 2)) / KM_KPC_GYR
def Mcrit(z, V): return V**3 / (G * Hkpc(z) * np.sqrt(Delta_c(z) / 2))

_zg = np.concatenate([np.linspace(0, 10, 2001), np.logspace(1, 3, 300)[1:]])
_ag = 1 / (1 + _zg)
_la = np.linspace(np.log(1e-5), 0.0, 40001)
_tla = cumulative_trapezoid(977.8 / (H0 * E(np.exp(-_la) - 1)), _la, initial=0.0) \
       + 977.8 / H0 * 2 / (3 * np.sqrt(OM)) * 1e-5**1.5
_tg = np.interp(np.log(_ag), _la, _tla)

def _T_eh(k, h=H0 / 100):
    om, ob = OM * h**2, OB * h**2
    fb = OB / OM; theta = 2.7255 / 2.7
    s = 44.5 * np.log(9.83 / om) / np.sqrt(1 + 10 * ob**0.75)
    alpha = 1 - 0.328 * np.log(431 * om) * fb + 0.38 * np.log(22.3 * om) * fb**2
    Gam = OM * h * (alpha + (1 - alpha) / (1 + (0.43 * k * h * s)**4))
    q = k * theta**2 / Gam
    L0 = np.log(2 * np.e + 1.8 * q); C0 = 14.2 + 731 / (1 + 62.5 * q)
    return L0 / (L0 + C0 * q**2)
_k = np.logspace(-4, 4, 4000)
_P = _k**NS * _T_eh(_k)**2
def sigma_rel(M):
    rho_m = 2.775e11 * OM * (H0 / 100)**2
    R = (3 * M / (4 * np.pi * rho_m))**(1 / 3) * (H0 / 100)
    x = _k * R; W = 3 * (np.sin(x) - x * np.cos(x)) / x**3
    return np.sqrt(np.trapezoid(_P * W**2 * _k**3, np.log(_k)))

_anch = {0.0: 0.6700, 3.0: 0.2411, 6.0: 0.0694}
_nu = {z: np.sqrt(2) * erfcinv(F) for z, F in _anch.items()}
_x = np.log1p(np.array(list(_nu))); _y = np.log(np.array(list(_nu.values())))
BETA, LNNU0 = np.polyfit(_x, _y, 1)
def nu30(z): return np.exp(LNNU0) * (1 + z)**BETA
def nu17(z): return nu30(z) * sigma_rel(Mcrit(z, 30.0)) / sigma_rel(Mcrit(z, 17.0))

def F_Z(z):
    z = np.atleast_1d(z).astype(float)
    out = np.empty_like(z)
    Fre = erfc(nu17(ZRE) / np.sqrt(2))
    for i, zz in enumerate(z):
        if zz >= ZRE:
            out[i] = erfc(nu17(zz) / np.sqrt(2))
        else:
            out[i] = max(Fre, erfc(nu30(zz) / np.sqrt(2)))
    return out

_FZg = F_Z(_zg)
_o = np.argsort(_tg)
_T, _A, _Z, _FZ = _tg[_o], _ag[_o], _zg[_o], _FZg[_o]
_dFZ = np.diff(_FZ, prepend=0.0)

def history(f):
    td = f * t_dyn_gyr(_Z)
    if f > 0:
        tau = _T[:, None] - _T[None, :]
        K = np.where(tau >= 0, 1 - np.exp(-np.clip(tau, 0, None) / td[None, :]), 0.0)
        Frel = K @ _dFZ
    else:
        Frel = _FZ.copy()
    I = cumulative_trapezoid(_A**-3, Frel, initial=0.0)
    return _A, Frel, I

def Irel_of_f(f):
    a, F, I = history(f)
    return I[-1], F[-1]

def fluid_table(f, na=400):
    a, F, I = history(f)
    X = I - F * a**-3
    lg = np.linspace(np.log(1e-4), 0.0, na); ag = np.exp(lg)
    Xi = np.interp(lg, np.log(a), X); Fi = np.interp(lg, np.log(a), F)
    w = np.where(Xi > 1e-12 * X[-1], -1 - Fi * ag**-3 / np.maximum(Xi, 1e-300), -30.0)
    return ag, np.clip(w, -30.0, -1.0), Xi
