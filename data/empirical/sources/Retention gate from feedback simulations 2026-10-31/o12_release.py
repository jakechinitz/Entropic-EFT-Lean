"""
O.12 release history: absorbing first-entry excursion set with the retained-well gate, convolved with the
mixing kernel K_mix = 1 - exp(-tau / (f t_dyn(z_f))).

  V_crit = 17 km/s for z > z_re = 7.66, 30 km/s below; M_crit from the Bryan-Norman virial relation
  S_crit(z) = sigma^2[M_crit(z)], barrier B(z) = delta_c / D(z)
  F_Z(z) = P[ max_{z' >= z} { max_{s < S_crit(z')} delta(s) - B(z') } >= 0 ]
  F_rel(t) = int K_mix(t - t_f) dF_Z(t_f),  I_rel = int a^-3 dF_rel

Validation targets (manuscript O.12): F_Z(10, 8, 7, 6, 5, 3, 1, 0) = 0.0138 0.0388 0.0522 0.0704 0.104 0.243 0.509 0.671;
I_rel(f = 0, 0.25, 0.5, 0.75, 1, 2) = 103.7 96.3 90.2 85.0 80.6 67.3.
"""
import numpy as np, sys, os
from scipy.integrate import quad, cumulative_trapezoid
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sigmaM as S

h, Om = S.h, S.Om
OL = 1 - Om
G = 4.30091e-9                 # Mpc (km/s)^2 / Msun
H0 = 100 * h                   # km/s/Mpc
GYR = 977.8 / h * h            # placeholder (not used)


def Hz(z):
    return H0 * np.sqrt(Om * (1 + z) ** 3 + OL)


def delta_c_vir(z):
    x = Om * (1 + z) ** 3 / (Om * (1 + z) ** 3 + OL) - 1
    return 18 * np.pi ** 2 + 82 * x - 39 * x * x


def M_crit(z, zre=7.66, v_pre=17.0, v_post=30.0):
    V = np.where(z > zre, v_pre, v_post)
    return V ** 3 / (G * Hz(z) * np.sqrt(delta_c_vir(z) / 2))


def t_of_z(z):
    a = 1 / (1 + z)
    H0g = H0 / 977.79                     # 1/Gyr
    return quad(lambda x: 1 / (x * H0g * np.sqrt(Om / x ** 3 + OL)), 1e-9, a)[0]


def t_dyn(z):                              # Gyr
    return 977.79 / (Hz(z) * np.sqrt(delta_c_vir(z) / 2))


def growth(z):
    a = 1 / (1 + z)
    f = lambda x: 1 / (x * np.sqrt(Om / x ** 3 + OL)) ** 3
    E = np.sqrt(Om / a ** 3 + OL)
    return E * quad(f, 1e-8, a)[0] / quad(f, 1e-8, 1)[0]


def first_entry(zgrid, ntraj=300000, nS=4000, seed=7, batch=2000, **gate):
    """F_Z on zgrid (descending z). Returns array of the same length."""
    Sc = S.sigma_interp(np.log10(M_crit(zgrid, **gate))) ** 2
    B = 1.686 / np.array([growth(z) for z in zgrid])
    Smax = Sc.max() * 1.0001
    Sg = np.linspace(0, Smax, nS + 1)
    dS = Sg[1] - Sg[0]
    idx = np.searchsorted(Sg, Sc)            # grid index just above S_crit(z)
    rng = np.random.default_rng(seed)
    hit_any = np.zeros(len(zgrid))
    done = 0
    while done < ntraj:
        n = min(batch, ntraj - done)
        steps = rng.normal(scale=np.sqrt(dS), size=(n, nS))
        d = np.concatenate([np.zeros((n, 1)), np.cumsum(steps, axis=1)], axis=1)
        # Brownian-bridge maxima inside each interval
        U = rng.uniform(size=(n, nS))
        a_, b_ = d[:, :-1], d[:, 1:]
        bm = 0.5 * (a_ + b_ + np.sqrt((b_ - a_) ** 2 - 2 * dS * np.log(U)))
        runmax = np.maximum.accumulate(np.concatenate([np.zeros((n, 1)), bm], axis=1), axis=1)
        # max over s < S_crit(z): use the running max up to the interval containing S_crit (bridge-corrected,
        # slightly conservative by a fraction of one interval)
        Mz = runmax[:, np.clip(idx, 0, nS)]
        hit = Mz >= B[None, :]
        # absorbing: entered by z if any z' >= z hit (zgrid descending)
        ever = np.maximum.accumulate(hit, axis=1)
        hit_any += ever.sum(0)
        done += n
    return hit_any / ntraj


def release(zgrid, FZ, f):
    """F_rel(a) on the same grid given F_Z and the kernel ratio f."""
    t = np.array([t_of_z(z) for z in zgrid])
    dF = np.diff(np.concatenate([[0.0], FZ]))
    td = t_dyn(zgrid)
    Frel = np.zeros_like(FZ)
    for j in range(len(zgrid)):
        if dF[j] <= 0:
            continue
        tau = t - t[j]
        if f == 0:
            K = (tau >= 0).astype(float)
        else:
            K = np.where(tau >= 0, 1 - np.exp(-np.maximum(tau, 0) / (f * td[j])), 0.0)
        Frel += dF[j] * K
    a = 1 / (1 + zgrid)
    Irel = np.sum(np.diff(np.concatenate([[0.0], Frel])) / a ** 3)
    return Frel, Irel


if __name__ == "__main__":
    zgrid = np.round(np.arange(30.0, -1e-9, -0.01), 4)
    cache = "FZ_ref.npy"
    if os.path.exists(cache):
        FZ = np.load(cache)
    else:
        FZ = first_entry(zgrid)
        np.save(cache, FZ)
    print("F_Z:", " ".join("z=%g:%.4f" % (z, np.interp(-z, -zgrid, FZ)) for z in (10, 8, 7, 6, 5, 3, 1, 0)))
    print("manuscript: z=10:0.0138 z=8:0.0388 z=7:0.0522 z=6:0.0704 z=5:0.104 z=3:0.243 z=1:0.509 z=0:0.671")
    for f in (0, 0.25, 0.5, 0.75, 1.0, 2.0):
        Fr, I = release(zgrid, FZ, f)
        print("f=%.2f  I_rel=%.1f  F_rel(0)=%.3f" % (f, I, Fr[-1]))
    print("manuscript I_rel: 103.7 96.3 90.2 85.0 80.6 67.3")
