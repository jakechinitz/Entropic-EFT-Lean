"""Retention gate from the carrier criterion (Section 18): a well holds records when its virialized gas can cool,
t_cool(T_vir, n_vir) < t_dyn. Primordial gas (X = 0.76) in collisional ionization equilibrium, atomic H/He
cooling (Katz, Weinberg & Hernquist 1996 rates) plus Compton cooling on the CMB; no H2, no UV background.
Gas density: mean virial overdensity Delta_c(z) rho_crit(z) times f_b. t_dyn = R_vir/V_vir as in O.12.
T_vir = mu m_p V^2 / (2 k) (Barkana & Loeb 2001), mu from the CIE ionization state at T_vir."""
import numpy as np, json, sys
from scipy.optimize import brentq
sys.path.insert(0, '/home/claude/lam'); import o12_release as O
kB, mp = 1.380649e-16, 1.6726e-24; X = 0.76; Y = 1 - X; yHe = Y / (4 * X)
def rates(T):
    s = 1 + np.sqrt(T / 1e5)
    G = dict(H0=5.85e-11 * np.sqrt(T) * np.exp(-157809.1 / T) / s, He0=2.38e-11 * np.sqrt(T) * np.exp(-285335.4 / T) / s,
             Hep=5.68e-12 * np.sqrt(T) * np.exp(-631515.0 / T) / s)
    a = dict(Hp=8.40e-11 / np.sqrt(T) * (T / 1e3) ** -0.2 / (1 + (T / 1e6) ** 0.7),
             Hep=1.50e-10 * T ** -0.6353 + 1.9e-3 * T ** -1.5 * np.exp(-470000 / T) * (1 + 0.3 * np.exp(-94000 / T)),
             Hepp=3.36e-10 / np.sqrt(T) * (T / 1e3) ** -0.2 / (1 + (T / 1e6) ** 0.7))
    return G, a
def cie(T):
    G, a = rates(T)
    xHp = G['H0'] / (G['H0'] + a['Hp'])
    r1 = G['He0'] / a['Hep']; r2 = G['Hep'] / a['Hepp']          # n_He+/n_He0, n_He++/n_He+
    f0 = 1 / (1 + r1 + r1 * r2); f1 = r1 * f0; f2 = r1 * r2 * f0
    return xHp, f0, f1, f2
def Lambda(T, nH, z):
    """Net cooling rate per volume, erg/cm^3/s."""
    G, a = rates(T); xHp, f0, f1, f2 = cie(T)
    nHp, nH0 = xHp * nH, (1 - xHp) * nH; nHe = yHe * nH
    nHe0, nHep, nHepp = f0 * nHe, f1 * nHe, f2 * nHe
    ne = nHp + nHep + 2 * nHepp; s = 1 + np.sqrt(T / 1e5)
    L = 7.50e-19 * np.exp(-118348 / T) / s * ne * nH0                      # H excitation
    L += 5.54e-17 * T ** -0.397 * np.exp(-473638 / T) / s * ne * nHep       # He+ excitation
    L += 1.27e-21 * np.sqrt(T) * np.exp(-157809.1 / T) / s * ne * nH0      # collisional ionization
    L += 9.38e-22 * np.sqrt(T) * np.exp(-285335.4 / T) / s * ne * nHe0
    L += 4.95e-22 * np.sqrt(T) * np.exp(-631515 / T) / s * ne * nHep
    L += 8.70e-27 * np.sqrt(T) * (T / 1e3) ** -0.2 / (1 + (T / 1e6) ** 0.7) * ne * nHp   # recombination
    L += (1.55e-26 * T ** 0.3647 + 1.24e-13 * T ** -1.5 * np.exp(-470000 / T) * (1 + 0.3 * np.exp(-94000 / T))) * ne * nHep
    L += 3.48e-26 * np.sqrt(T) * (T / 1e3) ** -0.2 / (1 + (T / 1e6) ** 0.7) * ne * nHepp
    gff = 1.1 + 0.34 * np.exp(-(5.5 - np.log10(T)) ** 2 / 3)
    L += 1.42e-27 * gff * np.sqrt(T) * (nHp + nHep + 4 * nHepp) * ne      # bremsstrahlung
    L += 5.41e-36 * ne * (T - 2.7255 * (1 + z)) * (1 + z) ** 4             # Compton
    ntot = nH + nHe + ne
    mu = (nH + 4 * nHe) / ntot
    return L, ntot, mu
def nH_vir(z):
    rho_c = 1.8785e-29 * O.h ** 2 * (O.Hz(z) / O.H0) ** 2                  # g/cm^3
    return O.delta_c_vir(z) * rho_c * (O.S.Ob / O.S.Om) * X / mp
def ratio(T, z):
    L, ntot, mu = Lambda(T, nH_vir(z), z)
    tcool = 1.5 * ntot * kB * T / L / 3.156e16                               # Gyr
    return tcool / O.t_dyn(z), mu
def gate(z):
    T = brentq(lambda lt: np.log(ratio(10 ** lt, z)[0]), 3.7, 5.0, xtol=1e-6); T = 10 ** T
    mu = ratio(T, z)[1]
    V = np.sqrt(2 * kB * T / (mu * mp)) / 1e5
    return T, mu, V
if __name__ == '__main__':
    out = {}
    for z in (30, 25, 20, 15, 12, 10, 8):
        T, mu, V = gate(z)
        out[z] = dict(T=T, mu=mu, V=V, nH=nH_vir(z))
        print(f"z={z:4.1f}  n_H,vir={nH_vir(z):.2e}  T_gate={T:8.0f} K  mu={mu:.3f}  V_gate={V:5.2f} km/s   (T at mu=1.22: V={np.sqrt(2*kB*T/(1.22*mp))/1e5:.2f}; mu=0.59: {np.sqrt(2*kB*T/(0.59*mp))/1e5:.2f})")
    json.dump(out, open('cooling_gate.json', 'w'), indent=1)
