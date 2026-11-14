"""Release-gate crossing for each dwarf's main progenitor (Section 20 / O.12 gates: V_vir > 17 km/s before z_re = 7.66,
> 30 km/s after). Mean mass-accretion history of Fakhouri, Ma & Boylan-Kolchin (2010):
dM/dt = 46.1 Msun/yr (M/1e12)^1.1 (1+1.11 z) sqrt(Om (1+z)^3 + OL), integrated back from M200(z=0).
V_vir from Bryan & Norman (1998) Delta_c relative to critical."""
import numpy as np, json
from scipy.integrate import solve_ivp
G = 4.30091e-6; Om, OL, H0 = 0.315, 0.685, 67.4
def E(z): return np.sqrt(Om * (1 + z)**3 + OL)
def Hkpc(z): return H0 * 1e-3 * E(z)                      # km/s/kpc
def Dc(z):
    x = Om * (1 + z)**3 / E(z)**2 - 1; return 18 * np.pi**2 + 82 * x - 39 * x**2
def Vvir(M, z):
    rho_c = 3 * Hkpc(z)**2 / (8 * np.pi * G)
    R = (3 * M / (4 * np.pi * Dc(z) * rho_c))**(1 / 3); return np.sqrt(G * M / R)
def history(M0, zmax=15):
    # dM/dz = dM/dt * dt/dz ; dt/dz = -1/((1+z) H(z)), H in 1/yr
    H0yr = H0 / 3.0857e19 * 3.156e7
    f = lambda z, lm: [-(46.1 * (np.exp(lm[0]) / 1e12)**1.1 * (1 + 1.11 * z) * E(z)) / ((1 + z) * H0yr * E(z)) / np.exp(lm[0])]
    s = solve_ivp(f, [0, zmax], [np.log(M0)], dense_output=True, rtol=1e-8, max_step=0.05)
    return lambda z: np.exp(s.sol(z)[0])
def crossed(M0, zre=7.66):
    Mz = history(M0); zs = np.linspace(0, 15, 1501)
    V = np.array([Vvir(Mz(z), z) for z in zs])
    pre = V[zs >= zre].max(); post = V[zs < zre].max()
    return bool(pre >= 17 or post >= 30), float(pre), float(post)
if __name__ == '__main__':
    reg = json.load(open('registered_predictions.json'))
    for p in reg['predictions']:
        c, pre, post = crossed(p['M200'])
        print(f"{p['key']:18s} {p['cls']:8s} M200 {p['M200']:.2e}  Vmax(z>=7.66) {pre:5.1f}  Vmax(z<7.66) {post:5.1f}  gate {'crossed' if c else 'not crossed'}")
