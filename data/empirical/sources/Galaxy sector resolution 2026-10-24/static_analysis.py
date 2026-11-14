"""Static analysis of the galaxy-sector completion.

Spherical systems.  Units: kpc, km/s, Msun, G = 4.30091e-6.
  g_b = G M_b(<r)/r^2,  J(g_b) = n_B(sqrt(g_b/a0)) g_b,  M_perp(<r) = r^2 J / G.

Parts
  1. Stiff-coupling amplification: a stock held at the RAR density by a stiff coupling
     transmits a fractional Jeans imbalance delta_J of the stock to the baryons as
     a_b = g_RAR (1 - delta_J J'(g_b)) + O(1/lambda).  Tabulate J' for benchmarks.
  2. Response stock: density, positivity, budget cap R_cap, Eddington isotropic DF in the
     total RAR potential, f >= 0 check.
  3. Energy budget: mechanical energy (K+W, self + baryon) of a stock of the same mass in
     (a) an isotropic Jeans NFW halo with the same baryons and (b) the capped RAR stock.
  4. Clusters with the coupling off: fitted acceleration scale of the BCG region.
"""
import numpy as np, math, json
from scipy.integrate import quad, cumulative_trapezoid
from scipy.optimize import brentq, minimize_scalar

G = 4.30091e-6
A0 = 1.2307e-10*3.0857e19/1e6          # (km/s)^2/kpc
h = 0.6894
RHOC = 3*(0.1*h)**2/(8*math.pi*G)

def nB(x): return 1/np.expm1(x)
def J(gb): x = np.sqrt(gb/A0); return nB(x)*gb
def Jprime(gb, eps=1e-6):
    return (J(gb*(1+eps))-J(gb*(1-eps)))/(2*eps*gb)

def Mexp(r, M, Rd): x = r/Rd; return M*(1-(1+x)*np.exp(-x))
def Mhern(r, M, a): return M*r**2/(r+a)**2

# Benchmarks: baryons as spherical-equivalent disk (+ bulge).  Budget from abundance
# matching: stock = (1 - f_b,cosmic) M200 with Moster-like M200(M_b).
BENCH = {
  'MW':        dict(parts=[('exp', 6.0e10, 2.6), ('hern', 9.0e9, 0.7)]),
  'dwarf':     dict(parts=[('exp', 3.0e8, 1.0)]),
  'LSB_dwarf': dict(parts=[('exp', 3.0e8, 3.0)]),
  'massive':   dict(parts=[('exp', 1.5e11, 5.0), ('hern', 5e10, 1.5)]),
  # clusters/groups: BCG (Hernquist) + ICM beta-model gas (beta = 2/3), explicit M200
  'MW_c+':     dict(parts=[('exp', 6.0e10, 2.6), ('hern', 9.0e9, 0.7)], dc=0.2),
  'MW_c-':     dict(parts=[('exp', 6.0e10, 2.6), ('hern', 9.0e9, 0.7)], dc=-0.2),
  'MW_light':  dict(parts=[('exp', 6.0e10, 2.6), ('hern', 9.0e9, 0.7)], M200=1.5e12),
  'Sb':        dict(parts=[('exp', 1.0e10, 2.0)]),
  'dwarf_c+':  dict(parts=[('exp', 3.0e8, 1.0)], dc=0.2),
  'dwarf_c-':  dict(parts=[('exp', 3.0e8, 1.0)], dc=-0.2),
  'massive_spiral':       dict(parts=[('exp', 1.5e11, 5.0), ('hern', 5e10, 1.5)], M200=2.5e12),
  'massive_spiral_heavy': dict(parts=[('exp', 1.5e11, 5.0), ('hern', 5e10, 1.5)], M200=6.0e12),
  'group_small':          dict(parts=[('hern', 2.0e11, 6.0), ('beta', 1.0e12, 40.0)], M200=1.5e13),
  'cluster':   dict(parts=[('hern', 1.2e12, 15.0), ('beta', 9.0e13, 150.0)], M200=6.0e14),
  'group':     dict(parts=[('hern', 4.0e11, 8.0), ('beta', 4.0e12, 60.0)], M200=5.0e13),
}
def Mb_of(parts):
    def f(r):
        out = 0.0*np.asarray(r, float)
        for kind, M, s in parts:
            if kind == 'exp': out = out + Mexp(r, M, s)
            elif kind == 'hern': out = out + Mhern(r, M, s)
            else:   # beta = 2/3 gas: M(<r) = M (x - arctan x) normalised at x = 10
                x = np.asarray(r, float)/s
                out = out + M*(x-np.arctan(x))/(10-math.atan(10))
        return out
    return f

def moster_M200(Mb):
    def ms(M):
        M1, N, b, g = 10**11.59, 0.0351, 1.376, 0.608
        return 2*N*M/((M/M1)**(-b)+(M/M1)**g)
    return 10**brentq(lambda lm: math.log10(ms(10**lm))-math.log10(Mb), 9, 15.5)

def nfw_params(M200, dc=0.0):
    c = 10**(0.905-0.101*math.log10(M200*h/1e12)+dc)
    r200 = (3*M200/(4*math.pi*200*RHOC))**(1/3); rs = r200/c
    rhos = M200/(4*math.pi*rs**3*(math.log(1+c)-c/(1+c)))
    return c, r200, rs, rhos

def M_nfw(r, rhos, rs): x = r/rs; return 4*math.pi*rhos*rs**3*(np.log1p(x)-x/(1+x))

def energies(r, Ms, Mb):
    """Isotropic Jeans equilibrium of a stock with enclosed mass Ms(r) in the potential of
    Ms + Mb; returns K, W_self, W_b (interaction), all on grid r (stock truncated at r[-1])."""
    rho = np.gradient(Ms, r)/(4*math.pi*r**2); rho = np.maximum(rho, 0)
    g = G*(Ms+Mb)/r**2
    # sigma^2 rho = int_r^R rho g dr  (zero pressure at the edge)
    P = np.concatenate([cumulative_trapezoid((rho*g)[::-1], -r[::-1], initial=0)[::-1]])
    K = 1.5*np.trapezoid(4*math.pi*r**2*P, r)
    # W_self = -int G Ms dMs / r ; W_b = -int G Mb dMs / r  (energy of stock in baryon field
    # counted fully, baryons static)
    dM = np.gradient(Ms, r)
    Wself = -np.trapezoid(G*Ms*dM/r, r)
    # potential of baryons: Phi_b(r) = -G Mb(r)/r - G int_r^inf dMb/r'
    Mbtot = Mb[-1]
    dMb = np.gradient(Mb, r)
    outer = cumulative_trapezoid((dMb/r)[::-1], -r[::-1], initial=0)[::-1]
    Phib = -G*Mb/r - G*outer - 0.0
    Wb = np.trapezoid(Phib*dM, r)
    return K, Wself, Wb

def eddington(r, rho, Mtot):
    """Isotropic Eddington DF for density rho(r) in the potential of Mtot(r) (total
    enclosed mass), truncated at r[-1].  Returns min f / max f and the energy grid."""
    g = G*Mtot/r**2
    # relative potential Psi = Phi(R) - Phi(r) >= 0
    Psi = cumulative_trapezoid(g[::-1], -r[::-1], initial=0)[::-1]
    Psi = Psi + G*Mtot[-1]/r[-1]*0   # truncated: Psi(R)=0 at edge
    # d rho / d Psi as function of Psi
    order = np.argsort(Psi)
    P = Psi[order]; R = rho[order]
    drdP = np.gradient(R, P)
    Es = np.linspace(P[1], P[-1], 300)
    F = []
    for E in Es:
        m = P < E
        if m.sum() < 3: F.append(np.nan); continue
        integrand = drdP[m]/np.sqrt(E-P[m]+1e-30)
        F.append(np.trapezoid(integrand, P[m]))
    F = np.array(F)
    f = np.gradient(F, Es)/(math.sqrt(8)*math.pi**2)
    ok = np.isfinite(f)
    return float(np.nanmin(f[ok][5:])), float(np.nanmax(f[ok])), Es, f

def analyse(name, parts):
    Mbf = Mb_of(parts); Mbtot = sum(p[1] for p in parts)
    M200 = moster_M200(Mbtot)
    c, r200, rs, rhos = nfw_params(M200)
    stock_budget = 0.84*M200          # 1 - Omega_b/Omega_m
    r = np.geomspace(1e-2, 3*r200, 6000)
    Mb = Mbf(r); gb = G*Mb/r**2
    Mperp = r**2*J(gb)/G
    rho_perp = np.gradient(Mperp, r)/(4*math.pi*r**2)
    neg = r[rho_perp < 0]
    # budget cap
    Rcap = float(np.interp(stock_budget, Mperp, r)) if Mperp[-1] > stock_budget else float('inf')
    S_cap = stock_budget/Mbtot
    # stiff-coupling amplification table
    tab = []
    for rr in (2, 5, 10, 20, 50, 100, 200):
        if rr < r[-1]:
            g = float(np.interp(rr, r, gb)); tab.append(dict(r=rr, gb_over_a0=g/A0, Jprime=float(Jprime(np.array(g)))))
    # energies: NFW stock (same budget, out to r200) vs capped RAR stock (out to Rcap)
    rN = np.geomspace(1e-2, r200, 4000)
    MsN = 0.84*M_nfw(rN, rhos, rs)
    KN, WsN, WbN = energies(rN, MsN, Mbf(rN))
    rR = np.geomspace(1e-2, min(Rcap, 3*r200), 4000)
    MsR = rR**2*J(G*Mbf(rR)/rR**2)/G
    KR, WsR, WbR = energies(rR, MsR, Mbf(rR))
    EN = KN+WsN+WbN; ER = KR+WsR+WbR
    # Eddington DF for the capped RAR stock in the total potential
    rhoR = np.gradient(MsR, rR)/(4*math.pi*rR**2)
    fmin, fmax, Es, f = eddington(rR, np.maximum(rhoR, 0), MsR+Mbf(rR))
    Vf = (G*Mbtot*A0)**0.25
    return dict(name=name, Mb=Mbtot, M200=M200, c=c, r200=r200, stock_budget=stock_budget,
                S_budget=S_cap, R_cap=Rcap, V_flat=Vf,
                negative_response_radii=[float(neg.min()), float(neg.max())] if neg.size else None,
                Jprime_table=tab,
                E_NFW_per_mass=EN/MsN[-1], E_RAR_per_mass=ER/MsR[-1],
                dE_per_mass=(ER-EN)/MsN[-1], dE_over_Vf2=(ER-EN)/MsN[-1]/Vf**2,
                virial_NFW=2*KN/abs(WsN+WbN), virial_RAR=2*KR/abs(WsR+WbR),
                eddington_fmin_over_fmax=fmin/fmax)

if __name__ == "__main__":
  out = {}
  for name, b in BENCH.items():
      out[name] = analyse(name, b['parts']); print(json.dumps(out[name], indent=1), flush=True)
  json.dump(out, open('/tmp/claude-0/c25/static_results.json', 'w'), indent=1)
