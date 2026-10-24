"""Checks for the envelope-premises note (2026-10-24).

1. Closed forms for the matched envelope (edge, stock) against direct ODE integration.
2. Inversion of the total stock ratio S(eta) and the edge radius in units of r_M.
3. Weak-lensing lower bounds on S for the Mistele et al. (2024) baryonic-mass bins.
4. The saved Milky Way-like benchmark's circular speed beyond its edge.
Units for (1)-(2): G = a0 = M_b = 1, so A = 1 and r_M = 1.
"""
import math, json
import numpy as np
from scipy.integrate import solve_ivp, quad
from scipy.optimize import brentq

def q_of(e): return math.sqrt(2/(1+e))
def S_of(e):
    q = q_of(e); b = math.atan(q)
    return (1-e)/(2*e) + (1/(2*e))*math.sqrt(1+q*q)/q**3*(b+q-2*q/math.sqrt(1+q*q))
def R_over_rM(e): q = q_of(e); return (1+math.atan(q)/q)/(2*e)

out = {"ode_check": [], "table": [], "lensing": [], "benchmark": {}}
for eta in [0.03, 0.06, 0.13, 0.3, 0.6]:
    A = 1.0; a = 1/(2*eta); zeta = math.pi*(1+eta)*a*a; k = math.sqrt(2*math.pi/zeta)
    rho_a = A/(4*math.pi*a*a); drho_a = -2*A/(4*math.pi*a**3)
    f = lambda r, y: [y[1], -2*y[1]/r - k*k*y[0]]
    ev = lambda r, y: y[0]; ev.terminal = True; ev.direction = -1
    sol = solve_ivp(f, [a, 10*a], [rho_a, drho_a], events=ev, rtol=1e-12, atol=1e-16, dense_output=True)
    R = sol.t_events[0][0]
    Menv = quad(lambda r: 4*math.pi*r*r*sol.sol(r)[0], a, R, limit=400)[0]
    q = k*a; b = math.atan(q)
    Mform = A*a*math.sqrt(1+q*q)/q**3*(b+q-2*q/math.sqrt(1+q*q))
    g_a = (0.5 + A*a)/a**2
    out["ode_check"].append(dict(eta=eta, R_over_a_ode=R/a, R_over_a_closed=1+b/q,
        Menv_ode=Menv, Menv_closed=Mform, hydrostatic_lhs=2*zeta*drho_a, hydrostatic_rhs=-g_a,
        g_a_over_a0=g_a, closed_g_a=2*eta*(1+eta)))
for S in [5.1760752, 11.5, 29, 100]:
    e = brentq(lambda x: S_of(x)-S, 1e-6, 0.999)
    out["table"].append(dict(S=S, eta=e, a_over_rM=1/(2*e), R_over_rM=R_over_rM(e), R_over_S_rM=R_over_rM(e)/S))

G = 6.674e-11; Msun = 1.989e30; a0 = 1.2307e-10; kpc = 3.0857e19; kC = 5.1760752
for lo, hi in [(9, 10.5), (10.5, 10.8), (10.8, 11.1), (11.1, 11.5)]:
    lm = (lo+hi)/2; rM = math.sqrt(G*10**lm*Msun/a0)/kpc
    row = dict(logMb=lm, rM_kpc=rM)
    for L in [300, 1000]:
        e = brentq(lambda x: R_over_rM(x)*rM - L, 1e-7, 0.99); S = S_of(e)
        row["L%d" % L] = dict(S_min=S, f_ret_max=kC/S, rigorous_S_min=(L/rM-1)/2)
    out["lensing"].append(row)

Mb = 6.9e10*Msun; S = 11.5029; Rkpc = 124.45588
Mtot = Mb*(1+S)
out["benchmark"] = dict(rM_kpc=math.sqrt(G*Mb/a0)/kpc, v_flat_kms=(G*Mb*a0)**0.25/1e3,
    v_at_kms={str(r): math.sqrt(G*Mtot/(r*kpc))/1e3 for r in [Rkpc, 300, 1000]})
ok = all(abs(c["R_over_a_ode"]-c["R_over_a_closed"]) < 1e-8 and abs(c["Menv_ode"]-c["Menv_closed"]) < 1e-7*c["Menv_closed"]
         and abs(c["hydrostatic_lhs"]-c["hydrostatic_rhs"]) < 1e-12 and abs(c["g_a_over_a0"]-c["closed_g_a"]) < 1e-12
         for c in out["ode_check"])
out["closed_forms_match_ode"] = ok
print(json.dumps(out, indent=1))
