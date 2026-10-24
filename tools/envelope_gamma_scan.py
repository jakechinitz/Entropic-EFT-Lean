"""Envelope extent and stock for polytropic exponents gamma, matched to the deep-RAR stock.
Units G = a0 = M_b = 1 (so A = 1, r_M = 1). Same matching as the gamma = 2 note:
density and slope continuous at a, hydrostatic balance there, compact baryons."""
import math, json
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq

def envelope(eta, gamma):
    A = 1.0; a = 1/(2*eta)
    rho_a = A/(4*math.pi*a*a); M_a = 0.5 + A*a          # baryons + inner stock
    g_a = M_a/a**2
    K = g_a*a/(2*gamma*rho_a**(gamma-1))               # from K*gamma*rho^(gamma-2)*rho' = -g, rho' = -2 rho/a
    def f(r, y):
        M, rho = y
        rho = max(rho, 0.0)
        return [4*math.pi*r*r*rho, -M*rho**(2-gamma)/(K*gamma*r*r)]
    ev = lambda r, y: y[1]; ev.terminal = True; ev.direction = -1
    sol = solve_ivp(f, [a, 1e5*a], [M_a, rho_a], events=ev, rtol=1e-10, atol=1e-14, max_step=a/20)
    if len(sol.t_events[0]) == 0:
        return dict(R=math.inf, S=math.inf)
    R = sol.t_events[0][0]; M_R = sol.y_events[0][0][0]
    return dict(R=R, S=M_R - 1.0, R_over_a=R/a)

out = {}
for gamma in [2.0, 1.8, 5/3, 1.5, 1.4]:
    rows = []
    for S in [5.18, 11.5, 30, 100]:
        try:
            e = brentq(lambda x: envelope(x, gamma)['S'] - S, 1e-4, 0.99, xtol=1e-10)
            r = envelope(e, gamma)
            rows.append(dict(S=S, eta=e, R_over_rM=r['R'], R_over_a=r['R_over_a'], R_over_S_rM=r['R']/S))
        except ValueError as err:
            rows.append(dict(S=S, error=str(err)))
    out[str(round(gamma, 4))] = rows
print(json.dumps(out, indent=1))
