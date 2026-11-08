"""Check of no-go 2: a stiffly coupled stock that is not self-supported pushes its
imbalance onto the baryons, amplified by J'(g_b).

Spherical energy (static baryons):
  E = int [ -(g_b+g_s)^2 + lam (g_s - J(g_b))^2 ] r^2 dr / (2G)
Stock inward acceleration   a_s = g_b + g_s + lam (J - g_s)
Baryon inward acceleration  a_b = g_b + g_s + lam (g_s - J) J'(g_b)
(variations of E with respect to the enclosed masses; checked by finite differences below).

The RAR stock rho_p has an exact isotropic Jeans dispersion sigma_R^2 in the RAR field
g_R.  Give the stock sigma^2 = (1+d) sigma_R^2 at fixed total mass.  Linearising
rho = rho_p (1 + eps), g_s = J + G dM/r^2 gives the boundary-value problem
  (lam - 1) G dM / r^2 = -d g_R + (1+d) sigma_R^2 d/dr [ dM' / (4 pi r^2 rho_p) ],
  dM(r0) = dM(R) = 0,
solved here by finite differences.  Prediction: a_b/g_R - 1 = -d J' lam/(lam-1) + O(d/lam).
"""
import numpy as np, math, json
from scipy.integrate import cumulative_trapezoid
from scipy.sparse import diags
from scipy.sparse.linalg import spsolve
import static_analysis as S

G, A0 = S.G, S.A0
Mbf = S.Mb_of(S.BENCH['MW']['parts'])
R = 200.0
r = np.geomspace(0.05, R, 1500)
Mb = Mbf(r); gb = G*Mb/r**2
Jv = S.J(gb); gR = gb + Jv; Jp = S.Jprime(gb)
Mp = r**2*Jv/G
rho_p = np.gradient(Mp, r)/(4*math.pi*r**2)
P = cumulative_trapezoid((rho_p*gR)[::-1], -r[::-1], initial=0)[::-1] + rho_p[-1]*gR[-1]*r[-1]/2
sig2R = P/rho_p

# finite-difference check of the baryon acceleration formula
def energy(Mb_arr, Ms_arr, lam):
    gbb = G*Mb_arr/r**2; gs = G*Ms_arr/r**2
    e = (-(gbb+gs)**2 + lam*(gs - S.J(gbb))**2)*r**2/(2*G)
    return np.trapezoid(e, r)
lam_chk = 50.0
Ms_test = Mp*(1+0.05*np.sin(np.log(r)))
i0 = 1000; dm = 1e5; width = 15
pert = np.zeros_like(r); pert[i0:i0+width] = -dm      # move shell mass dm outward across a band
dr_band = r[i0+width]-r[i0]
dE = energy(Mb+pert, Ms_test, lam_chk) - energy(Mb, Ms_test, lam_chk)
force_fd = -dE/(dm*dr_band)          # outward force per unit mass, finite difference
gs_t = G*Ms_test/r**2
rm = slice(i0, i0+width)
force_formula = np.mean(-(gb[rm]+gs_t[rm]) - lam_chk*(gs_t[rm]-Jv[rm])*Jp[rm])
check = dict(finite_difference=float(force_fd), formula=float(force_formula))

def solve(lam, d):
    n = len(r); h = np.diff(r)
    A = np.zeros((n, n)); b = np.zeros(n)
    k = (1+d)*sig2R
    w = 1/(4*math.pi*r**2*rho_p)
    for i in range(1, n-1):
        # d/dr [ w dM' ] at i, central differences on a nonuniform grid
        hm, hp = r[i]-r[i-1], r[i+1]-r[i]
        wp = 0.5*(w[i]+w[i+1]); wm = 0.5*(w[i]+w[i-1])
        cp = 2*wp/(hp*(hm+hp)); cm = 2*wm/(hm*(hm+hp))
        A[i, i+1] += k[i]*cp; A[i, i-1] += k[i]*cm; A[i, i] += -k[i]*(cp+cm)
        A[i, i] += -(lam-1)*G/r[i]**2
        b[i] = d*gR[i]
    A[0, 0] = 1; A[-1, -1] = 1
    dM = np.linalg.solve(A, b)
    dg = G*dM/r**2
    a_b = gR + dg + lam*dg*Jp
    out = {}
    for rr in (10, 20, 50, 100, 150):
        i = np.searchsorted(r, rr)
        out[rr] = dict(baryon_err=float(a_b[i]/gR[i]-1), rar_err=float(dg[i]/gR[i]),
                       predicted=float(-d*Jp[i]*lam/(lam-1)), Jprime=float(Jp[i]))
    return out

res = dict(force_check=check, runs={})
print('force check', check)
for lam in (10.0, 100.0, 1000.0):
    for d in (-0.1, -0.03, 0.03, 0.1):
        key = f'lam={lam:g}, d={d:+.2f}'
        res['runs'][key] = solve(lam, d)
        print(key, ' '.join(f"r{k}: b{v['baryon_err']:+.3f} pred{v['predicted']:+.3f} rar{v['rar_err']:+.4f}"
                            for k, v in res['runs'][key].items()), flush=True)
json.dump(res, open('/tmp/claude-0/c25/stiff_amplification.json', 'w'), indent=1)
