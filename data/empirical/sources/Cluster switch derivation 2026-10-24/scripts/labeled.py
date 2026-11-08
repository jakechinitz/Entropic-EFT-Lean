"""Carrier-labelled contact rule on GPT's observed-cluster setup.

Rule (derived switch):
  * cells exist only on the central carrier's support r < r_d, where condensed (stellar)
    baryons dominate the enclosed baryons (X-COP data);
  * the carrier's occupation counts only stock bound to the carrier,
    n = g_own / g_rec, with g_rec from the stellar profile and g_own from bound particles;
  * a particle's free-energy derivative is psi_own (orbit averaged) if it is bound to the
    carrier and inside the support, and 0 otherwise (F does not depend on unattached stock);
  * the work register is the cell energy of the support (derived, per unit cluster stock).
Everything else (initial particles, gravity, integrator, impulses, register debit) is
GPT's evolve.py with Claude's archived kernel.
usage: python3 labeled.py CLUSTER K REGSPEC T LABEL N [mode]
mode = labeled (default) | support (support-gated psi on all stock, for comparison)
"""
import sys, json, math
from pathlib import Path
import numpy as np
from numba import njit
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE)); sys.path.insert(0, str(HERE/'source_snapshot'))
import evolve, descent3 as D
from descent_sim import orbit_avg
G, A0 = D.G, D.A0
CAR = json.loads((HERE/'carriers.json').read_text())

@njit(cache=True)
def interp1(xq, xs, ys):
    if xq <= xs[0]: return ys[0]
    if xq >= xs[-1]: return ys[-1]
    i = np.searchsorted(xs, xq) - 1
    t = (xq - xs[i])/(xs[i+1]-xs[i]); return ys[i] + t*(ys[i+1]-ys[i])

@njit(cache=True)
def eP(xi, vi, rP, phiP, rd):
    rr = math.sqrt(xi[0]**2+xi[1]**2+xi[2]**2)
    if rr >= rd: return 1.0
    return 0.5*(vi[0]**2+vi[1]**2+vi[2]**2) + interp1(rr, rP, phiP)

@njit(cache=True)
def psi_eff(xi, vi, rg, Phi, g, psi, rP, phiP, rd):
    if eP(xi, vi, rP, phiP, rd) >= 0: return 0.0
    E, L = D.EL(xi, vi, rg, Phi, g)
    a, _ = orbit_avg(E, L, rg, Phi, psi)
    if a != a: return 0.0
    return a

@njit(cache=True)
def contacts_labeled(x, v, partner, nprop, rg, Phi, g, psi, register, m, seed, rP, phiP, rd):
    np.random.seed(seed)
    acc = 0; spent = 0.0
    for i in range(x.shape[0]):
        j = partner[i]
        ri = math.sqrt(x[i,0]**2+x[i,1]**2+x[i,2]**2); rj = math.sqrt(x[j,0]**2+x[j,1]**2+x[j,2]**2)
        if ri >= rd or rj >= rd: continue            # cells only on the support
        for p in range(nprop[i]):
            dx0 = x[i,0]-x[j,0]; dx1 = x[i,1]-x[j,1]; dx2 = x[i,2]-x[j,2]
            d = math.sqrt(dx0*dx0+dx1*dx1+dx2*dx2)
            if d == 0: break
            n0 = dx0/d; n1 = dx1/d; n2 = dx2/d
            u0 = v[i,0]-v[j,0]; u1 = v[i,1]-v[j,1]; u2 = v[i,2]-v[j,2]
            w = u0*n0+u1*n1+u2*n2
            dw = np.random.normal()*(0.3*math.sqrt(u0*u0+u1*u1+u2*u2)+1.0)
            dK = 0.25*m*((w+dw)**2 - w*w)
            if dK > register: continue
            vi = v[i].copy(); vj = v[j].copy()
            vi[0] += 0.5*dw*n0; vi[1] += 0.5*dw*n1; vi[2] += 0.5*dw*n2
            vj[0] -= 0.5*dw*n0; vj[1] -= 0.5*dw*n1; vj[2] -= 0.5*dw*n2
            Ei2, _ = D.EL(x[i], vi, rg, Phi, g); Ej2, _ = D.EL(x[j], vj, rg, Phi, g)
            if Ei2 >= 0 or Ej2 >= 0: continue
            before = psi_eff(x[i], v[i], rg, Phi, g, psi, rP, phiP, rd) + psi_eff(x[j], v[j], rg, Phi, g, psi, rP, phiP, rd)
            after = psi_eff(x[i], vi, rg, Phi, g, psi, rP, phiP, rd) + psi_eff(x[j], vj, rg, Phi, g, psi, rP, phiP, rd)
            if not (after < before): continue
            v[i] = vi; v[j] = vj
            register -= dK; spent += dK; acc += 1
    return acc, spent

def psi_own(rg, grec, gown, rd):
    xg = np.sqrt(np.maximum(grec, 1e-30)/A0); ns = 1/np.expm1(xg)
    n = np.maximum(gown/np.maximum(grec, 1e-30), 1e-12)
    dpsi = grec*ns*(1+ns)*(np.log1p(1/n) - xg)
    dpsi = np.where(rg <= rd, dpsi, 0.0)
    psi = np.zeros_like(rg)
    psi[:-1] = -np.cumsum((0.5*(dpsi[1:]+dpsi[:-1])*np.diff(rg))[::-1])[::-1]
    return psi

if __name__ == '__main__':
    name, k, regspec, T, label, N = sys.argv[1], float(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4]), sys.argv[5], int(sys.argv[6])
    mode = sys.argv[7] if len(sys.argv) > 7 else 'labeled'
    c = CAR[name]; rd = c['rd']; rP = np.array(c['r']); phiP = np.array(c['phi']); Mrec = np.array(c['Mrec'])
    STATE = {}
    orig_psi = D.psi_bose; orig_contacts = D.contacts
    def psi_patch(rg, gb, gs):
        STATE['rg'] = rg
        return np.zeros_like(rg)      # replaced inside contacts
    def contacts_patch(x, v, partner, np_, rg, Phi, g, psi, register, m, seed):
        rr = np.linalg.norm(x, axis=1)
        grec = G*np.interp(rg, rP, Mrec, right=Mrec[-1])/rg**2
        if mode == 'labeled':
            bound = np.array([eP(x[i], v[i], rP, phiP, rd) < 0 for i in range(len(x))])
            Mown = m*np.searchsorted(np.sort(rr[bound]), rg, side='right')
            ps = psi_own(rg, grec, G*Mown/rg**2, rd)
            return contacts_labeled(x, v, partner, np_, rg, Phi, g, ps, register, m, seed, rP, phiP, rd)
        else:
            Ms = m*np.searchsorted(np.sort(rr), rg, side='right')
            ps = psi_own(rg, grec, G*Ms/rg**2, rd)
            return orig_contacts(x, v, partner, np_, rg, Phi, g, ps, register, m, seed)
    D.psi_bose = psi_patch; D.contacts = contacts_patch
    evolve.run(name, k=k, N=N, T=T, seed=1, dt=.1, regspec=regspec, label=label, force='conservative', softening=5.)
