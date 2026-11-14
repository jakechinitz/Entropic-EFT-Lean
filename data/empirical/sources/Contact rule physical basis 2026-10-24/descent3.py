"""Contact descent, third version: 3-D particles with central-impulse contacts.

State: positions x (N,3), velocities v (N,3), equal masses.  Gravity: spherical (monopole)
field of stock + static baryons, rebuilt after every drift (kick-drift-kick, dt = 0.1 Myr).
Contacts (every ncont steps):
  - neighbours from a KD-tree: each element proposes with its nearest 3-D neighbour,
    Poisson(k Omega dt_c / 2pi) proposals per element;
  - impulse along the separation n = (x_i - x_j)/|x_i - x_j|:
        v_i += (dw/2) n,   v_j -= (dw/2) n,   dw ~ N(0, 0.3 |v_i - v_j| + 1 km/s)
    This conserves total momentum and total angular momentum exactly, since n is parallel
    to x_i - x_j;
  - kinetic change dK = (m/4)[(w+dw)^2 - w^2], with w = (v_i - v_j).n, is drawn from or
    deposited to the work register (rejected if the register cannot pay);
  - acceptance: the pair's orbit-averaged mismatch potential psi (computed from E and |L|
    in the current spherical potential) decreases.
Gate (optional): carrier-wide mean-subtracted 1-D dispersion inside r200 at or below SIGC.
Logged: RAR offsets, E_mis on [0.5, EMIS_R] kpc and its exact constrained floor
(minimizer.py), stock energy change vs register, exact P and L conservation of contacts.
Usage: python3 descent3.py CASE K REGISTER [N] [T_Gyr] [SIGC] [SEED]
"""
import numpy as np, math, json, sys, time
from numba import njit
from scipy.spatial import cKDTree
from scipy.integrate import cumulative_trapezoid
import static_analysis as S
from descent_sim import build_fields, orbit_avg, interp
from descent2 import eddington_ics
import minimizer as MN

G, A0 = S.G, S.A0
C = 1.0227e-3
EMIS_R = 200.0
FUNC = 'E'   # 'E': quadratic field mismatch; 'D': Bose relative entropy with equipartition cell density

@njit(cache=True)
def gmag(rr, rg, g):
    n = rg.size
    if rr > rg[n-1]: return g[n-1]*(rg[n-1]/rr)**2
    if rr < rg[0]: return g[0]*rr/rg[0]
    return interp(rr, rg, g)

@njit(cache=True)
def kick(x, v, rg, g, h):
    for i in range(x.shape[0]):
        rr = math.sqrt(x[i,0]**2+x[i,1]**2+x[i,2]**2)
        a = -gmag(rr, rg, g)/rr
        for k in range(3): v[i,k] += h*C*a*x[i,k]

@njit(cache=True)
def drift(x, v, dt):
    for i in range(x.shape[0]):
        for k in range(3): x[i,k] += dt*C*v[i,k]

@njit(cache=True)
def phi_at(rr, rg, Phi, g):
    n = rg.size
    if rr > rg[n-1]: return Phi[n-1]*rg[n-1]/rr
    if rr < rg[0]: return Phi[0] - 0.5*g[0]*(rg[0]**2 - rr**2)/rg[0]
    return interp(rr, rg, Phi)

@njit(cache=True)
def EL(xi, vi, rg, Phi, g):
    rr = math.sqrt(xi[0]**2+xi[1]**2+xi[2]**2)
    E = 0.5*(vi[0]**2+vi[1]**2+vi[2]**2) + phi_at(rr, rg, Phi, g)
    Lx = xi[1]*vi[2]-xi[2]*vi[1]; Ly = xi[2]*vi[0]-xi[0]*vi[2]; Lz = xi[0]*vi[1]-xi[1]*vi[0]
    return E, math.sqrt(Lx*Lx+Ly*Ly+Lz*Lz)

@njit(cache=True)
def contacts(x, v, partner, nprop, rg, Phi, g, psi, register, m, seed):
    np.random.seed(seed)
    acc = 0; spent = 0.0
    for i in range(x.shape[0]):
        j = partner[i]
        for p in range(nprop[i]):
            dx0 = x[i,0]-x[j,0]; dx1 = x[i,1]-x[j,1]; dx2 = x[i,2]-x[j,2]
            d = math.sqrt(dx0*dx0+dx1*dx1+dx2*dx2)
            if d == 0: break
            n0 = dx0/d; n1 = dx1/d; n2 = dx2/d
            u0 = v[i,0]-v[j,0]; u1 = v[i,1]-v[j,1]; u2 = v[i,2]-v[j,2]
            w = u0*n0+u1*n1+u2*n2
            dw = np.random.normal()*(0.3*math.sqrt(u0*u0+u1*u1+u2*u2)+1.0)
            dK = 0.25*m*((w+dw)**2 - w*w)          # (mu/2)[(w+dw)^2-w^2], mu = m/2
            if dK > register: continue
            Ei, Li = EL(x[i], v[i], rg, Phi, g); Ej, Lj = EL(x[j], v[j], rg, Phi, g)
            vi = v[i].copy(); vj = v[j].copy()
            vi[0] += 0.5*dw*n0; vi[1] += 0.5*dw*n1; vi[2] += 0.5*dw*n2
            vj[0] -= 0.5*dw*n0; vj[1] -= 0.5*dw*n1; vj[2] -= 0.5*dw*n2
            Ei2, Li2 = EL(x[i], vi, rg, Phi, g); Ej2, Lj2 = EL(x[j], vj, rg, Phi, g)
            if Ei2 >= 0 or Ej2 >= 0: continue
            a0_, _ = orbit_avg(Ei, Li, rg, Phi, psi); b0_, _ = orbit_avg(Ej, Lj, rg, Phi, psi)
            a1_, _ = orbit_avg(Ei2, Li2, rg, Phi, psi); b1_, _ = orbit_avg(Ej2, Lj2, rg, Phi, psi)
            if not (a1_ + b1_ < a0_ + b0_): continue
            v[i] = vi; v[j] = vj
            register -= dK; spent += dK; acc += 1
    return acc, spent

def psi_bose(rg, gb, gs):
    """Functional derivative of F_D = int N Theta D(n || n*) d^3x with n = g_s/g_b and the
    equipartition cell density N Theta = g_b^2 n*(1+n*)/(4 pi G):
        d psi_D / dr = g_b n*(1+n*) [ln(1+1/n) - x],  psi_D(R_out) = 0.
    Near equilibrium this reduces to d psi/dr = J - g_s (the quadratic mismatch)."""
    xg = np.sqrt(gb/A0)
    ns = 1/np.expm1(xg)
    n = np.maximum(gs/gb, 1e-12)
    dpsi = gb*ns*(1+ns)*(np.log1p(1/n) - xg)
    psi = np.zeros_like(rg)
    psi[:-1] = -np.cumsum((0.5*(dpsi[1:]+dpsi[:-1])*np.diff(rg))[::-1])[::-1]
    return psi

def F_bose(rg, gb, gs, rmax):
    xg = np.sqrt(gb/A0); ns = 1/np.expm1(xg); n = np.maximum(gs/gb, 1e-300)
    D = xg*n - ((1+n)*np.log1p(n) - n*np.log(n)) - np.log(-np.expm1(-xg))
    dens = gb**2*ns*(1+ns)/(4*math.pi*G)*D*4*math.pi*rg**2
    dom = rg <= rmax
    return float(np.trapezoid(dens[dom], rg[dom]))

def stock_energy(x, v, m, rg, Mbg):
    r = np.sqrt((x**2).sum(1)); order = np.argsort(r); rs = r[order]
    K = 0.5*m*np.sum(v**2)
    Wself = -np.sum(G*m*np.arange(len(rs))*m/rs)
    gb = G*Mbg/rg**2
    Phib = -cumulative_trapezoid(gb[::-1], -rg[::-1], initial=0)[::-1] - G*Mbg[-1]/rg[-1]
    Pr = np.where(r <= rg[-1], np.interp(r, rg, Phib), -G*Mbg[-1]/r)
    return K + Wself + m*np.sum(Pr)

def to3d(r, vr, L, rng):
    N = r.size
    nhat = rng.normal(size=(N, 3)); nhat /= np.linalg.norm(nhat, axis=1)[:, None]
    t = rng.normal(size=(N, 3)); t -= (t*nhat).sum(1)[:, None]*nhat; t /= np.linalg.norm(t, axis=1)[:, None]
    vt = L/r
    return r[:, None]*nhat, vr[:, None]*nhat + vt[:, None]*t

def run(case, kpo, reg_per_mass, N=4000, T=12.0, sigc=0.0, seed=1, dt=0.1, ncont=20):
    r, vr, L, Mstock, Mbf, Mbtot, halo = eddington_ics(case, N, seed)
    rng = np.random.default_rng(seed+11)
    x, v = to3d(r, vr, L, rng)
    m = Mstock/N
    rg = np.geomspace(0.5, 30*halo['r200'], 2200); Mbg = Mbf(rg)
    Vf = (G*Mbtot*A0)**0.25
    register = reg_per_mass*N*m          # energy units: Msun (km/s)^2
    E0 = stock_energy(x, v, m, rg, Mbg)
    # exact constrained floor of E_mis on the logging domain, for this stock budget
    dom = rg <= EMIS_R
    T_target = rg[dom]**2*S.J(G*Mbg[dom]/rg[dom]**2)/G
    Ystar = MN.minimiser(rg[dom], T_target, Mstock)
    Efloor = MN.emis(rg[dom], Ystar, T_target)
    radii = [5, 10, 20, 50, 100, 200] if halo['r200'] < 700 else [20, 50, 100, 300, 600, 1000]
    nsteps = int(T*1000/dt)
    def fields():
        rr = np.sqrt((x**2).sum(1)); order = np.argsort(rr)
        g, gb, gs, J, Phi, psi, Ms = build_fields(rg, Mbg, rr[order], m, G, A0)
        if FUNC == 'D':
            psi = psi_bose(rg, gb, gs)
        return rr, (g, gb, gs, J, Phi, psi, Ms)
    rr, (g, gb, gs, J, Phi, psi, Ms) = fields()
    hist = []; spent_tot = 0.0; acc_tot = 0; dP_max = 0.0; dL_max = 0.0; t0 = time.time()
    P0 = m*v.sum(0); L0 = m*np.cross(x, v).sum(0)
    for s in range(nsteps):
        kick(x, v, rg, g, 0.5*dt); drift(x, v, dt)
        rr, (g, gb, gs, J, Phi, psi, Ms) = fields()
        kick(x, v, rg, g, 0.5*dt)
        if kpo > 0 and s % ncont == 0:
            gate = True
            if sigc > 0:
                ins = rr < halo['r200']
                vin = v[ins]; sig = math.sqrt(((vin - vin.mean(0))**2).sum(1).mean()/3)
                gate = sig <= sigc
            if gate:
                tree = cKDTree(x); _, idx = tree.query(x, k=2); partner = idx[:, 1].astype(np.int64)
                Om = np.sqrt(np.interp(rr, rg, g)*rr)/rr*C
                nprop = rng.poisson(kpo*Om*(ncont*dt)/(2*math.pi)).astype(np.int64)
                Pb = m*v.sum(0); Lb = m*np.cross(x, v).sum(0)
                acc, spent = contacts(x, v, partner, nprop, rg, Phi, g, psi, register, m, int(seed*7919+s) % 2**31)
                Pa = m*v.sum(0); La = m*np.cross(x, v).sum(0)
                dP_max = max(dP_max, float(np.abs(Pa-Pb).max())); dL_max = max(dL_max, float(np.abs(La-Lb).max()))
                register -= spent; spent_tot += spent; acc_tot += acc
        if s % int(500/dt) == 0 or s == nsteps-1:
            gR = gb + J
            E = stock_energy(x, v, m, rg, Mbg)
            Emis = float(np.trapezoid(((gs-J)**2*rg**2)[dom], rg[dom])/(2*G))
            ins = rr < halo['r200']; vin = v[ins]
            hist.append(dict(t_Gyr=round((s+1)*dt/1000, 3),
                             offsets={q: float(np.log10(np.interp(q, rg, g)/np.interp(q, rg, gR))) for q in radii},
                             Emis=Emis, F_bose=F_bose(rg, gb, gs, EMIS_R), Emis_over_floor=Emis/Efloor if Efloor > 0 else None,
                             dE_stock_Vf2=float((E-E0)/(N*m)/Vf**2), work_Vf2=spent_tot/(N*m)/Vf**2,
                             accepted=acc_tot, sigma_carrier=float(math.sqrt(((vin-vin.mean(0))**2).sum(1).mean()/3)),
                             frac_beyond_r200=float((rr > halo['r200']).mean())))
            h = hist[-1]
            print(f"t={h['t_Gyr']:6.2f} Emis={h['Emis']:.3e} dE={h['dE_stock_Vf2']:+.4f} W={h['work_Vf2']:+.4f} sig={h['sigma_carrier']:.0f} acc={acc_tot} "
                  + ' '.join(f"{k}:{val:+.3f}" for k, val in h['offsets'].items()), flush=True)
    rgrid = np.geomspace(2, 300, 40)
    off = np.log10(np.interp(rgrid, rg, g)/np.interp(rgrid, rg, gb + J))
    P1 = m*v.sum(0); L1 = m*np.cross(x, v).sum(0)
    return dict(case=case, k=kpo, register_per_mass=reg_per_mass, N=N, T=T, sigc=sigc, seed=seed, halo=halo, Vf=Vf,
                Emis_floor=Efloor, offsets_final={float(a): float(b) for a, b in zip(rgrid, off)},
                contact_dP_max=dP_max, contact_dL_max=dL_max,
                momentum_scale=float(m*N*Vf), angmom_scale=float(m*N*Vf*halo['r200']),
                history=hist, runtime_s=time.time()-t0)

if __name__ == '__main__':
    a = sys.argv
    case, kpo, reg = a[1], float(a[2]), float(a[3])
    N = int(a[4]) if len(a) > 4 else 4000; T = float(a[5]) if len(a) > 5 else 12.0
    sigc = float(a[6]) if len(a) > 6 else 0.0; seed = int(a[7]) if len(a) > 7 else 1
    if len(a) > 8: FUNC = a[8]
    res = run(case, kpo, reg, N, T, sigc, seed)
    res['functional'] = FUNC
    tag = '' if FUNC == 'E' else f'_F{FUNC}'
    json.dump(res, open(f'/tmp/claude-0/c25/d3_{case}_k{kpo:g}_reg{reg:g}_N{N}_sig{sigc:g}_s{seed}{tag}.json', 'w'), indent=1)
    print('contact |dP|max / (M Vf) =', res['contact_dP_max']/res['momentum_scale'], ' |dL|max / (M Vf r200) =', res['contact_dL_max']/res['angmom_scale'])
