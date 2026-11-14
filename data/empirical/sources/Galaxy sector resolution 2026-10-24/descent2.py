"""Contact descent, second version, after the independent audit.

Changes from descent_sim.py
  - equilibrium initial conditions: isotropic Eddington sampling of a tapered NFW stock
    (Kazantzidis taper beyond r200) in the stock + static-baryon potential;
  - self-consistent kick-drift-kick: the field is rebuilt after every drift (dt = 0.1 Myr);
  - contact rate per orbit: particle i makes Poisson(k Omega_i dt_c / 2 pi) proposals per
    contact interval, Omega = sqrt(g/r), so outskirts relax on their own orbital clock;
  - the stock energy K + W_b + W_self is measured directly;
  - optional gate SIGC (km/s): contacts only while the carrier-wide stock dispersion (median
    1-D dispersion inside r200) is at or below SIGC.  The gate is re-evaluated as the
    descent heats the stock.
Contact rule and register as in descent_sim.py (pair energy exchange at fixed L, accepted when
the pair's orbit-averaged psi decreases, register exchange w symmetric, w > 0 bounded by the
register).
Usage: python3 descent2.py CASE K_PER_ORBIT REGISTER [N] [T_Gyr] [SIGC] [SEED]
"""
import numpy as np, math, json, sys, time
from numba import njit
from scipy.integrate import cumulative_trapezoid
import static_analysis as S
from descent_sim import build_fields, orbit_avg, interp

G, A0 = S.G, S.A0
C = 1.0227e-3          # (km/s) x Myr -> kpc

@njit(cache=True)
def gfield(x, rg, g):
    n = rg.size
    if x > rg[n-1]:
        return g[n-1]*(rg[n-1]/x)**2      # Keplerian beyond the grid
    return interp(x, rg, g)

@njit(cache=True)
def kick(vr, r, L, rg, g, h):
    for i in range(r.size):
        vr[i] += h*C*(-gfield(r[i], rg, g) + L[i]*L[i]/r[i]**3)

@njit(cache=True)
def drift(r, vr, rmin, dt):
    for i in range(r.size):
        r[i] += dt*C*vr[i]
        if r[i] < rmin:
            r[i] = 2*rmin - r[i]; vr[i] = -vr[i]

@njit(cache=True)
def contacts(r, vr, L, order, nprop_each, rg, Phi, psi, register, wscale, seed, sigloc, sigc):
    np.random.seed(seed)
    n = r.size
    acc = 0; spent = 0.0
    for k in range(n-1):
        i = order[k]; j = order[k+1]
        for p in range(nprop_each[k]):
            if sigc > 0 and interp(r[i], rg, sigloc) > sigc: break
            Ei = 0.5*(vr[i]**2 + L[i]**2/r[i]**2) + interp(r[i], rg, Phi)
            Ej = 0.5*(vr[j]**2 + L[j]**2/r[j]**2) + interp(r[j], rg, Phi)
            s2 = 0.5*(vr[i]**2+vr[j]**2) + 1.0
            d = np.random.normal()*0.3*s2
            w = np.random.normal()*wscale*s2
            if w > register: w = register
            Ei2 = Ei + d + 0.5*w; Ej2 = Ej - d + 0.5*w
            vi2 = 2*(Ei2 - interp(r[i], rg, Phi)) - L[i]**2/r[i]**2
            vj2 = 2*(Ej2 - interp(r[j], rg, Phi)) - L[j]**2/r[j]**2
            if vi2 <= 0 or vj2 <= 0 or Ei2 >= 0 or Ej2 >= 0: continue
            pi0, _ = orbit_avg(Ei, L[i], rg, Phi, psi)
            pj0, _ = orbit_avg(Ej, L[j], rg, Phi, psi)
            pi1, _ = orbit_avg(Ei2, L[i], rg, Phi, psi)
            pj1, _ = orbit_avg(Ej2, L[j], rg, Phi, psi)
            if not (pi1 + pj1 < pi0 + pj0): continue
            vr[i] = math.copysign(math.sqrt(vi2), vr[i])
            vr[j] = math.copysign(math.sqrt(vj2), vr[j])
            acc += 1; spent += w; register -= w
    return acc, spent

def sigma_profile(r, vr, L, rg):
    edges = np.geomspace(rg[0], rg[-1], 41)
    v2 = vr**2 + (L/r)**2
    idx = np.clip(np.searchsorted(edges, r)-1, 0, 39)
    s = np.array([math.sqrt(v2[idx == k].mean()/3) if (idx == k).sum() > 5 else np.nan for k in range(40)])
    mid = np.sqrt(edges[1:]*edges[:-1]); ok = np.isfinite(s)
    return np.interp(rg, mid[ok], s[ok])

def eddington_ics(case, N, seed):
    b = S.BENCH[case]; parts = b['parts']; Mbf = S.Mb_of(parts)
    Mbtot = sum(p[1] for p in parts)
    M200 = b.get('M200') or S.moster_M200(Mbtot)
    c, r200, rs, rhos = S.nfw_params(M200, b.get('dc', 0.0))
    rd = 0.1*r200
    eps = -(1+3*c)/(1+c) + r200/rd
    r = np.geomspace(1e-3, 8*r200, 6000)
    x = r/rs
    rho = np.where(r <= r200, rhos/(x*(1+x)**2),
                   rhos/(c*(1+c)**2)*(r/r200)**eps*np.exp(-(r-r200)/rd))
    Ms = cumulative_trapezoid(4*math.pi*r**2*rho, r, initial=0) + 4/3*math.pi*r[0]**3*rho[0]
    norm = 0.84*M200/Ms[-1]          # total stock (taper included) = 0.84 M200
    rho = rho*norm; Ms = Ms*norm
    Mt = Ms + Mbf(r)
    g = G*Mt/r**2
    # Psi = -Phi, Phi(inf) = -G Mt(R)/R beyond the grid
    Psi = cumulative_trapezoid(g[::-1], -r[::-1], initial=0)[::-1] + G*Mt[-1]/r[-1]
    # Eddington f(E) = 1/(sqrt8 pi^2) d/dE int_0^E (drho/dPsi) dPsi / sqrt(E - Psi)
    P = Psi[::-1]; R = rho[::-1]
    dRdP = np.gradient(R, P)
    Eg = np.geomspace(P[0]*1.0001, P[-1], 800)
    F = np.empty_like(Eg)
    for k, E in enumerate(Eg):
        m = P < E
        u = np.sqrt(np.maximum(E - P[m], 0))     # substitute Psi = E - u^2
        F[k] = np.trapezoid((dRdP[m]*2)[::-1], u[::-1]) if m.sum() > 2 else 0.0
    f = np.maximum(np.gradient(F, Eg)/(math.sqrt(8)*math.pi**2), 0)
    rng = np.random.default_rng(seed)
    cm = Ms/Ms[-1]
    rr = np.interp(rng.random(N), cm, r)
    vr = np.empty(N); L = np.empty(N)
    for i in range(N):
        ps = np.interp(rr[i], r, Psi)
        v = np.linspace(0, math.sqrt(2*ps), 200)[1:]
        p = v**2*np.interp(ps - v**2/2, Eg, f, left=0)
        if p.sum() <= 0: vv = 0.5*math.sqrt(2*ps)
        else:
            cp = np.cumsum(p); vv = np.interp(rng.random()*cp[-1], cp, v)
        mu = rng.uniform(-1, 1)
        vr[i] = vv*mu; L[i] = rr[i]*vv*math.sqrt(1-mu*mu)
    return rr, vr, L, Ms[-1], Mbf, Mbtot, dict(M200=M200, c=c, r200=r200, rs=rs)

def stock_energy(r, vr, L, m, rg, Mbg):
    order = np.argsort(r); rs_ = r[order]
    K = 0.5*m*np.sum(vr**2 + (L/r)**2)
    Menc = m*np.arange(len(rs_))
    Wself = -np.sum(G*Menc*m/rs_)
    gb = G*Mbg/rg**2
    Phib = cumulative_trapezoid(gb[::-1], -rg[::-1], initial=0)[::-1] - G*Mbg[-1]/rg[-1]
    Phi_r = np.where(r <= rg[-1], np.interp(r, rg, Phib), -G*Mbg[-1]/np.maximum(r, 1e-9))
    Wb = m*np.sum(Phi_r)
    return K + Wself + Wb

def run(case, kpo, register_per_mass, N=4000, T=12.0, sigc=0.0, seed=1, dt=0.1, ncont=20):
    r, vr, L, Mstock, Mbf, Mbtot, halo = eddington_ics(case, N, seed)
    m = Mstock/N
    rg = np.geomspace(0.5, 30*halo['r200'], 2200); Mbg = Mbf(rg)
    Vf = (G*Mbtot*A0)**0.25
    register = register_per_mass*N
    wscale = 0.05 if register_per_mass > 0 else 0.0
    E0 = stock_energy(r, vr, L, m, rg, Mbg)
    nsteps = int(T*1000/dt)
    order = np.argsort(r)
    g, gb, gs, J, Phi, psi, Ms = build_fields(rg, Mbg, r[order], m, G, A0)
    radii = [5, 10, 20, 50, 100, 200] if halo['r200'] < 700 else [20, 50, 100, 300, 600, 1000]
    hist = []; spent_tot = 0.0; acc_tot = 0; t0 = time.time(); sig_hist = []
    rng = np.random.default_rng(seed+7)
    for s in range(nsteps):
        kick(vr, r, L, rg, g, 0.5*dt)
        drift(r, vr, rg[0], dt)
        order = np.argsort(r)
        g, gb, gs, J, Phi, psi, Ms = build_fields(rg, Mbg, r[order], m, G, A0)
        kick(vr, r, L, rg, g, 0.5*dt)
        if kpo > 0 and s % ncont == 0:
            # Omega [1/Myr] = v_c/r with v_c in km/s, r in kpc: (km/s)/kpc * C
            Om = np.sqrt(np.interp(r[order], rg, g)*r[order])/r[order]*C
            lam = kpo*Om*(ncont*dt)/(2*math.pi)
            nprop = rng.poisson(lam).astype(np.int64)
            if sigc > 0:
                # carrier-wide gate: median 1-D stock dispersion inside r200
                inside = r < halo['r200']
                v2 = vr[inside]**2 + (L[inside]/r[inside])**2
                sig_car = math.sqrt(np.median(v2)/3)
                gate_open = sig_car <= sigc
                sig_hist.append(sig_car)
            else:
                gate_open = True
            if gate_open:
                acc, spent = contacts(r, vr, L, order, nprop, rg, Phi, psi, register, wscale,
                                      int(seed*1000003 + s) % 2**31, np.zeros_like(rg), 0.0)
            else:
                acc, spent = 0, 0.0
            register -= spent; spent_tot += spent; acc_tot += acc
        if s % int(500/dt) == 0 or s == nsteps-1:
            gR = gb + J
            E = stock_energy(r, vr, L, m, rg, Mbg)
            hist.append(dict(t_Gyr=round((s+1)*dt/1000, 3),
                             offsets={rr: float(np.log10(np.interp(rr, rg, g)/np.interp(rr, rg, gR))) for rr in radii},
                             dE_stock_Vf2=float((E-E0)/(N*m)/Vf**2), work_Vf2=spent_tot/N/Vf**2,
                             accepted=acc_tot, frac_beyond_r200=float((r > halo['r200']).mean()),
                             sigma_carrier=float(sig_hist[-1]) if sig_hist else None))
            print(f"t={hist[-1]['t_Gyr']:6.2f} sig={hist[-1]['sigma_carrier'] or 0:5.0f} dE={hist[-1]['dE_stock_Vf2']:+.3f} W={hist[-1]['work_Vf2']:+.3f} acc={acc_tot} out={hist[-1]['frac_beyond_r200']:.3f} "
                  + ' '.join(f"{k}:{v:+.3f}" for k, v in hist[-1]['offsets'].items()), flush=True)
    gR = gb + J
    rgrid = np.geomspace(2, 300, 40)
    off = np.log10(np.interp(rgrid, rg, g)/np.interp(rgrid, rg, gR))
    tob = {float(x): float((np.interp(x, rg, Ms)+np.interp(x, rg, Mbg))/np.interp(x, rg, Mbg)) for x in (100, 300, 600, 1000, 1500)}
    return dict(case=case, k_per_orbit=kpo, register_per_mass=register_per_mass, N=N, T=T, sigc=sigc, seed=seed,
                dt=dt, halo=halo, Vf=Vf, offsets_final={float(a): float(b) for a, b in zip(rgrid, off)},
                total_over_baryon=tob, history=hist, runtime_s=time.time()-t0)

if __name__ == '__main__':
    a = sys.argv
    case, kpo, reg = a[1], float(a[2]), float(a[3])
    N = int(a[4]) if len(a) > 4 else 4000
    T = float(a[5]) if len(a) > 5 else 12.0
    sigc = float(a[6]) if len(a) > 6 else 0.0
    seed = int(a[7]) if len(a) > 7 else 1
    res = run(case, kpo, reg, N, T, sigc, seed)
    json.dump(res, open(f'/tmp/claude-0/c25/d2_{case}_k{kpo:g}_reg{reg:g}_N{N}_sig{sigc:g}_s{seed}.json', 'w'), indent=1)
