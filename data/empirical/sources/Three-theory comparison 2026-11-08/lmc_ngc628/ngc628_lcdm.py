"""NGC 628 old-disk vertical test with an abundance-matched NFW halo (LCDM row), on the archived reduced
vertical model (Galactic tests/old_disk_vertical.py). For each M*, the halo is Moster+13 M200 with the
Dutton-Maccio 2014 concentration (optionally shifted); its round vertical force adds
(V_h^2/R^2)(pi^2/3) h_z^2 to <sigma_z^2>, the same round-term algebra the completion uses.
The rotation constraint is V_flat from baryons + that halo."""
import numpy as np, json
import old_disk_vertical as O
G = O.G
RHO200 = 200 * 3 * (70 / 1e6)**2 / (8 * np.pi * G)            # Msun/pc^3, H in km/s/pc
def moster(lM):
    M1, N, b, g = 10**11.590, 0.0351, 1.376, 0.608; M = 10**lM
    return np.log10(2 * N * M / ((M / M1)**(-b) + (M / M1)**g))
grid = np.linspace(9, 14, 5001)
inv = lambda lms: np.interp(lms, moster(grid), grid)
cdm = lambda lM: 10**(0.905 - 0.101 * (lM - 12 + np.log10(0.7)))
def v2h(R, M, dlogM=0.0, dlogc=0.0):
    lM = inv(np.log10(M * 1e10)) + dlogM; c = cdm(lM) * 10**dlogc
    Mh = 10**lM; r200 = (3 * Mh / (4 * np.pi * RHO200))**(1 / 3); mu = lambda t: np.log1p(t) - t / (1 + t)
    return G * Mh * mu(c * R / r200) / (mu(c) * R)

def run(dlogM=0.0, dlogc=0.0, a0_SI=1.20e-10, hz=397.6, hR_arc=73.4, D=8.6, Vflat=180.0, eVflat=9.0, f_cold=0.15):
    O.a0 = a0_SI / O.kms2_per_pc_to_SI
    pc = D * 1e6 * 4.8481e-6; hR = hR_arc * pc
    Rd = np.array([62, 109, 132, 208, 293.0]) * pc
    sd = np.array([55.4, 50.9, 33.8, 22.6, 17.5]); ed = np.array([6.4, 8.9, 3.3, 2.1, 2.6])
    Sig_at = lambda r: 9.0 * (1 / (1 + np.exp(-(r - 1000) / 300))) * (1 / (1 + np.exp((r - 14000) / 1500)))
    Sig_gas = lambda r: Sig_at(r) + 40.0 * np.exp(-r / 2600.0)
    Rg = np.linspace(100, 30000, 600); v2g = lambda Ro: O.v2_from_sigma(Rg, Sig_gas, Ro)
    v2g_d = v2g(Rd)
    def preds(M):
        S0 = M * 1e10 / (2 * np.pi * hR**2); Sig_s = S0 * np.exp(-Rd / hR)
        gN = (O.v2_expdisk(Rd, S0, hR) + v2g_d) / Rd
        p = O.sigma_models(Rd, Sig_s, Sig_gas(Rd), gN, hz, f_cold=f_cold)
        newt = p['Newton (baryons only)']**2
        p['LCDM NFW'] = np.sqrt(newt + v2h(Rd, M, dlogM, dlogc) / Rd**2 * (np.pi**2 / 3) * hz**2)
        return p
    res = {}
    for m in ['completion', 'QUMOND', 'Newton (baryons only)', 'LCDM NFW']:
        res[m] = O.fit_scale(lambda M, m=m: np.sum(((preds(M)[m] - sd) / ed)**2), 0.2, 15.0)
    Rr = np.linspace(2.2 * hR, 4.0 * hR, 30); v2g_r = v2g(Rr)
    def vflat(M, law):
        S0 = M * 1e10 / (2 * np.pi * hR**2); v2b = O.v2_expdisk(Rr, S0, hR) + v2g_r; gN = v2b / Rr
        if law == 'lcdm': return np.mean(np.sqrt(v2b + v2h(Rr, M, dlogM, dlogc)))
        return np.mean(np.sqrt(Rr * O.nu(gN / O.a0) * gN))
    out = {}
    for m in res:
        law = 'lcdm' if m == 'LCDM NFW' else 'nu'
        brc, _, lo, hi = O.fit_scale(lambda M: ((vflat(M, law) - Vflat) / eVflat)**2, 0.2, 15.0)
        b, cmin, slo, shi = res[m]
        pull = (b - brc) / np.hypot(0.5 * (shi - slo), 0.5 * (hi - lo))
        out[m] = dict(Mstar_sigma=b, Mstar_sigma_range=[slo, shi], chi2=cmin, Mstar_rotation=brc, Mstar_rotation_range=[lo, hi], pull=pull)
    return out

allres = {}
for lab, kw in [('a0_1.2588_paper', dict(a0_SI=1.2588288653080082e-10)), ('a0_1.249_headline', dict(a0_SI=1.2494e-10)),
                ('halo_-0.3dex', dict(a0_SI=1.2494e-10, dlogM=-0.3)), ('halo_+0.3dex', dict(a0_SI=1.2494e-10, dlogM=0.3)),
                ('c_x0.6', dict(a0_SI=1.2494e-10, dlogc=np.log10(0.6)))]:
    r = run(**kw); allres[lab] = r
    print(lab); [print(f'   {m:22s} M*={v["Mstar_sigma"]:.2f} chi2={v["chi2"]:.2f}  rot={v["Mstar_rotation"]:.2f}  pull={v["pull"]:+.2f}') for m, v in r.items()]
json.dump(allres, open('ngc628_lcdm.json', 'w'), indent=1)
