"""LCDM + supernova dark-matter heating (coreNFW, Read et al. 2016) vs the satellite support rule, on the eight
classical dSphs with GravSphere rho(150 pc) (Read, Walker & Steger 2019).
coreNFW: M(<r) = M_NFW(<r) f^n, f = tanh(r / r_c), r_c = eta R_1/2 (eta = 1.75, R_1/2 = 3D half-light = 1.305 R_e... Read+16 use the
projected half-light radius R_e: r_c = 1.75 R_e), n = tanh(q), q = kappa t_SF / t_dyn, kappa = 0.04,
t_dyn = 2 pi sqrt(r_s^3 / (G M_NFW(r_s))). t_SF = 13.8 Gyr - t_trunc (star formation from the start of the Universe
to its truncation; t_trunc = lookback time at which SF ended, as in Read+19 and the rerun harness).
Halo inputs are the rerun's: M200 (Read+19 abundance matching), c (Dutton & Maccio), r200."""
import numpy as np
G = 4.30091e-6; KPC_KMS_TO_GYR = 0.9778
D = {  # M200, c, r200 [kpc], R_e [kpc], t_trunc [Gyr ago]
 'Sextans': (2.0e9, 15.6, 26.7, 0.695, 10.6), 'Draco': (1.8e9, 15.8, 25.7, 0.221, 11.7), 'UrsaMinor': (2.8e9, 15.1, 29.8, 0.181, 12.4),
 'Carina': (8.0e8, 17.1, 19.6, 0.250, 2.8), 'Sculptor': (5.7e9, 14.0, 37.8, 0.283, 11.8), 'Fornax': (2.19e10, 12.3, 59.2, 0.710, 1.75),
 'LeoII': (1.6e9, 16.0, 24.7, 0.176, 6.3), 'LeoI': (5.6e9, 14.1, 37.6, 0.251, 3.1)}
GS = {'UrsaMinor': (1.53, .35, .32), 'Draco': (2.36, .29, .29), 'Sculptor': (1.49, .28, .23), 'Sextans': (1.28, .34, .29),
      'LeoII': (1.84, .17, .16), 'LeoI': (1.77, .33, .34), 'Carina': (1.16, .20, .22), 'Fornax': (0.79, .27, .19)}
RUN = {'UrsaMinor': (1.31, 32), 'Draco': (0.58, 22), 'Sculptor': (1.30, 23), 'Sextans': (0.31, 8),
       'LeoII': (0.95, 41), 'LeoI': (1.61, 31), 'Carina': (0.38, 35), 'Fornax': (1.50, 13)}   # relaxed rho150, n_shell
RATIO = {'Sextans': 5.52, 'Draco': 2.52, 'UrsaMinor': 2.00, 'Carina': 1.74, 'Sculptor': 0.98, 'Fornax': 0.38, 'LeoII': 0.20, 'LeoI': 0.09}
def mnfw(r, M200, c, r200):
    rs = r200 / c; m = lambda x: np.log(1 + x) - x / (1 + x)
    return M200 * m(r / rs) / m(c)
def rho_shell(Mfun, r1=0.1, r2=0.2):     # mean density in the 100-200 pc shell, as in the rerun's rho150
    return (Mfun(r2) - Mfun(r1)) / (4 / 3 * np.pi * (r2**3 - r1**3))
def term(n, rho, nsh=None):
    r, ep, em = GS[n]
    s2 = (0.434 * 0.5 * (ep + em) / r)**2 + 0.1**2 + ((0.434 / np.sqrt(nsh))**2 if nsh else 0)
    return (np.log10(rho) - np.log10(r))**2 / s2
out = {}
print(f"{'dwarf':10s} {'tSF':>5s} {'tdyn':>5s} {'n':>5s} | {'obs':>5s} {'NFW':>5s} {'heat':>5s} {'rule':>5s} | chi2 NFW heat rule")
tot = {'NFW': 0, 'heat': 0, 'rule': 0}
for k, (M200, c, r200, Re, ttr) in D.items():
    rs = r200 / c
    tdyn = 2 * np.pi * np.sqrt(rs**3 / (G * mnfw(rs, M200, c, r200))) * KPC_KMS_TO_GYR
    tSF = 13.8 - ttr; n = np.tanh(0.04 * tSF / tdyn); rc = 1.75 * Re
    nfw = rho_shell(lambda r: mnfw(r, M200, c, r200)) / 1e8
    heat = rho_shell(lambda r: mnfw(r, M200, c, r200) * np.tanh(r / rc)**n) / 1e8
    rule_rho, rule_ns = (nfw, None) if RATIO[k] > 1 else RUN[k]
    t = {'NFW': term(k, nfw), 'heat': term(k, heat), 'rule': term(k, rule_rho, rule_ns)}
    for m in tot: tot[m] += t[m]
    out[k] = dict(tSF=tSF, tdyn=tdyn, n=n, nfw=nfw, heat=heat, rule=rule_rho)
    print(f"{k:10s} {tSF:5.1f} {tdyn:5.2f} {n:5.2f} | {GS[k][0]:5.2f} {nfw:5.2f} {heat:5.2f} {rule_rho:5.2f} | {t['NFW']:5.2f} {t['heat']:5.2f} {t['rule']:5.2f}")
print('total chi2:', {m: round(v, 2) for m, v in tot.items()})
