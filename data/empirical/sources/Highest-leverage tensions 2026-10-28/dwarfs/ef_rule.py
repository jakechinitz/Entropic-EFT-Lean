"""Satellite activity rule test: a satellite's own cells are active (its stock relaxes) only where its own
law field dominates the host field; where the host field dominates, the stock keeps its pre-infall allocation.

Inputs
- Classical dSph structural data (McConnachie 2012): Galactocentric distance, stellar mass, projected half-light radius.
- Milky Way field: the capped RAR of M_b = 6e10 Msun with C_R = 14 (Appendix O.3), a0 = 1.2307e-10 m/s^2.
- rho(150 pc) values per dwarf from the 2026-10-26 best-fit rerun (runs/dsph/*.json, harness dsph_W.py):
  'nfw' = abundance-matched NFW (Read+2019 M200, Dutton & Maccio c) = retained stock, no contacts;
  'relaxed' = paper work register (0.9 V_f^2), mean of the last three snapshots, with its shell count.
- GravSphere rho(150 pc) and errors (Read+2019), as in score.py of that rerun.
The score is the rerun's: s^2 = (0.434 * mean err / rho)^2 + (0.434/sqrt(n_shell))^2 + 0.1^2.
"""
import numpy as np
G = 4.30091e-6; A0 = 1.2307e-10 / 3.2408e-14          # (km/s)^2 / kpc
DSPH = {  # D_GC [kpc], M* [Msun], R_e [kpc]
 'Draco': (76, 2.9e5, 0.221), 'UrsaMinor': (78, 2.9e5, 0.181), 'Sculptor': (86, 2.3e6, 0.283),
 'Sextans': (89, 4.4e5, 0.695), 'Carina': (107, 3.8e5, 0.250), 'Fornax': (149, 2.0e7, 0.710),
 'LeoII': (233, 7.4e5, 0.176), 'LeoI': (254, 5.5e6, 0.251)}
GS = {'UrsaMinor': (1.53, .35, .32), 'Draco': (2.36, .29, .29), 'Sculptor': (1.49, .28, .23), 'Sextans': (1.28, .34, .29),
      'LeoII': (1.84, .17, .16), 'LeoI': (1.77, .33, .34), 'Carina': (1.16, .20, .22), 'Fornax': (0.79, .27, .19)}
# rho150 [1e8 Msun/kpc^3]: (nfw, relaxed, n_shell of relaxed run)
RUN = {'UrsaMinor': (1.78, 1.31, 32), 'Draco': (1.60, 0.58, 22), 'Sculptor': (2.11, 1.30, 23), 'Sextans': (1.64, 0.31, 8),
       'LeoII': (1.55, 0.95, 41), 'LeoI': (2.10, 1.61, 31), 'Carina': (1.29, 0.38, 35), 'Fornax': (2.82, 1.50, 13)}
OFF_OBS = {'Draco': 0.70, 'UrsaMinor': 0.73, 'Sculptor': 0.25, 'Sextans': 0.49, 'LeoII': 0.21, 'Carina': 0.36, 'LeoI': 0.04, 'Fornax': -0.20}

def law(gN): return gN / (1 - np.exp(-np.sqrt(gN / A0)))
def g_mw(D, Mb=6e10, C=14):
    return min(law(G * Mb / D**2), G * Mb * (1 + C) / D**2)
def ratio(n):
    D, M, Re = DSPH[n]; r = 1.305 * Re
    return g_mw(D) / law(G * (M / 2) / r**2)
def term(n, rho, nsh):
    r, ep, em = GS[n]
    s = np.sqrt((0.434 * 0.5 * (ep + em) / r)**2 + (0.434 / np.sqrt(max(nsh, 1)))**2 + 0.1**2)
    return ((np.log10(rho) - np.log10(r)) / s)**2

if __name__ == '__main__':
    print(f"{'dwarf':10s} {'g_ext/g_int':>11s} {'class':>9s} {'obs':>5s} {'NFW':>5s} {'relax':>6s} {'chi2 NFW':>9s} {'chi2 relax':>11s} {'RAR off obs':>12s}")
    for n in sorted(DSPH, key=ratio, reverse=True):
        x = ratio(n); nfw, rel, ns = RUN[n]
        print(f"{n:10s} {x:11.2f} {'external' if x > 1 else 'internal':>9s} {GS[n][0]:5.2f} {nfw:5.2f} {rel:6.2f} "
              f"{term(n, nfw, 1e9):9.2f} {term(n, rel, ns):11.2f} {OFF_OBS[n]:+12.2f}")
    allN = sum(term(n, RUN[n][0], 1e9) for n in DSPH); allR = sum(term(n, RUN[n][1], RUN[n][2]) for n in DSPH)
    print(f"\nall retained (plain NFW): chi2 = {allN:.2f};  all relaxed (paper register): chi2 = {allR:.2f}")
    for thr in (0.5, 0.75, 1.0, 1.5, 2.0):
        c = sum(term(n, RUN[n][0], 1e9) if ratio(n) > thr else term(n, RUN[n][1], RUN[n][2]) for n in DSPH)
        print(f"rule, retained where g_ext/g_int > {thr}: chi2 = {c:.2f}")
    # rank correlation of the observed RAR offset with the dominance ratio
    from scipy.stats import spearmanr
    rho_s, p = spearmanr([ratio(n) for n in DSPH], [OFF_OBS[n] for n in DSPH])
    print(f"Spearman(g_ext/g_int, observed RAR offset) = {rho_s:.2f} (p = {p:.3f}, n = 8)")
    # other systems
    for name, ge, M, r in [('LMC (r = 8 kpc)', g_mw(50), 3e9, 8.0), ('NGC 5291 TDG (parent 1.5e11 at 60 kpc)', law(G * 1.5e11 / 60**2), 1e9, 3.0)]:
        print(f"{name}: g_ext/g_int = {ge / law(G * M / r**2):.2f}")
