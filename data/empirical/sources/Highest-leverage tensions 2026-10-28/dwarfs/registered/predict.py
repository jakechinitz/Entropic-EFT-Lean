"""Registered dwarf-galaxy predictions: satellite support rule vs LCDM (+ supernova heating).

Observable: the mass inside the 3D half-light radius, M(<r_1/2), r_1/2 = (4/3) R_e, compared with the Wolf et al.
(2010) estimator M_1/2 = 4 sigma_los^2 R_e / G from the Local Volume Database (Pace 2024; apace7/local_volume_database,
data/dwarf_all.csv, columns mass_dynamical_wolf and errors). Structural inputs from the same database:
stellar mass (mass_stellar, log10, V-band M/L = 2), circularized half-light radius (rhalf_sph_physical),
Galactocentric and M31-centric distances.
Star-formation duration t_SF = 13.8 Gyr - tau_90 (lookback time by which 90% of the stars had formed):
Weisz et al. 2015 (ApJ 804, 136) for every dwarf in its table; Read, Walker & Steger 2019 truncation time for Sextans;
Monelli et al. 2010 (Cetus: no stars formed in the last 8 Gyr); Monelli et al. 2010b (Tucana: burst ~13 Gyr ago,
duration <~1 Gyr); Gallart et al. 2021 (Eridanus II: burst at the earliest epoch, FWHM 500 Myr).

Models (all fixed before comparison with the Wolf masses; no parameter is fitted to them):
 NFW   : LCDM halo, M200 from the abundance-matching relation through the eight Read+19 dwarfs (log-linear fit below),
         Dutton & Maccio (2014) concentration, plus half the stellar mass.
 HEAT  : NFW with coreNFW supernova heating (Read et al. 2016): kappa = 0.04, r_c = 1.75 R_e, t_dyn at r_s.
 RULE  : support rule. Host field (Milky Way: M_b = 6e10, C_R = 14; M31: M_b = 1.1e11, C_R = 11; capped law) versus the
         dwarf's own law field at r_1/2. Ratio > 1: retained stock = NFW. Ratio < 1: relaxed stock = exponential law
         of the baryons at r_1/2 plus 0.08 dex (median offset of the 2026-10-26 relaxed runs from the law).
Model uncertainty 0.20 dex in log M_1/2 for every model (halo-mass scatter, relaxation scatter, tides).
"""
import numpy as np, pandas as pd, json, hashlib
G = 4.30091e-6; A0 = 1.2307e-10 / 3.2408e-14; KPC_KMS_GYR = 0.9778; h = 0.7
SIG_MODEL = 0.20; RELAX_OFFSET = 0.08

# Read+19 abundance-matched M200 for the eight classical dSphs (rerun harness values) -> log-linear relation
AM = {'Draco': (2.9e5, 1.8e9), 'UrsaMinor': (2.9e5, 2.8e9), 'Sextans': (4.4e5, 2.0e9), 'Carina': (3.8e5, 8.0e8),
      'LeoII': (7.4e5, 1.6e9), 'Sculptor': (2.3e6, 5.7e9), 'LeoI': (5.5e6, 5.6e9), 'Fornax': (4.3e7, 2.19e10)}
xa = np.log10([v[0] for v in AM.values()]); ya = np.log10([v[1] for v in AM.values()])
AM_B, AM_A = np.polyfit(xa, ya, 1)
def m200_of(ms): return 10**(AM_A + AM_B * np.log10(ms))

TAU90 = {  # lookback time [Gyr] by which 90% of stars formed
 'andromeda_01': 10**9.86 / 1e9, 'andromeda_02': 10**9.75 / 1e9, 'andromeda_03': 10**9.72 / 1e9, 'andromeda_05': 10**9.87 / 1e9,
 'andromeda_06': 10**9.73 / 1e9, 'andromeda_11': 10**10.11 / 1e9, 'andromeda_13': 10**10.1 / 1e9, 'carina_1': 10**9.46 / 1e9,
 'canes_venatici_1': 10**9.92 / 1e9, 'canes_venatici_2': 10**9.92 / 1e9, 'draco_1': 10**10.01 / 1e9, 'fornax_1': 10**9.38 / 1e9,
 'hercules_1': 10**10.1 / 1e9, 'leo_1': 10**9.23 / 1e9, 'leo_2': 10**9.81 / 1e9, 'leo_4': 10**10.05 / 1e9,
 'sculptor_1': 10**10.03 / 1e9, 'ursa_minor_1': 10**9.96 / 1e9, 'sextans_1': 10.6, 'cetus_1': 8.0, 'tucana_1': 12.5,
 'eridanus_2': 13.0}

def law(gN): return gN / (1 - np.exp(-np.sqrt(gN / A0)))
def host_field(D, Mb, C): return min(law(G * Mb / D**2), G * Mb * (1 + C) / D**2)
def mnfw(r, M200, c, r200):
    rs = r200 / c; m = lambda x: np.log(1 + x) - x / (1 + x)
    return M200 * m(r / rs) / m(c)

def predict(row):
    ms = 10**row.mass_stellar; Re = row.rhalf_sph_physical / 1e3; r12 = 4 / 3 * Re
    M200 = m200_of(ms); c = 10**(0.905 - 0.101 * np.log10(M200 * h / 1e12))
    r200 = (3 * M200 / (4 * np.pi * 200 * 136.0))**(1 / 3)          # rho_crit = 136 Msun/kpc^3 (h = 0.7)
    rs = r200 / c
    nfw = mnfw(r12, M200, c, r200) + ms / 2
    tdyn = 2 * np.pi * np.sqrt(rs**3 / (G * mnfw(rs, M200, c, r200))) * KPC_KMS_GYR
    tSF = max(13.8 - TAU90[row.key], 0.0); n = np.tanh(0.04 * tSF / tdyn)
    heat = mnfw(r12, M200, c, r200) * np.tanh(r12 / (1.75 * Re))**n + ms / 2
    gi = law(G * (ms / 2) / r12**2)
    gmw = host_field(row.distance_gc, 6e10, 14); gm31 = host_field(row.distance_m31, 1.1e11, 11)
    ratio = max(gmw, gm31) / gi
    relaxed = (ms / 2) * law(G * (ms / 2) / r12**2) / (G * (ms / 2) / r12**2) * 10**RELAX_OFFSET
    rule = nfw if ratio > 1 else relaxed
    return dict(key=row.key, logMs=float(np.log10(ms)), Re_pc=float(Re * 1e3), M200=float(M200), tSF=float(tSF), n_heat=float(n),
                ratio=float(ratio), cls='retained' if ratio > 1 else 'relaxed',
                logM_NFW=float(np.log10(nfw)), logM_HEAT=float(np.log10(heat)), logM_RULE=float(np.log10(rule)),
                logM_LAW=float(np.log10(relaxed)),
                **{f'sigma_{k}': float(np.sqrt(v * G / (4 * Re))) for k, v in (('NFW', nfw), ('HEAT', heat), ('RULE', rule))})

if __name__ == '__main__':
    d = pd.read_csv('ext/lvdb/data/dwarf_all.csv')
    d = d[d.key.isin(TAU90) & np.isfinite(d.mass_dynamical_wolf)]
    P = [predict(r) for _, r in d.iterrows()]
    reg = dict(created='2026-10-28', am_relation=dict(slope=float(AM_B), intercept=float(AM_A)), sig_model=SIG_MODEL,
               relax_offset=RELAX_OFFSET, predictions=sorted(P, key=lambda p: p['ratio']))
    blob = json.dumps(reg, sort_keys=True, indent=1)
    open('registered_predictions.json', 'w').write(blob)
    print('SHA-256', hashlib.sha256(blob.encode()).hexdigest())
    # comparison with the existing Wolf masses (postdiction for these; the density predictions are the registered test)
    tot = {'NFW': 0, 'HEAT': 0, 'RULE': 0, 'LAW': 0}; disc = {'NFW': 0, 'HEAT': 0, 'RULE': 0, 'LAW': 0}; nd = 0
    print(f"{'key':18s} {'ratio':>6s} {'class':>8s} {'tSF':>5s} {'n':>4s} | {'obs':>5s} {'NFW':>5s} {'HEAT':>5s} {'RULE':>5s} | pulls HEAT RULE")
    for p in reg['predictions']:
        r = d[d.key == p['key']].iloc[0]
        o = r.mass_dynamical_wolf; eo = 0.5 * (r.mass_dynamical_wolf_em + r.mass_dynamical_wolf_ep)
        s = np.hypot(eo, SIG_MODEL)
        z = {m: (o - p['logM_' + m]) / s for m in tot}
        for m in tot: tot[m] += z[m]**2
        sep = abs(p['logM_HEAT'] - p['logM_RULE']) > 2 * SIG_MODEL / np.sqrt(2) * 0.5   # predictions differ by > 0.14 dex
        if sep:
            nd += 1
            for m in tot: disc[m] += z[m]**2
        print(f"{p['key']:18s} {p['ratio']:6.2f} {p['cls']:>8s} {p['tSF']:5.1f} {p['n_heat']:4.2f} | {o:5.2f} {p['logM_NFW']:5.2f} {p['logM_HEAT']:5.2f} {p['logM_RULE']:5.2f} | {z['HEAT']:+5.1f} {z['RULE']:+5.1f}{'  *' if sep else ''}")
    print('chi2 all', len(reg['predictions']), {m: round(v, 1) for m, v in tot.items()})
    print('chi2 discriminating (* , predictions differ > 0.14 dex)', nd, {m: round(v, 1) for m, v in disc.items()})
