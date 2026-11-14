# Three-theory comparison runs (2026-11-08)

These runs fill the MOND and ΛCDM cells of the empirical paper's proposed scoreboard. Each comparison reuses the archived pipeline of the matching stock-model number. Only the gravity model changes. An independent audit reran every script from code and outputs, and its corrections are folded in below.

Headline normalization: a0 = εcH0 = 1.2494e-10 m s^-2. This is the frozen four-parameter fit, H0 = 68.42.

## Scoreboard numbers

| Test | Stock model | MOND | ΛCDM | Source |
|---|---|---|---|---|
| SPARC, 130 galaxies, 2710 pts, 5 km/s floor (penalized χ²) | 3428.0 (k = 0) | 3319.8, a0 fitted to 0.914 (k = 1); 3402.0 at a0 = 1.2 (k = 0) | NFW with ΛCDM priors 2700.7; free NFW 1872.0 (k = 260 for both) | sparc/ |
| SPARC, no floor | 11251.0 | 11119.7 (a0 0.941); 11216.9 at 1.2 | 9585.7 with priors; 8121.6 free | sparc/ |
| Cluster mass at R500 / hydrostatic mass (median of 7 X-COP clusters with stars) | 0.91 (range 0.68–1.21) | 0.66 simple, 0.58 standard (range 0.48–0.75; below 1 in 12 of 12) | 0.94 (cosmic f_b) | clusters/ |
| LMC M(<30 kpc), 10^10 Msun (data 4.7–5.1) | 5.03 | 1.54–1.68 (QUMOND external field, archived) | 6.3 median, 3.7–10.8 over ±0.3 dex halo mass and ±0.11 dex c; ~5.4 if f_b is kept out of the dark component | lmc_ngc628/ |
| LMC M(<50 kpc), 10^10 Msun (data 8.76 +1.94/−1.77) | 8.29 | — | 9.5 median, 5.5–16.4 | lmc_ngc628/ |
| NGC 628 old-disk vertical, χ² (5 dispersions); pull vs rotation | 2.04; −0.2σ | 8.86; −2.9σ (algebraic, stock ν) | 2.01; −0.7σ (abundance-matched NFW; −0.03 to −1.7σ over shifts) | lmc_ngc628/ |
| KiDS isolated lenses, χ² (60 pts, full cov, 8 env amplitudes) | 171.0 at standard c; 146.6 at c × 0.6; 131.7 at c × 0.3 (mass shift +0.2) | **110.5** with no nuisance; 108.5 with a baryon-mass shift | 252.1 at standard c; 154.1 at c × 0.6; 124.3 at c × 0.38, mass +0.24 dex | kids/ |
| Cosmology, CMB + BAO + SN | Δχ² +1.07, 4 + cal params | not run (AeST is the MOND-family fit) | 6 + cal params | frozen_likelihood |
| Crater II σ (km/s; data 2.7 ± 0.3, S5 2.35) | 2.36 (tidal run) | 2.1 (+0.9/−0.6), predicted before measurement (McGaugh 2016) | cuspy NFW needs halo 2 dex below abundance matching | literature |
| Antlia 2 σ (km/s; data 6.0 ± 0.4) | 3.48 (best bound remnant) | 2.8 (+1.3/−0.8), EFE estimate (Ji et al. 2021) | low-c NFW reproduces it; favored over stock by 50–140 | literature |
| Wide binaries | null (parent-carrier rule) | ~20% velocity boost beyond a few kAU | null | literature, contested |

## Cosmology information criteria

N = 613 + 2 + 13 + 1820 = 2448 data points (2 ln N = 15.61). The frozen history has 4 cosmological parameters plus calibration; ΛCDM has 6 plus calibration. Supernova offsets are profiled identically in both models.

| Configuration | Δχ² | ΔAIC | ΔBIC |
|---|---|---|---|
| Dovekie, Σmν = 0.06, nonlinear lensing, calibration free | +1.07 | −2.93 | −14.5 |
| Low-z offset, Σmν = 0, calibration fixed | −0.28 | −4.28 | −15.9 |
| Fitted mixing time (5 parameters), first configuration | +0.85 | −1.15 | −6.95 |

Counting the τ and calibration priors as data moves ΔBIC by 0.002. The prescription inputs that feed the frozen history are not counted as parameters. These are the Renaissance occupation gate, the measured kernels, the 30 km/s post-reionization gate, η*, ε and 5.333.

## Readings

1. **Clusters.** MOND recovers about two thirds of the hydrostatic mass at R500, and falls below it in every cluster. The stock model and ΛCDM both bracket the data. Both are coextensive cohort estimates, and they differ by 3%.
2. **LMC.** The stock model and ΛCDM both reach the stream mass; the external-field QUMOND calculation gives a third of it. The stock model has no halo-mass freedom. ΛCDM spans a factor of 3 over its halo-mass scatter.
3. **NGC 628.** The stock model and abundance-matched NFW tie, at χ² 2.04 and 2.01. Algebraic QUMOND fails at −2.9σ. This is a win over MOND, not over ΛCDM.
4. **SPARC.** The stock law and the MOND exponential RAR are the same function. MOND with a fitted a0 scores lower by 108 (floor 5) to 131 (no floor). Most of the gain at no floor is in the nuisance priors: 117 of 131 in χ², of which inclination is 62, disk M/L 41 and distance 26. At floor 5 the velocity χ² carries 69 of 108. Even MOND at a0 = 1.2e-10 beats the stock law at 1.249, because the data in this pipeline prefer a0 ≈ 0.91–0.94. The stock law never wins an information criterion here:
   - AIC prefers NFW at both floors.
   - BIC prefers free NFW at no floor and free-a0 MOND at floor 5.
   - The stock law beats ΛCDM-prior NFW on BIC at both floors, and free NFW on BIC at floor 5.
   - At no floor χ²/N ≈ 4, so these gaps are not statistically calibrated.
5. **KiDS isolated lenses.** MOND fits best, at 110 with no halo freedom. This agrees with Brouwer et al. 2021 and Mistele et al. 2024. It requires the hot CGM to be counted in the MOND source; the nuis.py MOND rows (188/150) omit that and are superseded by nuis2.py. At standard and mildly reduced concentrations the stock model beats NFW (171 vs 252, 147 vs 154). Both reach about 124–132 only with concentrations near 0.3–0.4 of the c–M relation. There NFW is lower by about 6.5, and the stock minimum is not fully bracketed. The earlier review's 132.7 / 140.3 could not be reproduced exactly. The gap is the same size: 7.6 there, 6.5–8.1 here. The uncapped stock law, with the hot gas boosted the same way, gives 124.3. The theory excludes it through the cluster cohort ratio.
6. **Crater II and Antlia 2.** Crater II is an a priori MOND success. The stock model's Crater II advantage is over cuspy NFW only. On Antlia 2 the stock model (3.5) lies closer to the data than MOND (2.8). Both fall short of 6.0, and low-concentration NFW reproduces it.

## Net position for the scoreboard

- **Stock model beats MOND:** clusters, LMC, NGC 628 vertical, cosmology (MOND has no CMB fit without extra fields), groups and BCGs, Antlia 2 (marginally).
- **MOND beats the stock model:** SPARC (fitted a0 in this pipeline), KiDS isolated lenses, and possibly high-z, where constant a0 gives residual −0.245 against −0.313. Crater II is a tie with MOND.
- **Stock model beats ΛCDM:** parameter count in cosmology (ΔBIC −14.5 at Δχ² +1.07). It predicts Ω_Λ and H0, which ΛCDM fits. It predicts a0, which ΛCDM does not address. SPARC on BIC against prior-constrained halos. KiDS at standard concentrations. Crater II against cuspy NFW.
- **ΛCDM beats the stock model:** Antlia 2, KiDS at its best-fit low concentration (Δχ² ≈ 6.5), and SPARC on raw χ² and AIC.
- **Ties with ΛCDM:** clusters, LMC, NGC 628, CMB/BAO/SN χ².

## Files and paths

Scripts were run in a cloud container. Paths inside them point to that container: `/mnt/user-data/uploads/Sol and Fable/...` is this workspace, and `/home/claude/lens` is `Highest-leverage tensions 2026-10-28/lensing`, with the KiDS data from `Unified empirical program 2026-10-23/data/kids_rar`. `sparc/` uses `Horizon contact audit 2026-10-21/SPARC source` and the archived `galaxy_tests.py`. `lmc_ngc628/ngc628_lcdm.py` imports `Galactic tests/old_disk_vertical.py`. No archived file was modified.

## Addendum: SPARC a0 preference under other priors (sparc/sparc_prior_sens.py, sparc/sparc_split.py)

The table gives the best global a0 for the exponential law, in units of 1e-10 m s^-2, and the χ² cost of fixing a0 at the cosmological 1.249.

| Variant | No floor: a0 best, Δχ² | 5 km/s floor: a0 best, Δχ² |
|---|---|---|
| Baseline (disk M/L 0.5, 0.1 dex) | 0.94, 131 | 0.91, 108 |
| Disk M/L 0.6 | 0.97, 108 | 0.92, 102 |
| Disk M/L 0.4 | 0.92, 157 | 0.91, 112 |
| M/L prior 0.2 dex | 0.97, 95 | 0.90, 102 |
| M/L prior 0.3 dex | 0.98, 80 | 0.90, 94 |
| Inclination prior ×2 | 1.01, 53 | 0.95, 64 |
| Distance prior ×2 | 0.93, 89 | 0.87, 91 |
| All priors ×2 | 1.06, 18 | 0.88, 54 |
| 38 galaxies with TRGB, Cepheid or SN distances | 1.16, 4.9 | 1.00, 28 |
| Same, M/L 0.2 dex | 1.19, 1.8 | 1.00, 26 |

Best a0 by galaxy class, with the Δχ² cost of the cosmological value:

| Class | No floor | 5 km/s floor |
|---|---|---|
| V_flat < 80 km/s (26 galaxies) | 1.00, 13 | 0.90, 19 |
| 80–150 km/s (31) | 1.67, 32 | 1.34, 1.2 |
| V_flat ≥ 150 km/s (43) | 0.77, 186 | 0.84, 93 |
| No flat part (30) | 0.43, 138 | 0.51, 66 |

**Reading**

- Without the velocity floor, the low-a0 preference comes from the nuisance priors and the Hubble-flow distances. Doubling the prior widths cuts the cost to 18. With absolute distances only, the best a0 is 1.16–1.19 and the cosmological value costs 2–5 in χ², within about 1σ.
- With the floor, the preference is steadier (0.87–1.00).
- The galaxy classes disagree with one another by more than any single fit's error: best a0 runs from 0.4–0.5 to 1.3–1.7. Massive galaxies and galaxies without a flat part drive the low value. Intermediate galaxies prefer a value above the cosmological one.
- The scatter between classes, about 0.25 dex, is the real systematic. It matches the drift the paper already reports (0.97 for gas-dominated dwarfs, 1.37 for massive galaxies with absolute distances). The cosmological 1.249 lies inside it.
- The same spread applies to MOND with a fitted a0. Against canonical MOND at 1.2, the stock law is behind by 26 (floor) to 34 (no floor) in χ². That gap is the difference between 1.2 and 1.249.
