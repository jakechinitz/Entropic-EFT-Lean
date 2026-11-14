# Crater II and Antlia 2 with the LMC included (post hoc)

Date: 2026-09-27. This check adds the LMC and the Milky Way's reflex motion to the comparison in `RESULTS_stock_vs_LCDM.md`. Everything else is unchanged: the same satellites, N-body code, likelihood and progenitor priors.

## Setup

**LMC models.**
- **Stock:** Plummer baryons of 3e9 M☉ (b = 1.5 kpc) plus their retained stock, capped at 34 × 3e9 = 1.02e11. The resulting LMC has M(<30) = 5.0e10, M(<50) = 8.3e10 and v_c(8.7 kpc) = 87 km/s, all unfitted. The observed v_c(8.7 kpc) is 91.7.
- **ΛCDM:** a Hernquist sphere of 1.38e11 with a = 16.1 kpc, chosen so that v_c(8.7 kpc) = 91.7 (the Erkal et al. 2019 convention). It gives M(<30) = 5.8e10 and M(<50) = 7.9e10.

**Dynamics.**
- The Milky Way, the LMC and the satellite are integrated back 8 Gyr in an inertial frame in which the Milky Way is at rest at the origin today.
- The Milky Way feels the LMC's field at its centre and the LMC feels the Milky Way's field. The satellite feels both.
- Chandrasekhar friction acts on the LMC, computed from each model's Milky Way density with ln Λ = ln(r/(1.6 × 16 kpc)).
- LMC today: RA 80.894, Dec −69.756, D 49.59 kpc, proper motion (1.910, 0.229) mas/yr, v_los 262.2 km/s.

**Satellites.**
- The N-body runs use the same initial conditions as before, inside the time-dependent Milky Way + LMC field.
- Each run starts at an apocentre one, two or three pericentres back and is observed today.
- Crater II under ΛCDM has only two apocentres in the last 8 Gyr, so it has two infall ages.
- ΛCDM halo offsets: 0, −0.3, −0.6 and −0.9 dex for Antlia 2; −0.3, −0.9, −1.5 and −2.1 dex for Crater II.

## Orbits

The LMC pulls the Milky Way toward it by about 35 km/s over the last gigayear; Brooks et al. 2026 measure a reflex of 38.6. This shrinks both dwarfs' most recent pericentres, in both models:

| | Static Milky Way | With LMC, stock | With LMC, ΛCDM |
|---|---|---|---|
| Antlia 2 last pericentre | 36.7 / 34.2 kpc | 27.8 kpc (0.79 Gyr ago) | 25.9 kpc |
| Crater II last pericentre | 41.1 / 38.4 kpc | 25.3 kpc (1.68 Gyr ago) | 24.9 kpc |

In the static column, the first value is the theory Milky Way and the second the ΛCDM one.

## Results

**Antlia 2** (σ = 6.0 ± 0.4 observed).
- **Stock:** 5 of 27 states survive. The best has σ = 3.48, R_h = 2.41 and M* = 9.4e5, and every surviving state has σ between 1.9 and 3.5. Z falls from 1.45e-10 without the LMC to 1.8e-11.
- **ΛCDM:** the best states are at −0.6 to −0.9 dex, with σ = 6.8 to 8.0, R_h = 2.4 to 2.7 and M* = 3.4 to 6.1e5.
- **Bayes factor, stock/ΛCDM:** 0.019 with 0.3 dex halo scatter and 0.007 with 0.5 dex. ΛCDM is now favoured by 50 to 140. With Torrealba's σ = 5.71 ± 1.08, the stock is favoured by 22 to 37.

**Crater II** (σ = 2.7 ± 0.3 observed).
- **Stock:** Z = 3.5e-5, up from 1.2e-5. The best state starts with 2× today's stars at 0.7 R_h and has σ = 2.36, R_h = 0.86, M* = 3.2e5 and a tail fraction of 0.23. The next best starts with 4× today's stars at 1.0 R_h and has σ = 2.18, R_h = 1.24, M* = 4.4e5 and a tail fraction of 0.38. Only first-pericentre progenitors survive, so Crater II must have fallen in within about the last 2.8 Gyr.
- **ΛCDM:** it still needs −2.1 dex (log M_h ≈ 7.4–7.7) to reach σ ≈ 3.2 to 3.5, and R_h then shrinks to 0.76 to 0.78.
- **Bayes factor, stock/ΛCDM:** 2.0e8 with 0.3 dex scatter and 2.6e5 with 0.5 dex. Without the LMC these were 7.3e8 and 4.2e5.

**Combined** (Crater II × Antlia 2, Ji σ): 3.7e6 with 0.3 dex scatter and 1.9e3 with 0.5 dex. With Torrealba's σ: 7.4e9 and 5.8e6.

## Reading

Adding the LMC leaves Crater II as a decisive win for the stock over cuspy ΛCDM. The same one-pericentre progenitor fits the dispersion, stellar mass and tail fraction.

Antlia 2 turns from a draw into a loss for the stock. The reflex motion brings Antlia 2 closer to the Milky Way, which strips its stock harder. A light cuspy subhalo on the same orbit comes close to the observed σ. The loss depends on the dispersion measurement: it holds with Ji et al.'s 6.0 ± 0.4 and flips with Torrealba's 5.71 ± 1.08.

## Limits

- Both Milky Way models are heavier at 50 kpc than Brooks et al. measure (3.36 ± 0.15e11): the theory Milky Way by 17% and the ΛCDM one by 36%. A lighter Milky Way widens pericentres, which would warm both models' dwarfs.
- Antlia 2 uses DR2 proper motions and D = 132 kpc. An RR Lyrae distance of 124 kpc exists and was not used.
- The ΛCDM halo grid stops at −0.9 dex for Antlia 2. Lighter halos could raise ΛCDM's evidence a little further.
- The Milky Way–LMC force follows the standard asymmetric convention, not the theory's joint-source balance. Friction uses the same formula in both models.
- The grid is coarse and uses 40k particles, and ΛCDM halos are cuspy only.

## Files

| File | Contents |
|---|---|
| `lmc_models.py` | The two LMC models and the friction term |
| `orbit_lmc.py` | Three-body orbits |
| `run_lmc.py` | N-body runs in the moving field |
| `analyse_lmc.py`, `analysis_lmc_output.txt` | Analysis and its output |
| `jobs_lmc_*.txt` | Every configuration run |
| `lmc_results.zip` | Per-run outputs and orbits |
