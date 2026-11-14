# K01: which Δχ² belongs to which pipeline, and does the sign survive DESI DR2

Date: 2026-10-28. Code: `harness.py` (one CAMB harness for both models), `release.py` (the O.12 history as reconstructed in the independent best-fit pipeline), `queue.sh` with `q1-3.txt`, and `table.py`. Outputs are in `run/`, with the summary in `table_output.txt`.

## Data and settings

**Data**
- Planck 2018 plik_lite TT, TE and EE, plus two low-ℓ TT bins. The likelihood reproduces the planck-lite-py reference value −293.95586501795 exactly.
- DESI DR2 BAO.
- DES-Dovekie: Hubble diagram and STAT+SYS inverse covariance from the DES-SN5YR GitHub release, with M marginalised. For comparison, the original DES-SN5YR (2024 commit 97d8d0c) is also used.

**Models**
- ΛCDM.
- The tied release model: ω_c = 5.3333 ω_b with the O.12 history. It is implemented as conserved CDM plus a PPF fluid, and the clustering deficit is applied through A_L,eff.

**Switches**
- SN set.
- A free low-z (z < 0.1) magnitude offset.
- Σm_ν: 0 with N_eff 3.044, or 0.06 eV.
- τ prior: 0.0506 ± 0.0086 (the paper's) or 0.0544 ± 0.0073 (Planck 2018 lowE).
- Planck calibration: fixed, or free with prior 1 ± 0.0025.
- Nonlinear (Halofit) lensing: on or off.
- A_L for the release model: 0.979, a computed value (0.975), or 1.

## Results (Δχ² = release − ΛCDM; release has one fewer parameter)

| SN | low-z offset | Σm_ν | τ prior | cal | NL lensing | ΛCDM χ² | Δ (A_L 0.979) | Δ (A_L calc) | Δ (A_L 1) |
|---|---|---|---|---|---|---|---|---|---|
| Dovekie | free | 0 | paper | fixed | on | **2226.767** | +1.06 | +1.44 | −0.93 |
| Dovekie | free | 0 | paper | fixed | off | **2228.359** | +1.01 | +1.43 | −1.21 |
| Dovekie | free | 0 | paper | fixed | on, CAMB accuracy 1.5 | 2226.814 | +1.07 | | |
| Dovekie | none | 0 | paper | fixed | on | 2235.647 | +2.21 | | |
| Dovekie | free | 0.06 | lowE | free | on | 2230.042 | +2.40 | | |
| Dovekie | none | 0.06 | lowE | free | on | 2238.447 | **+2.72** | +3.09 | |
| DES-SN5YR (2024) | free | 0 | paper | fixed | on | 2235.348 | +1.21 | | |
| none (CMB + BAO) | | 0.06 | lowE | free | on | 603.146 | +2.42 | | |

## Where each published number comes from

- **2226.77 (ΛCDM; Section 20, O.12 PPF, Full Planck tied abundance).** This is reproduced to 0.003 by the first row. The supernova set is DES-Dovekie with an extra free offset for z < 0.1, which the bundle calls "low-z offset marginalization". That nuisance lowers the ΛCDM supernova χ² by 8.1. The paper calls this data set "DES-Dovekie" and does not state the extra parameter.
- **2228.316 / 2228.359 (ΛCDM; O.12 direct table, `High leverage closure 2026-10-21/fit_physical_lcdm`).** This is reproduced exactly by the second row. It is the same data with nonlinear CMB lensing switched off (`NonLinear_none`).
- **−0.515 / −0.519 (direct geodesic release vs ΛCDM, both linear lensing).** Its ΛCDM side is reproduced. Its release side (2227.86) comes from the paper's own release table (`Release zoom/Frel_table.npy`, f = 0.28) and its matched linear Weyl calculation.
  - My PPF reconstruction of the same history, with linear lensing, gives 2229.37 at A_L = 0.979 and 2227.15 at A_L = 1.
  - The direct calculation therefore carries a smaller effective lensing deficit than the PPF benchmark's 0.979.
- **+3.02 (independent best-fit pipeline).** My standard-configuration row gives +2.72 (A_L 0.979) and +3.09 (computed A_L). The independent value lies between them.

## What drives the sign

1. **Nonlinear lensing is not the driver.** Switching it on lowers both models by about 1.55. Δ changes by 0.05.
2. **Data and nuisance choices.** These move Δ by about +1.7 in the release model's disfavour.
   - The undeclared low-z offset is worth 1.15.
   - Σm_ν = 0.06, the Planck lowE τ prior and a free calibration are together worth a further 0.5 to 1.3.
3. **The release history and its lensing deficit.** These span about 1.5 at fixed data:

   | Implementation | Δ in the paper configuration |
   |---|---|
   | Direct geodesic (paper history) | about −0.5 |
   | σ_M caustic | +0.14 |
   | Paper PPF + 0.979 | +0.56 |
   | Reconstructed O.12 history + 0.979 | +1.06 |
4. **The penalty comes from BAO.** Without supernovae the release model is still worse by 2.4, and almost all of it is BAO: χ² 15.4 against 12.8. With the abundance tied at 5.333, DESI DR2 cannot be fitted as well, because ΛCDM moves its ratio to 5.25.

## Verdict

- In the paper's own data configuration, the release model and ΛCDM are tied: Δχ² runs from −0.5 to +1.1 depending on the release implementation.
- In the standard configuration, the same implementations give Δχ² ≈ +1.2 to +2.7:
  - DES-Dovekie as released, with only M marginalised;
  - Σm_ν = 0.06 eV;
  - the Planck 2018 lowE τ prior;
  - calibration free.

  The +1.2 end is an estimate: the paper's direct value shifted by the measured +1.7.
- With one fewer parameter, ΔAIC runs from −0.8 to +0.7.
- **The sign of −0.515 does not survive.** "Statistically competitive with one fewer parameter" does survive.

## Proposed manuscript changes (for Jake; not applied)

1. Name the low-z supernova offset nuisance wherever DES-Dovekie appears, or drop it from both models and requote.
2. Quote the matched direct comparison as a range across release implementations and data configurations, and drop the signed −0.515 headline.
3. State that the tied abundance costs about 2.5 in DESI DR2 BAO χ².
4. Make the remaining test a direct geodesic run with nonlinear lensing, Σm_ν = 0.06 eV and the plain Dovekie likelihood, in both models.

## Caveats

- The low-ℓ CMB treatment is simplified: two TT bins and a Gaussian τ prior.
- The fits are Gauss–Newton local optima, converged to 0.01 in χ².
- My release history is the independent pipeline's reconstruction, not the paper's `Frel_table.npy`.
