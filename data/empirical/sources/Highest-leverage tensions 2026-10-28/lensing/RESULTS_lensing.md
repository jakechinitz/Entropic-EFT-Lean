# Isolated-galaxy lensing and the Lagrangian budget edge: population forward model

Date: 2026-10-28.

**Code**
- `fwd.py`: model.
- `run_fwd.py`: four models at the baseline population.
- `envfit.py`: environment templates.
- `kscan.py`: budget multiplier.

**Outputs**: the matching `*_output.txt` and `kscan_*.txt` files.

## Data

- Brouwer et al. 2021 (KiDS-1000), isolated KiDS-bright lenses.
- Fig. 3 ESD profiles in four stellar-mass bins: log M* = [8.5, 10.3, 10.6, 10.8, 11.0].
- 15 radii from 0.035 to 2.6 Mpc per bin, 60 points in all.
- Full covariance, with the multiplicative bias applied.
- Source: kids.strw.leidenuniv.nl, `brouwer2021_rar.tar`.

## Model

**Lens population per bin**
- True M* drawn from an SHMR-implied central stellar mass function, times a completeness turnover. The turnover is calibrated so that bin 1 reproduces B21's log⟨M_gal⟩ = 10.14. Bins 2 to 4 then come out at 10.555, 10.772 and 10.947, against B21's 10.57, 10.78 and 10.96.
- Gaussian M* errors of 0.15 dex.
- Moster+13 SHMR (M200c) at z = 0.2 with 0.15 dex scatter.
- Tinker+08 halo mass function.
- M_gal = M*(1 + f_cold), with B21's cold-gas relation.
- Mean log M200c per bin: 11.59, 12.04, 12.36, 12.67.

**Profiles** (a0(z = 0.2) = εcH(z) = 1.36e-10 m s^-2). All are projected to ΔΣ and stacked linearly over the population.

| Model | Profile |
|---|---|
| RAR | Uncapped law response |
| CAP_200c | Law response capped at e^{-η*}(1 − f_b) M200c |
| CAP_sp | Law response capped at e^{-η*}(1 − f_b) M_sp (splashback mass, Diemer 2020; M_sp/M200c ≈ 1.33) |
| NFW | (1 − f_b) M200c NFW (Ishiyama+21 concentrations), truncated at r_sp, plus the galaxy point mass. It encloses the same total as CAP_sp. |

**Environment**
- Outside the bound region the theory's stock is cold dust that clusters as CDM does. Every model therefore receives the same environment term.
- The term has two templates: b(M_h) times the linear-matter ΔΣ, and a DK14 infall term beyond r_sp.
- Amplitudes are fitted per bin and are non-negative.

## Results (χ² on 60 points)

| Environment | RAR | NFW | CAP_200c | CAP_sp |
|---|---|---|---|---|
| none | 188 | 422 | 569 | 482 |
| linear, one amplitude | 185 | 277 | 375 | 312 |
| linear + infall, per bin (8 amplitudes) | **176** | **250** | **340** | **281** |
| R < 0.31 Mpc only (32 points), no environment | 84.5 | 98.7 | 116.4 | 93.4 |

### Budget multiplier

The budget is set to k times the M_sp budget, with the 8-amplitude environment.

| k | 1 | 1.5 | 2 | 3 | 4 | 6 | 10 | ∞ |
|---|---|---|---|---|---|---|---|---|
| χ² | 281 | 219 | 191 | 169 | 161 | **157** | 166 | 176 |

### Sensitivity

χ² is given at k = 1, 2, 3, 6, with the environment term.

| σ_obs, σ_SHMR, ΔlogM* (obs − true) | k = 1 | k = 2 | k = 3 | k = 6 |
|---|---|---|---|---|
| 0.15, 0.15, 0 (baseline) | 281 | 191 | 169 | 157 |
| 0.20, 0.20, 0 | 304 | 207 | 180 | 162 |
| 0.10, 0.10, 0 | 262 | 178 | 162 | 153 |
| 0.15, 0.15, −0.2 (true masses higher) | 197 | 149 | 140 | 134 |
| 0.15, 0.15, +0.2 | 420 | 297 | 260 | 236 |

## Reading

1. **The tension survives proper forward modelling.** The tested ingredients were population stacking, SHMR scatter, Eddington bias, the splashback-mass budget and an environment term shared with ΛCDM.
   - With the Lagrangian budget (k = 1), the capped theory is Δχ² ≈ 30 worse than an NFW halo given the same environment freedom.
   - It is about 105 worse than the uncapped law.
   - The best capped fit needs k ≈ 3 to 6, a stock budget of about 4 to 8 times M200c.
   - Even under the most favourable mass systematic (true masses 0.2 dex above the quoted ones), k = 1 is 63 worse than k = 6.
2. **The audit's "up to 2x" was right, but 2x is not enough.** Population stacking already places the mean M200c 0.03 to 0.08 dex above the inverted relation in bins 1 to 3. M_sp adds a factor of 1.33.
3. **The environment term is large for every halo model.** It is 2 to 3 times the linear-bias template in bins 3 and 4, for NFW as much as for the capped theory. B21's MICE comparison attributes the outer signal to neighbours and photometric-redshift leakage. That part of the outer signal is shared with ΛCDM. The inner and intermediate radii, where the capped profile has fallen to Keplerian before r_sp, are not shared.
4. **The uncapped law fits best.** That is the same statement as B21's: MOND and EG describe these isolated stacks better than a truncated halo does.

## Status

Not solved within the current budget premise. The only route I see is a budget larger than the splashback mass.

- **Candidate rule.** One reading of "stock bound to the potential of its records" (Section 18) would let a carrier claim the stock bound to its own logarithmic potential, out to roughly turnaround.
- **What it supplies.** That is about 2 times M_sp in ΛCDM terms, or k ≈ 2. On this data k = 2 is still about 34 worse than k = 6.
- **Status of the rule.** It would be a new premise, and I have not tested it.

## Proposed manuscript change (for Jake; not applied)

Section 15 currently says that beyond 0.3 Mpc every capped model falls below the data and that "the signal there must come from neighbouring structures, as it does in LCDM". Proposed replacement:

> A population forward model of the four KiDS-1000 isolated stellar-mass bins, with the Lagrangian budget at the splashback mass and the same environment term for both, gives χ² = 281 for the capped response against 250 for truncated NFW halos and 176 for the uncapped law over 60 points. The best capped fit needs a budget 3 to 6 times the splashback-mass stock. The isolated-lens profile therefore remains a failed test of the Lagrangian budget at its present normalization.

## Caveats

- The ΛCDM halo model is simplified: no baryonic contraction, no miscentring, and no hot gas in g_bar.
- The environment is template-based, not a MICE-matched mock.
- B21 add 0.1 dex to their RAR errors. Here the raw ESD covariance is used, so absolute χ² values are larger than B21's.
