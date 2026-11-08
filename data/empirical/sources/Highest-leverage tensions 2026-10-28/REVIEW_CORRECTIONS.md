# Independent review of ELIMINATION.md (2026-10-28, late afternoon)

Two reviewers worked from the code and outputs alone. Neither saw the reasoning behind the results. This file supersedes the affected claims in `ELIMINATION.md` and in the morning RESULTS files. Those files are left unchanged.

## Lensing

**Confirmed**
- Data handling, units, the covariance, the RAR excess, the population model and the χ² machinery are all correct.
- The numbers reproduce to 1e-14.
- The ranking HYB < NFW survives every environment model tried: a per-bin power law beyond 0.3 Mpc, linear only, infall only, or no environment inside 0.2 Mpc.

**Withdrawn: "the support-limited theory beats ΛCDM".** The NFW comparison was rigid: Moster+13 halo masses and Ishiyama+21 concentrations, with nothing fitted. Give both models the same two global nuisances, a halo-mass shift and a concentration factor (the usual stand-in for miscentring):

| Model | χ² (60 points + environment) |
|---|---|
| NFW | 132.7 |
| HYB | 140.3 |

NFW needs c ≲ 0.6 × Ishiyama for this. That is low but within standard halo-model practice. **The verdict is a draw.**

**The HYB advantage traced to a modelling choice.** Where the law needs less stock than the support holds, the surplus was placed as a thin shell at r_s. That moves 10–19% of the inner stock outward in the massive bins, which mimics low concentration.

| Surplus treatment | χ² |
|---|---|
| Kept in its NFW shape | 253 (equal to NFW) |
| Spread from r_s to 1.5 r_s | 217 |

The O.3 constrained minimiser on a bounded domain does put surplus at the domain edge, but its form is not pinned down. The projector also mishandles thin shells. The effect on χ² here is at most 1.3, but sharp features need an exact Abel projector.

**What stands**
- The Keplerian-edge failure disappears once the Section 18 support rule is applied to isolated lenses.
- The theory is then indistinguishable from ΛCDM on the B21 isolated-lens data.
- No model fits 0.5–1.5 Mpc. Every model leaves 3–6σ pulls there.

## Dwarfs

**Confirmed**
- The inputs match McConnachie 2012.
- The units and the χ² arithmetic are correct.
- The classification is robust to M_b, C_R, projected vs 3D radius, and Newtonian vs law fields, with Sculptor (ratio 0.98) the only exception.

**Corrected**
- *The Spearman correlation is not independent support.* Galactocentric distance alone gives the same 0.83, so the correlation is the known distance–offset trend. The exact permutation p-value is 0.015, not 0.010.
- *Look-elsewhere.* 10 of the 256 retained/relaxed assignments reach χ² ≤ 10.4, and the rule's assignment ranks 10th. The best is 5.7: retain Draco, Sextans, Carina and Leo II. Most of the gain comes from four dwarfs.
  - With the threshold fixed at 1, only 2 of the 70 four-dwarf subsets do this well.
  - If the cut position may be chosen freely, 21% of random orderings do this well.
- *Threshold sensitivity was overstated.* A threshold below 0.98, or M_b ≥ 7e10, retains Sculptor and gives χ² 11.7.

**What stands.** The rule is consistent with the data and better than all-CDM or all-relaxed. The evidence for it specifically is modest.

## Cosmology (K01)

**Confirmed**
- GEO matches the paper's direct geodesic model line by line.
- The neutrino-mass background treatment is accurate to below 0.01 in χ².
- The SN, BAO and Planck-lite pieces match their official implementations.
- The minima are converged to about 0.005.
- The ΛCDM values 2226.767 and 2228.359 are reproduced.

**Corrected**
- *The τ prior labelled "lowE" (0.0544 ± 0.0073)* is Planck's TT,TE,EE+lowE+lensing posterior. With plik-lite in the fit it double-counts the high-ℓ data. The lowE-only prior is 0.0506 ± 0.0086. The standard configuration was rerun with it:
  - Plain Dovekie, Σm_ν = 0.06 eV, calibration free.
  - **GEO − ΛCDM = +0.85, ΔAIC = −1.15** (`cosmology/run/*off0_mnu0.06_taufp_calfree*`).
- *The low-z SN offset.* It is worth 1.2–1.5 to the release model only in the paper's configuration. In the standard configuration it is worth 0.3–0.7.
- *Breakdown of the standard Δ:*

  | Component | Contribution |
  |---|---|
  | CMB | −1.5 |
  | BAO | +2.0 |
  | SN | +0.8 |
  | Priors | −0.4 |

  The BAO cost is physical: with ω_c tied to ω_b, the model cannot compensate for Σm_ν.

**What stands.** A χ² tie in every configuration (−0.4 to +0.9), with negative ΔAIC throughout.
