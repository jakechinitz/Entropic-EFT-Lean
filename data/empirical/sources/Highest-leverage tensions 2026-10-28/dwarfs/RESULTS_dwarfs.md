# Dwarf spheroidals (K03/K04): a satellite activity rule

Date: 2026-10-28. Script: `ef_rule.py`; output: `ef_rule_output.txt`.

## The problem

The paper treats satellite stock in two incompatible ways.

- Section 15 ("Retained-stock comparisons") and the Crater II and Antlia 2 runs use collisionless stock that keeps its pre-infall allocation with no contact relaxation.
- Appendix O.3 relaxes dwarf models onto the law (0.02 to 0.04 dex after 12 Gyr).

The 2026-10-26 rerun scores the eight GravSphere classical dSphs on rho(150 pc):

| Treatment | chi^2 (8 dSphs) |
|---|---|
| Unlimited register | 60.3 |
| Paper register (0.9 V_f^2) | 44.8 |
| Frozen register (0.45 V_f^2) | 28.4 |
| Plain NFW, no contacts | 17.2 (Fornax alone 11.8) |

The harness disagreement in K04 does not matter. Both harnesses relax dwarfs onto the law, and that is what the data reject. The contact rate (about 0.14 per Myr in a dSph core) is too fast to leave the stock unrelaxed.

## The rule tested

A satellite's own cells are active only where its own law field dominates the host's field. Where the host field dominates, the satellite's stock keeps its pre-infall allocation and evolves collisionlessly.

The test uses one number per dwarf:

- g_ext is the Milky Way field at the dwarf's distance, from the capped law with C_R = 14.
- g_int is the dwarf's own law field at its 3D half-light radius.

The ratio is fixed before any rho(150) comparison and uses no fitted quantity.

| Dwarf | g_ext/g_int | Class | rho150 obs | NFW (retained) | Relaxed | chi^2 retained | chi^2 relaxed | Observed RAR offset |
|---|---|---|---|---|---|---|---|---|
| Sextans | 5.52 | external | 1.28 | 1.64 | 0.31 | 0.54 | 8.44 | +0.49 |
| Draco | 2.52 | external | 2.36 | 1.60 | 0.58 | 2.22 | 17.35 | +0.70 |
| Ursa Minor | 2.00 | external | 1.53 | 1.78 | 1.31 | 0.23 | 0.18 | +0.73 |
| Carina | 1.74 | external | 1.16 | 1.29 | 0.38 | 0.13 | 10.90 | +0.36 |
| Sculptor | 0.98 | internal | 1.49 | 2.11 | 1.30 | 1.47 | 0.15 | +0.25 |
| Fornax | 0.38 | internal | 0.79 | 2.82 | 1.50 | 11.76 | 1.92 | -0.20 |
| Leo II | 0.20 | internal | 1.84 | 1.55 | 0.95 | 0.48 | 5.12 | +0.21 |
| Leo I | 0.09 | internal | 1.77 | 2.10 | 1.61 | 0.33 | 0.07 | +0.04 |

rho150 is in units of 1e8 Msun/kpc^3.

## Results

| Treatment | chi^2 |
|---|---|
| All relaxed | 44.1 |
| All retained (plain NFW) | 17.2 |
| Rule: retained where g_ext/g_int > 1 | **10.4** |

- **Threshold.** The result holds for thresholds from 0.5 to 1.5 (chi^2 10.4 to 11.7). It degrades to 21.1 at a threshold of 2, which moves Carina to relaxed.
- **Where the gain comes from.** The rule fixes the failures of both alternatives at once. Draco, Sextans and Carina are external-field dominated, so they keep their dense stock, which removes the relaxed model's large misses. Fornax is internally dominated, so it relaxes and cores, which removes plain CDM's largest miss. The remaining cost is Leo II (5.1).
- **Independent support.** The observed RAR offsets at r_1/2 order themselves by the same ratio. Spearman rho = 0.83, p = 0.01, n = 8. External-field-dominated dwarfs sit 0.36 to 0.73 dex above the RAR. Internally dominated ones sit at -0.20 to +0.21.
- **Consistency elsewhere.**
  - Isolated SPARC dwarfs have g_ext/g_int of about 0.1. They relax and lie on the RAR, as observed.
  - The LMC has a ratio of 0.69 at 8 kpc. It is internally dominated, consistent with the relaxed C_R = 33 stock used in the LMC tests.
  - Crater II and Antlia 2 are deeply external-field dominated. They are retained, which is the treatment the paper already uses.
  - The NGC 5291 tidal dwarfs (ratio 0.57) are not covered, because they inherit the parent's records and are descendants, not separate carriers. The rule applies only to carriers with their own records.

## Predictions

These follow from the rule and are distinct from both MOND's external-field effect and plain CDM.

- **Field dwarfs.** Isolated dSphs outside the Milky Way and M31 (Leo T, Cetus, Tucana, Aquarius) should lie on the RAR with cored stock.
- **M31 satellites.** External-field-dominated M31 satellites should lie above the RAR, with CDM-like central densities.
- **Sign of the external field.** In MOND, external-field domination lowers the dispersion. Here it preserves the pre-infall stock and raises the dispersion relative to the law. Tidal stripping can still lower it, as in Crater II.

## Status and caveats

- **This is a new premise for Jake to decide.** The current support rule says a carrier's support ends where its records stop dominating the enclosed baryonic mass. By that rule a dSph's records do dominate the baryons around it, so the dSph would be active. The proposal replaces "enclosed baryonic mass" with "field" for nested carriers. The nearest existing ground is that overlapping carriers already use the joint potential in the flux (Section 15).
- **The retained values are plain NFW at the abundance-matched mass,** with no tidal stripping. Stripping mainly removes the outskirts, but a stripped-retained run per dwarf is the next check.
- **The sample is small.** It is eight galaxies with one binary classification. The threshold was set at the natural value of 1 before the per-galaxy scoring, and no threshold between 0.5 and 1.5 changes the result.
