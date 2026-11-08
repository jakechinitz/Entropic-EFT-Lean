# Independent review of the dwarf release-gate result (2026-10-28, evening)

The reviewer worked from the code and outputs alone and reproduced all four chi^2 values: 30.0, 24.0, 21.7 and 25.4. Every input was checked: LVDB units, all 18 Weisz+2015 tau_90 values, the Fakhouri implementation and the coreNFW implementation.

## Findings that shape the manuscript wording

- **The gate is not pinned down by these data.**
  - Pre-reionization gate from 12 to 20 km/s:

    | Pre-gate (km/s) | chi^2 |
    |---|---|
    | 12–14.5 | 25.4 |
    | 15–18 | 21.7 |
    | 18.5–20 | 18.5 |

  - The 30 km/s post-reionization gate never decides a classification.
  - 147 of the 2^11 relaxed/retained assignments for the self-dominated dwarfs reach chi^2 <= 21.7.
- **The rule's chi^2 depends on the accretion-history model.** It ranges from 18.5 (Correa+15; exp(-0.4z)) to 27.6 (exp(-0.6z)). Halo-to-halo scatter makes individual classifications near the gate close to coin flips.
- **Host-field and data choices move the rule's chi^2.**
  - An M31 baryonic mass >= 1.25e11 retains Andromeda II, giving 29.2.
  - Tucana at sigma = 14 km/s (Gregory+19) gives 25.5 for both models.
  - Andromeda II at sigma = 9.3 gives 21.0 (rule) against 21.3 (heating).
- **Heating at its published calibration spans 23–25.5.** Varying kappa and eta gives 23–28.5.
- **Minor issues:**
  - Tucana uses LCID (12.5 Gyr) where the Weisz table gives 6.5 Gyr (heating 23.6).
  - Relaxed masses are evaluated at 1.305 R_e, while the Wolf masses use 4/3 R_e.
  - The harness starts halos at z = 6 with their z = 0 NFW.
  - Single seeds give 0.05–0.1 dex of noise.

## Verdict, as adopted in the manuscript

The combined rule is comparable to LCDM + heating on these 22 dwarfs. These data do not test the gate.
