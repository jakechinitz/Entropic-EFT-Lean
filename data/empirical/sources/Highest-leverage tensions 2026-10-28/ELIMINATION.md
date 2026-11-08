# Process of elimination on the three open items (2026-10-28, afternoon)

This note builds on the morning results in this folder. Those files are left unchanged; this note corrects two of their verdicts.

**Sources read**
- Research notes:
  - Lensing boundary tests and review (10-24)
  - Mechanism assessment (10-24)
  - Record rule derivation (10-25)
  - Read cap (10-25)
  - LMC and satellites checks
  - Release zoom
  - High leverage closure (10-21; the direct cosmology fits)
  - Full Planck tied abundance
  - Dark energy prediction tests
- Paper, Full: Sections 15, 18 and 20, Appendix O.3 and O.12, and the nesting and descendant paragraphs.
- Lean:
  - `Projectors.lean`: a smooth weight is idempotent only if it is binary.
  - `StockSettling.lean`: the work-budget endpoint, `settles_iff_below_threshold`.
  - `ContactSelection.lean`, `RetainedRelaxation.lean`, `GalacticLaw.lean`, `EnvelopePremises.lean`.

## 1. Isolated-galaxy lensing: the edge is removed by the paper's own support rule

**Candidates for the outer signal, and what removes each**

1. *A larger isolated budget.* The closed-form bound in the Lensing boundary review gives S_min(g_bar) = (π/4) sqrt(a0/g_bar) − 1, so S ≈ 86 at g_bar = 1e-14. The review shows S ≈ 100 is excluded for the Milky Way: a 1 Mpc halo would overlap M31 and exceed the Local Group mass. **Eliminated.**
2. *An uncapped response.* The stock is conserved and finite, and clusters need the cohort ratio 6.18 with the response switched off outside supports. **Eliminated by the theory itself.**
3. *All Lagrangian stock carried and settled inside r_C, so the exterior is Keplerian.* This is the morning model and the 5–9σ test. Section 18 states that a carrier's support ends where its records stop dominating the enclosed baryonic mass, and that stock outside the support enters no cell and stays collisionless. The paper applies this to clusters and groups but not to isolated lenses. In an isolated L* galaxy the hot CGM holds no records (Record rule derivation: mixed, shock-heated gas has w = 1 − K_mix → 0). Once the CGM's enclosed mass exceeds M_gal, the support ends. **The Keplerian-edge model therefore contradicts the paper's own rule.**
4. *What survives.* The law response inside r_s, built from the carried stock M_N(<r_s). Outside r_s the stock is uncarried and keeps its CDM distribution to the splashback radius. Beyond that is the shared environment.

**Test** (`lensing/hybrid.py`; B21 four isolated mass bins, 60 points, full covariance, population forward model). The hot CGM is isothermal with M_hot = f_hot f_b M200c out to r200. The same hot gas is added to every model.

χ², all 60 points, with the 8-amplitude environment term (inner 32 points, R < 0.31 Mpc, in brackets):

| f_hot, population | Support-limited (theory) | NFW (ΛCDM) | Full cap (morning) | Uncapped law |
|---|---|---|---|---|
| 0.2, baseline (r_s ≈ 110–125 kpc) | **216** (68) | 252 (103) | 270 (87) | 165 (79) |
| 0.1 (r_s ≈ 170–220 kpc) | 225 (78) | 252 (101) | 276 (90) | 170 (81) |
| 0.4 (r_s ≈ 55–63 kpc) | 229 (85) | 254 (110) | 259 (83) | 157 (75) |
| 0.2, σ = 0.2 dex | 215 (65) | 236 (85) | 292 (95) | 170 (81) |
| 0.2, M* true 0.2 dex higher | 289 (171) | 527 (409) | 204 (92) | 152 (94) |
| 0.2, M* true 0.2 dex lower | 364 (136) | 380 (152) | 396 (149) | 248 (124) |

**Results**
- The support-limited theory beats the ΛCDM halo in all six variants, by Δχ² = 16 to 238. It has the best inner fit in four of the six.
- There is no Keplerian edge: past r_s the stock simply continues its CDM profile.
- The remaining gap to an uncapped law lies at R > 0.3 Mpc. There the environment template decides the ranking, and ΛCDM faces the same question.
- **This reverses this morning's verdict.** "Fails at the Lagrangian normalization" came from applying the budget to stock the support rule does not carry.

**Open input**
- The hot-gas mass and profile of the lenses, f_hot ≈ 0.1–0.4. Isolated L* CGM estimates fall in this range.
- r_s is predicted from f_hot, not fitted.

## 2. Dwarfs: one support criterion covers satellites, isolated lenses and the Solar System

**Candidate levers for keeping Draco dense while Fornax cores**

| Lever | Why it fails or survives |
|---|---|
| Contact rate | ~0.14 per Myr in every dSph. **Eliminated.** |
| Work register | Paper and frozen registers still core Draco, Sextans and Carina (χ² 44.8, 28.4). For small σ, `settles_iff_below_threshold` (StockSettling.lean) says the budget does not limit settling. **Eliminated.** |
| Budget | Lagrangian budgets are hundreds of M_b. **Not limiting.** |
| Tidal stripping | Removes outer stock and does not raise ρ150. **Eliminated.** |
| Carrier support | **Survives.** It must be binary, per `Projectors.lean`. |

**Which support criterion**
- "Records dominate the enclosed baryonic mass about the satellite": every dSph passes, so all relax, giving χ² 44. **Eliminated.**
- "Inside the tidal radius" and "denser than the host locally" (Roche): every bound satellite passes. **Eliminated.**
- "Records dominate the baryonic *field*": **survives.** For an isolated spherical system it is identical to the paper's enclosed-mass wording, because the monopole field equals G M(<r)/r². For a nested system it compares the satellite's own baryonic field with the host's. In the deep regime it gives the same classification as the law-field ratio.

**Result.** Draco, Ursa Minor, Sextans and Carina are host-dominated and keep their stock. Fornax, Leo I and Leo II are self-dominated and relax. Sculptor sits at the boundary, with ratio 0.98.
- χ² = 10.4, against 17.2 for plain CDM and 44 for all relaxed.
- The observed RAR offsets order by the same ratio (Spearman 0.83, p = 0.01).

**The same sentence reproduces what the paper already does**
- **Clusters, groups and BCGs:** support ends where hot gas overtakes condensed baryons. This is Section 18 unchanged.
- **Isolated lenses:** item 1 above.
- **Sun and wide binaries:** the Milky Way field dominates, so they are descendants and Newtonian, as in Section 16.
- **The LMC:** self-dominated (ratio 0.69), so it is its own carrier, as in the LMC tests.

**Timing check, and the gap it leaves**
- The relaxation runs core a dSph within about 1 Gyr of z = 6. Draco must therefore have lacked support before infall too.
- The record rule supplies a candidate. After reionization, halos below the 30 km/s photoheating scale (the release gate already in Section 20) hold their remaining gas warm. Gas with t_cool > t_dyn holds no records. With f_b M200 ≈ 3e8 Msun of gas against 3e5 of stars, the stars cannot dominate the baryons until the gas is removed. The gas is removed by ram pressure at infall, and by then the Milky Way field dominates.
- Classical dSphs with V200 below 30 km/s (all eight except Fornax) would then never have carried cells unless they lost their gas while isolated. Fornax and Leo I kept cold gas and formed stars late.
- This step is qualitative. It needs each dwarf's gas history and its orbit since z ≈ 6.
- **Prediction:** gas-rich isolated dwarfs (cold HI, which holds records) lie on the RAR. Gas-poor dwarfs that lost their gas while already host-dominated keep cusps.

## 3. Cosmology (K01): the direct model is the right benchmark, and the sign hinges on one nuisance parameter

**Candidate causes of the pipeline spread, and what each turned out to be**
- *Nonlinear lensing:* shifts both models equally. **Eliminated.**
- *The PPF + A_L shortcut:* it overstates the release model's lensing deficit relative to the paper's direct geodesic calculation, by 1.5 to 1.8 in χ². This is the PPF-to-direct difference measured in the runs below. **Eliminated as a benchmark.** The direct calculation (`harness_v2.py`, model GEO) reproduces the paper's −0.58 with linear lensing, and the ΛCDM χ² 2228.359 exactly.
- *The undeclared low-z supernova offset:* worth 1.2 to 1.5 to the release model. **Survives as the decisive switch.**

**Direct geodesic release minus ΛCDM** (`cosmology/run/GEO_*`):

| Data configuration | Δχ² | ΔAIC (one fewer parameter) |
|---|---|---|
| Paper's (offset, Σm_ν = 0, paper τ, cal fixed), nonlinear lensing | −0.39 | −2.4 |
| Same, linear lensing (the paper's direct table) | −0.58 | −2.6 |
| Offset, Σm_ν 0.06, Planck lowE τ, cal free | +0.28 | −1.7 |
| No offset, Σm_ν 0, paper τ, cal fixed | +1.14 | −0.9 |
| **Standard: plain Dovekie, Σm_ν 0.06, lowE τ, cal free** | **+0.95** | **−1.05** |
| CMB + DESI only, standard settings | +0.28 | −1.7 |

**Results**
- On χ² alone the release model ties with ΛCDM in every configuration.
- With one fewer parameter, ΔAIC is negative in every configuration.
- The signed −0.5 needs the low-z offset. Under the standard configuration the direct number is +0.95.
- The BAO cost of the tied abundance in the direct model is about +2.0 (14.8 against 12.8). The CMB gains back about 1.6.
- **Proposed wording:** "Δχ² = +0.95 with one fewer parameter (ΔAIC = −1.05) under the plain DES-Dovekie likelihood and Σm_ν = 0.06 eV; −0.39 with an additional low-redshift supernova offset".

## What remains genuinely open

1. **Hot CGM masses of isolated lenses.** These set r_s. The observational input exists (X-ray stacking, tSZ, CGM surveys) and has not been used yet.
2. **Gas and orbit histories of the classical dSphs.** These are the timing check for the support criterion.
3. **The R > 0.3 Mpc environment.** This is common to every halo model. Settling it needs a MICE-style mock with the same isolation cut and photometric-redshift scatter, run with the theory's stock.
4. **The field-dominance wording of the support rule.** It is a premise change for Jake. It generalises the existing sentence and does not add a mechanism.
