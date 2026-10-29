# Held-out test record of 2026-10-26 (archived 2026-10-29)

This is a dated record. It documents the version of the theory frozen for the held-out tests of
2026-10-26 and a Lean formalization of that version (`Entropic/BestFit`, seven modules) written on
2026-10-29. That formalization is **not** part of this library. Three general pieces of it were ported
and restated against the current library:

| Ported to | Content |
|---|---|
| `Entropic/ContactLedger.lean` | the acceptance rule and work register: heating bounded by register plus credits, no heating once spent, mismatch antitone |
| `Entropic/ReleaseLedger.lean` | release-ledger conservation, one-signed vacuum accumulation, `I_rel ≥ F(1)`, early release; with the paper's reference history (`F(1) = 0.6633922061`, `I_rel = 94.2116`) some release precedes `z = 4.2` |
| `Entropic/RAR/Redshift.lean` | the law of `GalacticLaw.gObs` with `a₀(z) = ε c H(z)`: boost rising with `H`, `cH/a₀ = 1/ε`, Tully–Fisher zero point `M(z)/M(0) = H(0)/H(z)` |

**Numbers in the record below are those of 2026-10-26 and differ from the current paper.** On that date the
held-out comparison favored plain CDM on the classical dwarfs (best-fit χ² 29.5 on 7 degrees of freedom
against 17.2 for CDM) and ΛCDM in cosmology (Δχ² = +3.02, ΔAIC = +1.02). The current paper's dwarf result
(support-field rule, χ² 10.4 on the same eight dwarfs) was found after that test, and its cosmology result
(direct geodesic perturbations, Δχ² = +0.85, ΔAIC = −1.15) replaces the approximate PPF treatment and a
double-counted τ prior. The record is kept because it is the held-out result.

Two flags in the record were checked on 2026-10-29:

- **Contact cross-section.** The contact law `σ/m = 288 / (1 + (v/200 km s⁻¹)⁴) cm² g⁻¹` gives 0.46 at
  1000 km s⁻¹, under the 0.47 bound of Harvey et al. (2015) from colliding clusters. The bound does not apply:
  Section 18 confines contacts to stock inside active-carrier supports, and cluster stock outside the central
  galaxy's support (47–99 kpc in X-COP) is collisionless. Above 2000 km s⁻¹, typical of cluster
  collisions, the law is below 0.03 cm² g⁻¹.
- **Two values of H₀.** The galaxy runs use `a₀` at `H₀ = 67.4`; the release cosmology fits `H₀ = 68.94`, a
  2.3 % higher `a₀`, which the paper states. Rerunning the 22-dwarf registered predictions at the higher `a₀`
  leaves every classification unchanged and moves the support-rule χ² from 31.03 to 30.83.

---

# Best-fit version: Lean formalization (2026-10-29)

`Entropic/BestFit/` formalizes the version of the theory that was frozen for the held-out
tests of 2026-10-26 (results bundle `best_fit_tests.zip`, README sections 0 to 7). That version
fixes the paper's open choices as follows:

- acceleration scale `a₀ = ε c H(z)` with `ε = 0.187946` (running exponent `p = 1`);
- the paper's spherical law `g_obs = g / (1 − exp(−√(g/a₀)))`;
- the release cosmology of App. O.12: formation ratio 5.3333, `η* = 0.0298668443935`, fitted
  release integral `I_rel = 91.9`, present ratio 5.236;
- the local pair-contact law `Γ = A ρ u / (1 + (u/v₀)⁴)` with `A = 288 cm² g⁻¹`,
  `v₀ = 200 km s⁻¹`, the working note's acceptance rule and a work register of
  `0.45 V_f²` per unit stock mass;
- a supernova coupling `η = 0.1` (of `10⁵¹ erg` per `100 M☉` formed), no tidal-work credit.

It also covers the two variants tested on 2026-10-26 (energy-conserving contacts; contacts
only while a galaxy forms stars) and the Antlia 2 runs on the Milky Way + LMC orbit.

## Modules

| Module | Theorems | Kind | Content |
|---|---:|---|---|
| `Parameters` | 12 | B | `a₀` for both values of `H₀` used, `1/ε`, `a₀ · (1/ε) = cH₀`, present-ratio consistency, cross-section conversion and limits, supernova energy |
| `RedshiftLaw` | 14 | A, C | `g < g_obs`, `√(a₀g) ≤ g_obs ≤ g + √(a₀g)`, `g_obs` strictly increasing in `a₀`, boost rising with `H(z)`, `cH/a₀ = 1/ε` at every `z`, Tully-Fisher zero point `M(z)/M(0) = H(0)/H(z)` |
| `ContactLedger` | 14 | A | acceptance rule and register for any sequence of proposals: energy ledger, register ≥ 0, heating budget, no net heating once the register is spent, mismatch never rises, elastic contacts keep `K` fixed, gas gate |
| `PairKicks` | 20 | A | the best-fit kick conserves momentum and angular momentum and changes `2mK` by `2α d·Δp + 2α² d·d`; the elastic rotation conserves momentum and energy but not angular momentum |
| `ReleaseLedger` | 7 | A, B | committed + released stock conserved, vacuum density nonnegative and monotone, `I_rel ≥ F(1)`, some release at `a³ ≤ F(1)/I_rel`; for the fitted history, before `z = 4.3` |
| `Tides` | 5 | A, D | Jacobi mean-density identity, Wolf estimator, Antlia 2 today 5× below its pericentre threshold, survival split across the 16 recorded runs |
| `Results` | 5 | D | dwarf χ² with degrees of freedom, reduced-χ² ordering, 3σ excess test, cosmology ΔAIC |

Theorem counts are explicit `theorem` declarations (77). The axiom audit counts 127 theorem
constants, including generated equation and extensionality lemmas.

## What the formalization adds

1. **The elastic variant did not conserve angular momentum.** `PairKicks.angular_change` shows
   that any momentum-conserving pair update changes the pair's angular momentum by
   `(xᵢ − xⱼ) × Δpᵢ`, which vanishes only for impulses along the separation.
   `elastic_breaks_angular_momentum` gives an explicit pair for which the elastic rotation
   used in README section 7.1 changes it. The best-fit kick conserves it exactly
   (`kick_angular`). The elastic runs' rejection stands on their densities, but their dynamics
   carried this defect.
2. **The late-time cooling of the dwarfs is forced by the ledger.** `run_ledger` and
   `run_register_nonneg` give `K_final ≤ K_initial + R_initial + credits` for every sequence of
   proposals (`run_heating_bounded`). Once the register and the supernova credit are spent, the
   stock cannot end hotter than it is (`spent_register_no_heating`), while cooling contacts stay
   available. This is the mechanism README section 6 identified for the slow contraction of
   the dwarf runs.
3. **The fitted release history releases stock early.** `I_rel = 91.9` with `F(1) = 0.613`
   requires part of the release before redshift 4.3 (`fitted_history_releases_early`).
4. **Two parameters disagree slightly.** The galaxy runs used `a₀ = 1.2307×10⁻¹⁰ m s⁻²`
   (`H₀ = 67.4`), the cosmology fit implies `1.2481×10⁻¹⁰` (`H₀ = 68.35`), a 1.41 % difference
   (`a0_ratio_window`). The paper asks for one `H₀` in both sectors.
5. **The contact cross-section sits just under a merger bound.** At 1000 km/s it is
   `0.460 cm² g⁻¹` against the 0.47 bound (`merger_limit`); at the Bullet Cluster's 4700 km/s it
   is below `10⁻³` (`bullet_limit`).

## What is not certified

- **Physical premises (kind C).** These are stated as definitions or hypotheses and not
  derived: `a₀(z) = ε c H(z)`, the acceptance rule as the physics of the stock, the release
  law, and the identification of the RAR target.
- **Data inputs (kind D).** These are records of numbers computed outside Lean, and the
  theorems check only arithmetic on them. They include the χ² values, the 16-run survival
  table, and the host mass and slope at 40.1 kpc (from `tidal_threshold.py`). Simulation
  outputs, likelihoods and observational catalogues are not checked.
- **No bridge theorems.** `RedshiftLaw.gObs` is the same formula as `Entropic.GalacticLaw.gObs`,
  and `PairKicks.kick` is the impulse of `Entropic.StockSettling.applyContact`. No theorem here
  identifies them: those two modules need Mathlib files that were not available in this build
  (see Verification).
- **Statistics.** The χ² p-values quoted in the bundle are not computed in Lean.

## Verification

The modules import only Mathlib (Lean 4.35.0, the repository's pinned Mathlib `v4.35.0`) and
each other. They were compiled module by module against a local Mathlib build. That build is
partial, and the Mathlib cache server was not reachable, so the repository's full `lake build`
was not run here; CI would build `Entropic.BestFit` with the rest of the library, since
`Entropic.lean` imports it.

`scripts/AxiomAuditBestFit.lean` reports:

```
Entropic.BestFit: 127 theorems; 0 with nonstandard axioms
```

Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. The sources
contain no `sorry`, no `native_decide` and no custom axioms. Finite data checks use `decide` on
natural numbers, and numerical windows use `norm_num` on exact decimals.
