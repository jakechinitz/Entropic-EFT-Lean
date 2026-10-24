# Entropic Scalar EFT: Lean formalization

[![build](https://github.com/jakechinitz/Entropic-EFT-Lean/actions/workflows/build.yml/badge.svg)](https://github.com/jakechinitz/Entropic-EFT-Lean/actions/workflows/build.yml)

This project formalizes the mathematical statements of Jacob Chinitz's
*Entropic Scalar EFT: From Entanglement Microstructure to Gravity and Cosmic
Structure* in **Lean 4.35.0 with mathlib**. The source record and the SHA-256
hash of the PDF used are in `provenance.json`. CI builds the library, runs the axiom audit
and the ledger citation check on every push.

## Effective dynamics and cluster extensions (2026-10-23)

Six modules under `Entropic/Extensions20261023` add 119 explicit theorem declarations to the import graph. The status table below counts them. The normal pinned Lean 4.35 build and module-based axiom audit include all six modules. Their earlier standalone checks used Lean/mathlib 4.19. See [extension scope and provenance](verification/extensions_2026-10-23.md) for the distinction between conditional mathematics and empirical calculations.

## Stock settling and finite renewal (2026-10-23)

Two modules address open points from an external review. See [scope and reading](verification/settling_renewal_2026-10-23.md).

- `Entropic/FiniteRenewal.lean`: Kac's return-time identity for any finite reversible dynamics, and a finite shift register whose readings have the product law on every window up to its length (ensemble over register states). The charged-lepton shell load 720^N holds exactly without memorylessness. The G_* chain does not transfer as derived: every finite reversible renewal is periodic with entropy rate zero, which the maximum-entropy-rate selection of App. H.4 rejects.
- `Entropic/StockSettling.lean`: any schedule of central pair contacts conserves linear and angular momentum; reversible maps preserve fine-grained Casimirs; on a signed work ledger the population at supply exhaustion does not depend on the contact rate; and with work proportional to σ² the settled fraction is min(1, σ_c²/σ²). The σ² scaling and the fixed supply per unit stock are stated hypotheses.

## Assumption compatibility (2026-10-23)

`Entropic/Compatibility` proves `Nonempty EffectiveModel` (`Entropic.Compatibility.effective_assumptions_compatible`): one structure carrying the native closure root η and ε, the 1680-state Gibbs histories, the 720-state shell cycle, a finite positive stock shared by reconstruction, redistribution and nonzero reciprocal Newton forces, and an explicit expanding homogeneous Einstein solution with positive energy transfer, tied to the finite model through the same mass budget. It also proves that a fixed finite faithful archive and an exact dense-core RAR profile are each impossible. This is an effective subsystem, not a consistency proof of the full theory: the finite force system is not embedded in the expanding metric. `Entropic/Completion/InfiniteHistory.lean` gives one probability space for all integer times with the native Gibbs marginal and a measure-preserving reversible shift. Provenance and scope: [compatibility record](verification/compatibility_2026-10-23.md).

The completion modules extend this to `Nonempty GlobalModel` (`Entropic.Completion.global_effective_assumptions_compatible`): the exact native rooted history measure with the unique native η, and a global inhomogeneous clock/stock family with positive baryons, donor and retained stock, active release, radial contrast at every epoch and unbounded future proper time. The local pressure equations, density and volume evolution and component positivity are kernel checked; the coordinate Einstein-tensor reduction is checked separately in SymPy (`tools/completion_metric_check.py`). `Obstructions`, with `Compatibility.exact_dense_core_isEmpty`, records four incompatibilities (fixed finite archive against recoverable IID history, positive stock against the exact raw dense-core profile, one exchange vector against distinct streams, and bare against physical G without matching). `GlobalFloor.current_floor_fails_global_domain` proves that its first floor constant leaves the depletion-action domain; the selected-action certificate is local in time. This is not a microscopic or full-theory compatibility proof. Provenance, the 27 obligations and the global-floor candidate: [completion record](verification/completion_2026-10-23.md).

`Entropic/FourItems` adds two follow-up modules. `Streams`: a covariant 1+1 source/force decomposition for multistream exchange with energy conservation, positive internal allocation, an explicit two-stream witness and Bianchi-I constraint propagation (the Bianchi-I metric reduction is checked in SymPy, `tools/fouritems_bianchi_tensor.py`). `Selection`: matching underdetermination when the selected C.5 premise is omitted, affine kernel-normalization degeneracy, reversible energy-preserving swaps, and finite compensating-register bounds for an energy-conserving reset. These are not physical-selection proofs and contain no bound galaxy or native gravitational state. Record: [four open items](verification/fouritems_2026-10-23.md).

## Halo envelope premises (2026-10-24)

`Entropic/MicroEnvelope3D.lean` (GPT, ported) gives the pressure and depletion-floor identities, a weighted Schur bound and the matched-family stability margins of the isentropic envelope. `Entropic/EnvelopePremises.lean` separates its premises: the exponent γ = 2 is the stiffest member of the warm family that stays causal at every density (`causal_iff`, `stiff_limit`); a universal pair kernel has bounded range across compositions (`pair_coefficient_bounds`), so the matched coefficient ζ ∝ M_b must be a state label; matching gives `g(a) = 2η(1+η)a₀` and a closed-form envelope solution and stock (`envelope_mass_matched`); a stock reaching radius L needs a stock-to-baryon ratio of at least (L/r_M − 1)/2 (`stock_ratio_lower_bound`); and the retained and detected baryon fractions `k/S` and `(1+k)/(1+S)` are distinguished (`retained_fraction`, `detected_fraction_formula`). Scope and the weak-lensing comparison: [envelope premises](verification/envelope_premises_2026-10-24.md).

## Contact selection (2026-10-24)

`Entropic/ContactSelection.lean` gives the statistical and mechanical identities behind a stock-contact selection rule. It does not give a microscopic exchange operator, a rate, a cluster gate or halo formation. The Section 15 gap function is the relative entropy of geometric distributions: it is nonnegative and vanishes at the Bose occupation (`boseGap_eq_relEnt`, `relEnt_nonneg`, `boseGap_at_nStar`), with curvature `1/(n(1+n))` (`boseGap_second_derivative`). The quadratic field mismatch `(δg)²/8πG` is its Gaussian limit exactly under the equipartition condition `𝒩Θ = g_b² n(1+n)/4πG` (`equipartition_matching`). Local detailed balance suppresses uphill transitions as the bath temperature goes to zero (`uphill_rate_vanishes`). A symmetric mobility on orbit populations never raises the functional (`symmetric_flow_dissipates`), and pair impulses along the separation conserve momentum and angular momentum (`pair_impulse_conserves_angular_momentum`). The module also holds the algebra of the stiff-coupling amplification (`stiff_coupling_amplification`), the Vlasov–Poisson acceleration scaling (`vp_acceleration_scaling`) and the counterexample to clip-and-renormalise (`clip_renormalise_not_minimal`). Thirteen statements are ported from GPT's contact-bridge note. Section 3 adds eight identities used by the cluster and galaxy sections of the manuscripts: the enclosed stock-to-baryon ratio equals the occupation (`occupation_is_enclosed_ratio`), the budget clip is optimal and monotone (`clip_optimal`, `clip_monotone`), the weak-lensing stock bound (`lensing_stock_bound`), arithmetic checks on the X-COP comparison (`field_response_misses_clusters`, `cohort_between_xcop`) and on the redshift test (`redshift_ratio_precision`), and the bookkeeping statement `no_cells_no_bias`. Cluster protection is a premise, not a theorem: observed-cluster runs of the ungated rule rearrange cluster stock. Scope: [contact selection](verification/contact_selection_2026-10-24.md).

## Status (2026-10-23)

| Item | Value |
|---|---|
| Library | one Lean library, `Entropic`: 187 modules, 3,487 theorems (the v0.8 library is its submodule `Entropic.EFT`, 727 theorems) |
| Axioms | every theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (`scripts/AxiomAudit.lean`, log in `verification/axiom_audit_contactclusters_2026-10-24.log`) |
| Proof hygiene | no `sorry`, no custom axioms, no `native_decide`; finite enumerations and integer matrix identities are checked by kernel `decide` |
| Claim ledger | `ledger/LEDGER.md`: all 1,437 statements of the manuscript with kind and status |
| Ledger totals | proved 874, proved in part 90, numerical enclosures 59, data comparisons 64, physical premises 153, not formalized 143, simulation outputs 19, other 35 (interpretive, definitions, corrections, cited results) |
| Citation check | `scripts/CiteCheck.lean`: 987 Lean names cited in the ledger, 0 unresolved |

Supporting files:

- `ledger/CLAIMS.md`: kind × status table and the reverse index from Lean names to claims.
- `ledger/RETIREMENT.md`: the 114 structures of the v0.8 library (`Entropic.EFT`) classified as instantiated certificates, mathematical packages with their proving theorems, physical premises, or data carriers.
- `ledger/PLAN.md`: the 14 work chunks and what each module group covers.
- `ledger/extraction/`: the per-section claim extraction (C01 to C15) from which the ledger was built.
- `tools/`: an independent Python re-derivation of the finite ensemble and closure numbers of `Entropic.EFT` (not the Lean kernel), run in CI.
- `verification/`: the axiom-audit and citation-check logs of the release build. Version 0.8 (Lean 4.33, library `EntropicEFT`) is in the git history of `main` before this release.

## Read this distinction first

A Lean theorem says that its conclusion follows from its **explicit
mathematical assumptions**. It does not establish that those assumptions
describe nature, that the transcription captures every qualification in the
paper, or that a prediction is observationally accurate.

There are three different evidential claims:

1. **An identity is correct.** For example, the three exchange currents sum to
   zero. This is proved.
2. **A consistency check is incomplete, or a specified combination of
   assumptions is incompatible.** For example, the reduced continuity
   equation alone does not preserve positive stock for every positive initial
   stock and positive prescribed drain. This is proved for that reduced
   equation. Whether the full model permits those inputs is a separate question.
3. **The model is excluded by observations.** This would require a definite
   physical prediction and a comparison with measurements, including relevant
   uncertainties. No theorem in this project makes this claim.

Ledger kinds follow the same separation: A (exact mathematics) and B (numerical
values) are proved outright where formalized; C (premise-conditional) records the
physical premise and proves what follows from it; D (data) records the comparison
with the cited data; E (interpretive) is not formalized.

## Layout

| Path | Content |
|---|---|
| `Entropic/FiniteModel.lean`, `ClosureRoot.lean`, `Spine.lean`, ... | finite boundary ensemble, closure root with certified decimals, spine constants |
| `Entropic/AppB` to `Entropic/AppQ` | one module group per appendix (B, C to E, F and G, H.1 to H.9a, H.10, H.11 to H.15, I and J, K to N, O, P, Q) |
| `Entropic/Main` | main-text Parts IV to VIII (galactic, core, cosmological statements) |
| `Entropic/Sweep` | final sweep: spin-3/2 pair projectors and transfer semigroup, Gaussian and Fourier integrals, S₇ orbit count, staggered constraint complex, Dirac frame flips, fused-label information cap, Hermite Gram matrix, v0.8 certificate instances |
| `Entropic/RetainedRelaxation.lean` | retained angular-marginal update of O.3 |
| `Entropic/Pass2` | second pass on the open claims: ladder Schur lemma and commutants (frame lock up to phase, block phases, V₀⊕V₁⊕V₂ commutant, spin-3/2 pair commutant via an integer coupled basis, H_mark → Q intertwiner and its uniqueness, SU(3) invariant form, real forms); first variation on ℝⁿ (integration by parts, fundamental lemma, Euler–Lagrange theorem) and the field equations of the two-potential, Newton, scalar and carrier actions; weak maximum principle and vanishing of decaying harmonic functions; curvature of conformally flat 3-metrics and the static weak-field expansion; tensor-product Lie generation (𝔰𝔩(mn)), 𝔰𝔩(16) from the spin-3/2 bilinears, 𝔰𝔩(64) and the 𝔰𝔩(81) bridge closure (complex forms) |
| `Entropic/EFT/` | v0.8 library, ported to Lean 4.35.0 (namespace `Entropic.EFT`) |

## Reproduce the check

Install the Lean toolchain manager (elan), then from this directory:

```sh
lake exe cache get
bash verify.sh
```

`verify.sh` builds the project, runs the axiom audit, and checks the audit
output. The `lean-toolchain` and `lake-manifest.json` files pin the compiler and
dependency revisions; do not run `lake update` if you want those exact pins.
The first setup needs internet access and several GB of disk space.

## Verification and trust

All theorems have proof terms checked by the Lean kernel. Physical premises are
theorem hypotheses or explicit definitions of the model. Statements over the reals
use mathlib's standard foundations (`propext`, `Classical.choice`, `Quot.sound`);
the audit log gives the count for the whole library and for `Entropic.EFT`.

The hosted verification environment needed an executable-path compatibility
shim for `/proc/<pid>/exe` discovery. Its source and explanation are under
`verification/`; it does not modify Lean's proof checker.

## Not formalized

The ledger gives a reason for each of the 143 statements marked not formalized.
The main groups are:

- pseudo-Riemannian curvature and variational calculus on manifolds (warped-product
  reductions, Bianchi identities, Euler–Lagrange equations of the field actions);
- unbounded operators and functional calculus (strong-resolvent limits, rigging maps,
  spectral measures);
- general SU(2) representation theory beyond the explicit j = 1, 3/2 and weight-count
  cases (Clebsch–Gordan for all spins, Schur uniqueness, coherent-state integrals);
- Haar integrals, Lie-closure computations (su(81), su(9^N)), Joyce's closed form for
  the diamond Green function, and simulation outputs.

No theorem asserts that the paper is physically correct or physically inconsistent.
