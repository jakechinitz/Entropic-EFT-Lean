# Entropic Scalar EFT: Lean formalization

[![build](https://github.com/jakechinitz/Entropic-EFT-Lean/actions/workflows/build.yml/badge.svg)](https://github.com/jakechinitz/Entropic-EFT-Lean/actions/workflows/build.yml)

This project formalizes the mathematical statements of Jacob Chinitz's
*Entropic Scalar EFT: From Entanglement Microstructure to Gravity and Cosmic
Structure* in **Lean 4.35.0 with mathlib**. The source record and the SHA-256
hash of the PDF used are in `provenance.json`. CI builds the library, runs the axiom audit
and the ledger citation check on every push.

## Effective dynamics and cluster extensions (2026-10-23)

Six modules under `Entropic/Extensions20261023` add 119 explicit theorem declarations to the import graph. The 154-module/2,812-theorem figures below identify the previously audited upstream snapshot; they are not recomputed totals for these additions. The normal pinned Lean 4.35 build and module-based axiom audit include all six modules. Their earlier standalone checks used Lean/mathlib 4.19. See [extension scope and provenance](verification/extensions_2026-10-23.md) for the distinction between conditional mathematics and empirical calculations.

## Status (2026-10-22)

| Item | Value |
|---|---|
| Library | one Lean library, `Entropic`: 154 modules, 2,812 theorems (the v0.8 library is its submodule `Entropic.EFT`, 727 theorems) |
| Axioms | every theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (`scripts/AxiomAudit.lean`, log in `verification/axiom_audit_chunk14_2026-10-22.log`) |
| Proof hygiene | no `sorry`, no custom axioms, no `native_decide`; finite enumerations and integer matrix identities are checked by kernel `decide` |
| Claim ledger | `ledger/LEDGER.md`: all 1,437 statements of the manuscript with kind and status |
| Ledger totals | proved 874, proved in part 90, numerical enclosures 59, data comparisons 64, physical premises 153, not formalized 143, simulation outputs 19, other 35 (interpretive, definitions, corrections, cited results) |
| Citation check | `scripts/CiteCheck.lean`: 979 Lean names cited in the ledger, 0 unresolved |

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
