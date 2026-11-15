# Clock attachment, direction records and scale-chain tests: manuscript and formalization map

The full manuscript of 15 November 2026 adds, in I.8, two event completions of the clock attachment; in I.9, the
direction-record identity for the Wilson operator, the relaxed-field statement, a four-row comparison of the matched
strong coupling and the leading-log scale relation; in Sections 13.5 and 27, the continuous coefficient fits and the
muon forward test; in C.8, fixed-exponent fits of the chain constant; in J.4, the label calculations on the inversion
complex. `Entropic/Extensions20261115/` formalizes the parts of these that are mathematical statements.

| Module | What is proved | Ledger |
|---|---|---|
| `DirectionRecord` | `W = (3/2)|V|² = 8(1 − |f|²/16)`; `W/8` as the direction weight of the port vector; hop `−it σ·V` and its determinant; `W ≤ (8/3)|k|²`; Bloch symbol `W/2` of the cell-projector sum; decay generator and `γ_W = (d/4L_*) s` | C10-105, C10-106, C10-107 |
| `ClockCoupling` | `d/L_* ∈ (1.07306, 1.07307)` and `γ_W ∈ (0.268265, 0.268268)` from the C.8 volume identification at `m₄ = 2.3219`; relaxed-field invariance; offsets and ordering of the four rows; `Δ ln Λ₃ = −(2π/9)Δα⁻¹` through fixed thresholds; ratios `0.51` and `4.1` | C10-108, C10-111, C10-112, C10-113 |
| `ScaleChainTests` | `n ∈ (7.02, 7.04)` with one-σ interval ends in `(6.59, 6.61)` and `(7.45, 7.47)`; seven unique among integers `n ≥ −200`; `q ∈ (0.286, 0.288)` with ends in `(0.276, 0.278)` and `(0.296, 0.298)`; `2/7` unique among rationals with denominator at most eleven; muon offset `5.34…5.37σ` at tenfold precision | C01-04, C01-05, C01-64, C03-175 |
| `ChainConstant` | calibration values at `m₄ = 2.3219` and at the three fixed-exponent fits; `G₀ < G_*` for `m₄ ≤ 2.3240` | C01-17, C05-83 |
| `LabelRing` | `Tr (NT)^q = Tr T^q` for even `q` when `NT = TN`, `N² = I`; `½ ln(27/8) ∈ (0.60819, 0.60821)` | C10-114 |

Inputs that the Lean takes as given and does not derive:

- the four matched inverse couplings `50.99`, `51.04`, `52.10`, `53.98` and the references `52.48`, `53.02`. They are
  numerical results of the stiffness, quark and matching calculations in `02 Research/Native color running
  2026-11-10`;
- the chain constants `2.3219`, `2.32163`, `2.32235`, `2.32103` (growth runs in `02 Research/Forward tests
  2026-11-09`);
- CODATA 2022 values of `G`, `m_μ/m_e` and `m_e`, and the PDG tau mass.

Not formalized, and recorded as premise or numerical in the ledger: the choice of clock attachment (C10-110), the
identification of the record damping with the Hermitian Wilson mass (C10-109), colour parallel transport in the record
operator, the random-timing gluon correction, two-loop matching, the forecast probabilities of Section 27 (C03-176),
and the ring residuals and determinant integrals of J.4.

Verification: each module was compiled with the pinned Lean 4.35.0 against the Mathlib cache for the pinned revision
and the existing modules it imports (`AppIJ.Color`, `AppCDE.Calibration`, `AppCDE.ElectronNumerics`, `Spine`). The
source scan passes. An axiom audit of the namespace `Entropic.Extensions20261115` reports zero nonstandard axioms. All
44 names cited in the ledger resolve to theorems. The full library build and the complete audits run in CI.
