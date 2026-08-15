# Build status — v0.8.0 (kernel-verified)

Version-by-version record. The current state is the v0.8.0 section near the bottom;
the sections below run in chronological order from the first kernel-checked build.

## Verified 2026-08-13 (v0.2.2)

`lake build` **completed successfully** (2,210 jobs) under Lean 4.33.0 with
Mathlib pinned at v4.33.0. All 43 modules elaborate and kernel-check.
`python tools/audit.py` passes independently (42 numerical checks).

Zero `sorry`/`admit`; zero project-level `axiom` declarations. Axiom footprint
of representative theorems (via `#print axioms`):

- `corrected_amplitude_factorization` (H.9 repair): `propext`, `Classical.choice`,
  `Quot.sound` only — i.e. standard Lean/Mathlib foundations, fully kernel-checked.
- `singleStrandZeroPointEnergy_eq_three_halves` (O.13 ledger): same, fully kernel-checked.
- `boundaryStates_card` (1,680-state count) and the eleven spectrum multiplicities:
  additionally trust `native_decide` (`ofReduceBool` — compiled evaluation rather
  than kernel reduction). To remove this trust, replace `native_decide` with
  `decide` and accept longer kernel evaluation.

## Changes from v0.2.1 (build-infrastructure + proof-engineering only; no semantic changes)

1. Imports moved above module docstrings in all 43 files (Lean 4 syntax requirement).
2. `EntropicEFT.Core.Prelude`: `import Mathlib` narrowed to 12 targeted imports
   (2,167 transitive modules instead of 8,690; per-module elaboration now seconds).
3. ~95 real/complex-valued `def`s marked `noncomputable` (compiler requirement; no
   proof content affected). One erroneous `noncomputable` on `edgeRecordCount : ℕ` reverted.
4. `Decidable PortAssignment.injective` instance: `inferInstance` → unfold-then-infer.
5. Tactic repairs: `Nat.choose` goals moved from `norm_num` to `decide`
   (BranchAudit ×4, Renewal, CorrectedH9); `simp`+`omega` → `unfold`+`ring_nf`+`omega`
   (SpinDimensions); over-closing `ring` after `field_simp` made conditional
   (Static, StrongField); `+ 0` rewrite closed by `simp` (SingleStrandRecord);
   `a0_closed` via `unfold`+`ring` (RankOne).
6. Missing imports added: `InnerProductSpace.Basic` (SharpTransfer),
   `SpecialFunctions.Pow.Real` (StrongField).
7. `Edge7`: `def` → `abbrev` so subtype `Fintype`/`DecidableEq` instances synthesize.

## v0.3.0 addition — premise instantiation (kernel-verified)

New module `EntropicEFT/Instantiation/ToyCDT.lean`. An explicit finite causal complex
(2 spatial cells x 3 causal layers, events carrying admissible codes from the verified
1,680-state ensemble) jointly realizes the interpreted premise set:

- all six `FoundationSpec` commitments (capacity, geometry=capacity, mass=entropy
  deficit, many pasts, tetrahedral 7^4 architecture, faithful per-layer resolution);
- `MarkedFusionIncidence` (9 record labels = nonmax complement dim at 2j=3, via the two
  independent upstream theorems);
- `SameClosureCouplingMarkedSource`, `SurvivalGapMassBridge` (real-analysis statement,
  exp of gap differences), `ReleaseTriggerIndependentOfClosure`,
  `EqualIRConversionNormalization`, `FixedContinuumEventMeasure` (discrete shadow).

Main theorem `premises_jointly_satisfiable : Nonempty ToyRealization` — axioms:
propext, Classical.choice, Quot.sound + the two native_decide certificates inherited
from the ensemble counts.

Deliberately NOT instantiated: GeometricEmbeddingSpec, TransverseInfluenceSpec,
StrongBoundarySpec, ArrowOfTimeSpec, CommonGeometryCapacityLimit, VolumeConjugacy,
CausticReleaseBridge. A finite toy cannot honestly witness continuum/dynamical
completions; this boundary is the informative part of the construction.

Methodological note: premise fields are Prop-slots, so trivial instantiation by `True`
is always possible and meaningless. The content is the interpretation map: every field
is discharged by a nonvacuous statement about the SAME explicit model. The theorem is
relative consistency of the interpreted premise set, not a statement about Nature.

## v0.3.1 — premise-faithfulness audit and strengthening

Self-audit of v0.3.0 found FIVE of twelve interpreted premises closed by `rfl`
(definitional tautologies doing no consistency work). Three were strengthened to
falsifiable content; two remain flagged as bookkeeping-grade.

Premise grading after strengthening:
- STRONG (falsifiable, nonvacuous): finiteLocalCapacity (membership in the verified
  1680 ensemble); manyPasts (explicit two-predecessor witness, decide); tetrahedral
  (7^4 = 2401 + injectivity); faithfulResolution (per-layer injectivity, decide);
  survivalGap (real analysis, exp of gap differences); markedIncidence (meeting of two
  independent upstream theorems); geometryCapacity (NEW: linkage iff channel-sharing,
  true only by 4+4 > 7 pigeonhole — false for an 8-channel alphabet, checked over all
  36 event pairs by decide); massEntropy (NEW: nonnegativity on 1..1680 and strict
  monotonicity via Real.log_lt_log); sameCoupling (NEW: reproduces the upstream H.9
  contraction u = 2(sqrt(eta) q)^2 = 8 eta/49, requires sq_sqrt, eta >= 0).
- BOOKKEEPING-GRADE (still near-definitional, honestly flagged): releaseTrigger
  (functional dependence on orientation only), equalConversion (1 = 1),
  fixedMeasure (state-independent count). These express structural choices of the toy
  rather than falsifiable constraints; strengthening them requires dynamical structure
  a static complex does not have.

Faithfulness caveat (unchanged): whether each interpretation matches the manuscript's
intended meaning is a physics judgment outside Lean. In particular markedIncidence is
a dimension-level shadow (9 = 9) of a representation-level identification; the full
premise also requires the specific intertwiner, which remains in the SU(2) certificate.

## v0.4.0 — certified root existence and uniqueness for eta*

New module `EntropicEFT/UV/RootExistence.lean`. Kernel-checked:

- `Z_pos`, `boundaryStates_nonempty`: partition function strictly positive (unconditional).
- `meanK2_bounds`: 122/3 <= <K^2>_eta <= 170/3 for EVERY real eta, proven from the
  finite-sum definition + the native_decide spectrum bounds. This DISCHARGES the
  `mean_bounds` field of the `GibbsAnalysis` certificate as a theorem.
- `stationary_root_exists (A : GibbsAnalysis)`: the stationarity equation
  eta * <K^2>_eta = 3/2 has a root in the exact rational window [1/100, 9/244], by IVT.
  Right endpoint uses the exact identity (9/244)*(122/3) = 3/2 — the cutoff-theorem
  coincidence used constructively.
- `closureProduct_strictMonoOn`, `stationary_root_unique (A)`: the closure product has
  derivative <K^2> - eta*Var(K^2) > 0 on the window (case split on the variance sign;
  eta*Var <= (9/244)*64 < 122/3), so the root is UNIQUE in the window.

Epistemic upgrade: the `stationary` field of `EtaStarSpec` no longer needs to be
asserted — existence and uniqueness follow from GibbsAnalysis's two remaining
derivative fields (`mean_deriv`, `evidence_deriv`) and `variance_bound`. Remaining
certificate content: those calculus fields (finite-sum differentiation of exp, a
mechanizable Mathlib exercise) and the thirteen-digit decimal enclosure (an interval
arithmetic project). Axiom footprint of all three theorems: standard foundations plus
the three native_decide enumeration certificates (ensemble card, spectrum min/max).

## v0.5.0 — gauge compatibility: the factor-split no-go

New module `EntropicEFT/Gauge/FactorSplit.lean` (response to the gauge-invariance
objection). Kernel-checked:
- `sameFactorGaussCasimir_noGo`: K² cannot be the local Gauss Casimir — a Gauss Casimir
  vanishes on physical states while the audited spectrum floor is 122/3 > 0 on the
  nonempty 1680 ensemble. Constructive use of the native_decide spectrum theorems.
- `leftFactor_commutes_rightFactor`, `leftObservable_gaugeInvariant`: exact commutation
  of open-factor observables with gauge-factor projections (the mechanism for
  [K², P_inv] = 0 with K² > 0).
- Mode arithmetic: dim Inv(V3^4) = 7; 7^4 * 7 = 16807 gauge-invariant fixed-spin modes;
  open-factor chain 2401 -> 840 -> 1680 tied to the audited cardinalities.
- `RelationalCapacityGaugeSplit`: the forced microscopic identification, stated as an
  explicit premise (NOT proven); its realization by a decorated G_v remains inside the
  open GeometricEmbeddingSpec.

## v0.6.0 — full gauge invariance propagated through the spine

New module `EntropicEFT/Gauge/SpinePropagation.lean`, incorporating the tightened
criterion: [O, P_inv] = 0 (subspace descent, for self-adjoint O) is WEAKER than full
kinematical gauge invariance [O, U(g)] = 0 for all g; the separated-factor construction
delivers the strong form. Kernel-checked:
- `fullGaugeAction_commutes`: open-factor operators commute with the ENTIRE gauge
  group action (for all g), axiom-free.
- Spine ledger (all rfl, totality is the point): sumM, sumSq, routeA/B/C, the
  injectivity predicate, quantumK3, classicalClosure3, quantumVariance3, quantumK2R,
  and the Gibbs weight at every eta — hence meanK2, varK2, and the stationary root
  inherit full gauge invariance wholesale.
- `parameter_spine_gauge_scalar`: scalarPassage (2/7), pairContractionU, edgeAmplitude,
  zeta, Ze carry no state argument and hence no gauge-factor dependence.
Remaining microscopic audit unchanged: the decorated G_v realizing the split lives in
the open GeometricEmbeddingSpec.

## v0.6.1 — compositional sufficiency for the decorated vertex
`assembled_transfer_gauge_commutes`: any finite composition of open-factor generators
commutes with every gauge transformation. Decoration locality of the generators alone
suffices for full gauge invariance of the assembled microscopic transfer.

## v0.7.0 — the decorated-vertex specification is jointly realizable

New module `EntropicEFT/Gauge/VertexRealization.lean`. Kernel-checked:
- `frame_realizes_closure` (axiom-free, pure `ring`): the explicit integer tetrahedral
  frame (1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1) — norms² 3, pairwise dots −1, cos = −1/3 —
  satisfies |Σ mᵢvᵢ|² = classicalClosure3(b) for EVERY boundary code. The soft closure
  operator is exhibited over a concrete gauge-independent architectural frame, closing
  the frame-provenance trap structurally.
- `vertexModel : DecoratedVertexModel` and `spec_jointly_realizable`: an explicit model
  witnesses all seven requirements at once — seven-channel alphabet; assembled-transfer
  gauge invariance via the CONSUMED sufficiency theorem (decoration locality is the only
  input); intertwiner rigidity (condensate sector exactly preserved); the frame theorem;
  exclusion stability; the ℤ₂ orientation involution (native_decide over 4802 states)
  doubling 840 to 1680; joint-measure factorization.
- Honest scope: j=3 selection is realized kinematically, not derived dynamically; the
  model realizes the SPECIFICATION, not the GFT condensate. Deriving this structure
  from an actual decorated GFT field remains the physics program.

## v0.8.0 — FINAL RELEASE: structural connections

New module `EntropicEFT/Structure/Connections.lean`. Kernel-checked, full build green
(2,231 jobs, 48 modules, 0 sorries, 0 project axioms):

1. `universal_channel_sharing` — any two admissible states share a channel (proved via
   the 35x35 subset-level pigeonhole `four_subsets_share`, 4+4 > 7, lifted through
   `support_card_four`). The capacity graph on the ensemble is COMPLETE: locality must
   be dynamical, matching the sim's measured correlation length xi ~ 0.57.
2. `johnson_fibration` — the ensemble fibers over the 35 four-subsets (Johnson scheme
   J(7,4)) with constant fiber 48 = 24 orderings x 2 orientations. The sim's 48x35
   locality fracture, as combinatorics.
3. `unweighted_mean_exact` — Sum of 3K^2 over the ensemble = 255360 exactly: the flat
   mean of K^2 is 152/3; the measured Gibbs mean ~50.223 = exact rational + certified
   tilt at eta*.
4. `closureVec_bcc` (near-axiom-free, pure algebra) — every closure vector has
   all-equal coordinate parity: resolved nonclosure is quantized on the BCC sublattice
   of Z^3.
5. `three_halves_bridge` — the stationarity target and the single-strand zero-point
   energy are the same rational, linking RootExistence and SingleStrandRecord.
6. `stationarity_bracketing` — general lemma: roots of eta*M(eta) = c with
   M in [lo,hi] lie in [c/hi, c/lo]; the eta* window is the instance. Theory-free,
   candidate for upstreaming.

## RELEASE SUMMARY (v0.2.1 -> v0.8.0, this session)

- v0.2.2: first kernel-checked build ever (import order, noncomputable, tactic repairs)
- v0.3.x: premise set jointly satisfiable (ToyCDT), vacuity audit + strengthening
- v0.4.0: eta* root existence + uniqueness (IVT at the exact 9/244 endpoint)
- v0.5.0: gauge no-go (K^2 is not the Gauss Casimir) + factor split
- v0.6.x: full-gauge-action spine ledger + compositional sufficiency (axiom-free)
- v0.7.0: decorated-vertex spec jointly realizable; frame realization theorem
- v0.8.0: structural connections (complete capacity graph, Johnson fibration, exact
  flat mean, BCC quantization, 3/2 bridge, bracketing principle)

Trust base throughout: propext, Classical.choice, Quot.sound + enumerated
native_decide certificates (finite combinatorial counts only). All physical premises
explicitly named as structures; all Math certificates (Gibbs derivative fields, SU(2)
intertwiner construction, 13-digit eta* enclosure) explicitly declared as external.

## Continuous verification (added with the GitHub setup)

From this point the build is no longer verified only on the author's machine.
`.github/workflows/build.yml` runs on every push and pull request:

1. `leanprover/lean-action@v1` installs elan, honours `lean-toolchain` (Lean 4.33.0),
   fetches the Mathlib cache, and runs `lake build` on the default target. Dependency
   revisions come from the committed `lake-manifest.json`; CI never runs `lake update`,
   so the pinned Mathlib revision cannot drift underneath the build.
2. The build log is scanned for `declaration uses 'sorry'` and the job fails if any
   appears — `lake build` only warns on `sorry`, it does not fail.
3. `Scripts/AxiomAudit.lean` runs `#print axioms` over the headline theorems listed in
   the sections above, and `tools/check_axioms.py` fails the job if any of them depends
   on an axiom outside `{propext, Classical.choice, Quot.sound, Lean.ofReduceBool}`.
   `sorryAx` is deliberately absent from that allowlist. The captured footprint is
   uploaded as a CI artifact so the axiom lists can be read directly rather than taken
   on trust.
4. A separate job runs `tools/syntax_sanity.py` and `tools/audit.py` (the independent
   Python re-derivation, 42 numerical checks) on a clean Python 3.12 environment.

`.lake/` is gitignored: the repository ships sources and pinned revisions, not build
artifacts, so a green badge means the code was rebuilt from scratch on infrastructure
nobody involved in the project controls.

Scope of the badge, stated plainly: it certifies that the Lean kernel accepts these
proofs and that their axiom footprint is the declared one. It certifies nothing about
whether the named physical premises hold, whether the interpretation map to the
manuscript is faithful, or whether the open interfaces can be filled.
