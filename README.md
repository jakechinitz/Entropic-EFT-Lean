# EntropicEFT — Lean formalization

[![build](https://github.com/jakechinitz/Entropic-EFT-Lean/actions/workflows/build.yml/badge.svg)](https://github.com/jakechinitz/Entropic-EFT-Lean/actions/workflows/build.yml)

**What this repository proves and what it does not:** the finite combinatorial and
algebraic content of *Entropic Scalar EFT* — the 1,680-state boundary ensemble and its
exact K² spectrum, the corrected H.9 closure decomposition, existence and uniqueness of
the stationary η\*, the gauge factor-split no-go, and the joint satisfiability of the
interpreted premise set in an explicit finite model — is machine-checked by the Lean 4
kernel; the *physical* content — that this microstructure describes Nature — is not
proved here at all, and is instead carried by explicitly named premise structures,
external mathematics certificates, and open interfaces that this repository deliberately
leaves unfilled.

Nothing below upgrades that sentence. Every green check on this page is a statement
about a finite formal object, not about the universe.

Audited manuscript SHA-256:

```text
bec8390dec21af31fa5c1e3ca8c26503e664ee66ddb679d6f4085dba5e9882c7
```

## Trust base

If you are deciding how much weight to put on the badge above, this is the complete
answer. A theorem in this repository rests on exactly three kinds of thing:

1. **Standard foundations.** `propext`, `Classical.choice`, `Quot.sound` — the ordinary
   axioms of Lean 4 and Mathlib, and nothing else. There are zero project-level `axiom`
   declarations and zero `sorry`/`admit` holes; CI fails if either appears.
2. **Enumerated `native_decide` certificates.** The finite combinatorial counts (the
   1,680-state cardinality, the eleven spectrum multiplicities, the ℤ₂ orientation
   doubling over 4,802 states) are discharged by compiled evaluation rather than kernel
   reduction, which means trusting the Lean compiler in addition to the kernel. This
   trust is removable in principle by replacing `native_decide` with `decide` and
   accepting a much longer kernel evaluation; it is *not* removed here. These are the
   only places the kernel is bypassed, and they are all finite enumerations.
3. **Named physical premises and external mathematics.** Everything that is a modelling
   commitment is a Lean *structure* with named fields — `SurvivalGapMassBridge`,
   `MarkedFusionIncidence`, `FixedContinuumEventMeasure`, `RelationalCapacityGaugeSplit`,
   and so on — never an axiom and never a theorem. Ordinary mathematics not mechanized
   here (the SU(2) Clebsch–Gordan construction, the finite-Gibbs derivative fields, the
   thirteen-digit η\* interval enclosure) is likewise a `...Math` certificate structure.
   Consuming one of these is visible in the type of every theorem that depends on it.

Categories 1 and 2 are checked mechanically on every push: `Scripts/AxiomAudit.lean`
runs `#print axioms` over the headline theorems and `tools/check_axioms.py` fails the
build if anything outside that allowlist — `sorryAx` above all — appears. The captured
footprint is uploaded as a CI artifact, so you can read the actual axiom list for
yourself rather than trusting this paragraph.

Category 3 is not mechanically checkable, and that is the point. Formalizing a premise
must not make the premise look derived. `EntropicEFT/OpenProblems/Interfaces.lean` is the
one-stop index of what remains open: the GFT/CDT embedding, the transverse influence
functional, the strong-field boundary theory, and arrow-of-time typicality all have
interfaces with no global instance.

## Design goal

The repository is deliberately **not** one giant proof file. Every Lean module begins
with a `LOCAL CONTRACT` specifying:

- manuscript location;
- what is defined locally;
- what is proved exactly;
- which inputs are ordinary external mathematics;
- which inputs are physical/model assumptions;
- what remains open.

A reader — human or LLM — should therefore be able to inspect one module without
reconstructing the full manuscript.

## Epistemic rule

1. **Exact finite/algebraic content** is stated as Lean definitions/theorems.
2. **Ordinary mathematics not yet mechanized in this repository** is represented by a
   narrowly scoped `...Math` certificate structure (for example the full SU(2)
   Clebsch–Gordan construction or finite-Gibbs differentiation).
3. **Physical bridges** are explicit structures such as `SurvivalGapMassBridge`,
   `MarkedFusionIncidence`, or `FixedContinuumEventMeasure`.
4. **Open completions** are interfaces with no global instance: GFT/CDT embedding,
   transverse influence functional, strong-field boundary theory, arrow-of-time
   typicality, etc.
5. **Empirical results** are data/status certificates, never Lean theorems about Nature.

## The H.9 repair

The repository incorporates the corrected closure decomposition

```text
K^2 = |c|^2 + V_q
```

rather than the inconsistent identification `K^2 = |c|^2` that appeared in H.9. The full
renewed amplitude is exactly factorized into

```text
exp(-eta K^2/2)
  = exp(-eta V_q/2) * exp(-eta |c|^2/2).
```

Only the genuine three-component vector `c` is Gaussian-linearized. The scalar
quantum-variance factor stays in the native fresh-state amplitude. The normalized
vector-response coupling remains `sqrt eta`; the minimal marked source then *explicitly*
reuses that coupling rather than pretending this reuse follows from the Gaussian identity
alone.

See `EntropicEFT/Marked/CorrectedH9.lean`.

## Single-strand record ledger (H.9 → O.13)

`EntropicEFT/Marked/SingleStrandRecord.lean` makes the record-energy ambiguity explicit.
The finite selected model contains one three-mode canonical phase space, so Lean-level
bookkeeping gives exactly three coordinate/momentum pairs and zero-point ledger `3/2`.
The nine marked labels are matrix-unit/operator labels `(a,b)` with identity
Hilbert–Schmidt Gram; they do **not** create nine (or six) independent oscillators.
On the degenerate first-excitation triplet the difference-sign Liouvillian has eigenvalue
zero. A literal two-deposit countermodel is represented by a different type containing two
phase spaces; it has six pairs and zero-point energy `3`.

The repository deliberately does **not** claim that Hubbard–Stratonovich integration alone
proves this physical oscillator realization. The identification of the single `d^3 xi`
auxiliary with one canonical oscillator strand, the operator-dual history reading, the
difference-sign `W_*` dynamics, and fresh-per-vertex preparation are packaged as
`SingleStrandCanonicalRealization`. Once that realization is adopted, O.13 no longer takes
`3/2` as an arbitrary input: it imports the exact finite ledger theorem. The further
identification of that ledger with physically released IR energy remains an explicit
bridge.

A Tomita–Takesaki/GNS interpretation is compatible with the finite operator-doubling
picture, but is not claimed as a theorem here: a full modular statement would require a
specified von Neumann algebra, state, and cyclic/separating hypotheses.

## Main directories

- `Core/` — shared notation, claim status, physical interfaces.
- `Foundations/` — postulates/operational inputs without physical axioms.
- `UV/` — 1680-state ensemble, closure invariant, exact spectrum, Gibbs closure, eta audit.
- `Representation/` — twice-spin arithmetic, 7+9 complement specification, sharp transfer.
- `Information/` — classical replacement/maximum-caliber separation.
- `Quantum/` — replacement channels, histories, records, no-signaling interfaces.
- `Marked/` — corrected H.9, single-strand/operator-record ledger, and 21-edge graph.
- `Scale/` — recurrence, electron scale, lepton shell algebra.
- `Edge/` — tetrahedral isotropy, edge kernel, source projection.
- `Gravity/` — static capacity/Einstein branch, field variables, strong spherical branch.
- `Gaussian/` — finite covariance determinant/KL bridge.
- `Transverse/` — rank-one galactic EFT algebra and open influence-functional gate.
- `Transport/` — telegrapher branch.
- `Cosmology/` — saturated dust, fixed-measure/unimodular dark-energy algebra, O.13 gate.
- `Gauge/` — factor-split no-go, gauge propagation, decorated-vertex realization.
- `Lattice/` — exact finite-regulator identities and empirical/open simulation certificates.
- `Clusters/` — cluster bookkeeping and open map test.
- `Microstructure/` — native gate and geometric embedding obligations.
- `Numerics/` — interval-certificate interfaces for transcendental numerical spine.
- `Structure/` — cross-cutting connections (complete capacity graph, Johnson fibration,
  exact flat mean, BCC quantization, the 3/2 bridge, stationarity bracketing).
- `Instantiation/` — the explicit finite ToyCDT model realizing the premise set.
- `Audit/` — cross-sector identities and machine-readable Section 26 claim ledger.
- `OpenProblems/` — one-stop unresolved-completion index.

## Reproducing the build

The project is pinned by `lean-toolchain` and `lakefile.toml` to Lean/Mathlib
**v4.33.0**, with exact dependency revisions in the committed `lake-manifest.json`.
Build artifacts (`.lake/`) are deliberately not committed — the claim is that you can
rebuild this, not that you can download it.

```bash
elan toolchain install $(cat lean-toolchain)   # if you do not already have it
lake exe cache get                             # prebuilt Mathlib oleans
lake build                                     # ~2,231 jobs, 48 modules
lake env lean Scripts/AxiomAudit.lean          # trust base, printed
```

Do **not** run `lake update`: it would re-resolve dependencies and discard the pinned
revisions in `lake-manifest.json`.

The independent Python audit re-enumerates the 1,680 states and re-derives the complete
K² spectrum, the corrected H.9 decomposition and bounds, η\*, the sharing entropy, the
marked transfer, L\*, G\*, the lepton ratios, and several cross-sector cancellations —
from the manuscript definitions rather than from the Lean sources:

```bash
pip install scipy
python tools/audit.py
```

It is a cross-check on whether the Lean definitions mean what they are said to mean. It
is not a proof checker, and it is not a substitute for `lake build`.

Both are run on every push by [`.github/workflows/build.yml`](.github/workflows/build.yml).

## Reading strategy

If asked about one result, open only its module and its direct imports. Do **not** assume
a structure field is proved merely because it exists. The suffix conventions are useful:

- `...Math` = ordinary mathematics proof obligation / certificate;
- `...Spec`, `...Bridge`, `...Completion`, `...Target` = conditional physical or model
  content;
- theorem with no such input = intended exact formal consequence.

See `MANUSCRIPT_MAP.md` for the module ↔ manuscript map, `SECTION_REVIEWS.md` for the
per-section audit notes, and `BUILD_STATUS.md` for the version-by-version record of what
was verified when.

## Citing

Releases are tagged and immutable; cite a tag (for example `v0.8.0`) rather than a branch.

## License

Apache License 2.0 — see [LICENSE](LICENSE).
