# Assumption compatibility (2026-10-23)

Source: Sol and Fable / 02 Research / Assumption compatibility 2026-10-23 (built there with Lean 4.19). Integrated here on Lean 4.35 against the unchanged upstream modules; the 4.19 portability patch is not used. Porting changes: closers after `convert ... using 1` (4.35 leaves the function-equality goal), `ZMod.natCast_eq_zero_iff`, `Fintype.card_fin` ordering in GibbsHistory, removal of `ring` after `field_simp` where it now closes the goal, and lower-case emphasis in two doc comments. The standalone `Audit.lean` script is replaced by the repository axiom audit. `Entropic/Completion/InfiniteHistory.lean` is a snapshot of the in-progress Full compatibility closure folder; its other modules are not yet integrated.

## RESULTS.txt (verbatim)

```
ASSUMPTION COMPATIBILITY — 23 OCTOBER 2026

Result
======

The supplement proves Nonempty EffectiveModel for a specified, nontrivial
effective subsystem. It does NOT prove that every physical assumption in the
four publications has a common realization. That larger claim remains open.

The main theorem is:
  Entropic.Compatibility.effective_assumptions_compatible
in formalization/Entropic/Compatibility/All.lean.

This is an inhabited structure of actual equations and inequalities. It has
no arbitrary Prop-valued premise slots filled with True, no admitted proofs,
and no additional physical axioms. The proof is relative to Lean's ordinary
classical foundations. See VERIFICATION.json and the saved audit log for the
final build and axiom-check results.

What is tied together
====================

1. One native eta solves the exact finite-ensemble stationarity equation.
   The imported, checked closure proof brackets eta and its sharing entropy.
   The same eta gives epsilon = gshare/(4*pi^2), the selected muon and tau
   ratios, the Gibbs law, the formation inventory, and the release law.
   Different EffectiveModel values cannot choose different stationary eta.

2. A native Gibbs sample space has 1680 states, indexed by the eleven certified
   energy levels and their degeneracies. For every finite duration n, its
   product-history law is normalized, strictly positive on every word, and
   consistent under removing the last sample. Appending a sample is injective
   on the previous history plus that sample. The archive has 1680^n states.
   This is an exact family of finite laws, not a claimed infinite quantum
   history construction. It uses the nonuniform Gibbs marginal.

3. The selected six-label shell sector has an explicit reversible 720-cycle.
   Its invariant uniform law, first return of exactly 720, and arithmetic
   mean return of 720 are proved. A separate theorem proves that this cycle
   is NOT full-support memoryless renewal. The cycle and Gibbs history have
   different variables and different laws; they are not silently identified.

4. The same finite stock is used in positive reconstruction, redistribution,
   and reciprocal forces. There are two distinct positions, strictly positive
   baryons and stock at each position, a positive unreleased donor, and a
   redistribution that actually changes the initial stock. Reconstruction
   and redistribution preserve its mass; the total pair force vanishes.
   With a positive Newton coefficient, their mutual Newton force is proved
   nonzero, so the force witness cannot collapse to a zero interaction.
   This is an algebraic force certificate, not a solution of a two-body PDE.

5. At a strictly positive time in an explicit expanding solution, the sums
   of those finite baryons and retained stock equal the homogeneous baryon
   and retained densities (in a unit physical-volume inventory convention).
   The unreleased stock and release fraction agree as well. Their exponential
   allocation uses the same epsilon and eta. Thus the witnesses are connected
   by their actual mass budget, not merely by a list of unrelated examples.
   The two-point discretization is NOT an inhomogeneous solution of that FLRW
   metric. Establishing that spatial/dynamical interface is still required.

6. A mass-normalized positive projection is proved, including a signed target
   with a genuinely negative cell. The projected mass is the same retained
   budget. Its target changes when positivity requires it. The theorem does
   not assert the raw RAR remains exact after clipping.

7. The expanding solution has a nonzero interval on the unchanged dust branch
   of the selected depletion action, with one fixed positive floor K and
   0 < 3(K-V) < C. A separate intermediate depletion state and a contact with
   nonzero heat, work, and admissible work-register endpoints are exhibited.
   Neither certificate derives the constitutive law or its microscopic rate.

The continuous example
======================

In units c = 1 and 8*pi*G = 1, write e(t) = exp(-t), and set

  H(t) = 1/8 + e(t)/24,
  a(t) = exp(t/8 + (1-e(t))/24),
  D(t) = e(t)/12,
  V(t) = 3 H(t)^2 - D(t),
  Q(t) = D(t) [1 - 3 H(t)],
  b(t) = epsilon/[12(1+epsilon)] * a(t)^(-3),
  C(t) = D(t) - b(t).

Lean proves a' = H a, H' = -D/2, 3H^2 = b+C+V, b' = -3Hb,
C' = -3HC-Q, and V' = Q. Thus both flat homogeneous Einstein equations and
the component energy balances hold, not just a conservation identity with
an externally guessed expansion rate. For t >= 0, H > 0, a > 0, Q > 0 and
V >= 0. Initially a = 1, V = 0, b > 0, C > 0 and C = b/epsilon.

Define

  F(t) = -log(a(t)^3 C(t)/C(0))/eta,
  u(t) = (1-F(t)) C(t),
  R(t) = F(t) C(t),
  Gamma(t) = Q(t)/[eta C(t)(1-F(t))].

On a proved positive-duration interval, C > 0 and 0 <= F < 1; at positive
times F > 0. Lean proves F' = Q/(eta C), Gamma*u = Q/eta, both u/R evolution
equations, and C = (b/epsilon) exp(-eta F). A fixed K can be chosen so the
solution also remains in the original dust branch of the depletion action
on a positive interval. No numerical integration or simulation was used.

The interval restriction is essential. Baryons decay more slowly than D in
this analytic example, so its donor cannot remain positive for all time.
This is a local existence witness, not the fitted cosmic history, a global
depletion solution, or a resolution of cosmological caustics.

The two incompatibility certificates
====================================

A. FiniteArchive has no values. Exactly recoverable independent binary
   alternatives for every duration cannot fit a single fixed finite capacity.
   This is stronger than checking a particular finite permutation. The full
   paper's current P.9 explicitly supplies an unbounded exported archive, so
   this is NOT a refutation of that current branch. Requiring fixed total
   capacity would reintroduce the contradiction.

B. ExactDenseCore has no values. A positive-amplitude uniform baryonic core,
   the exact unprojected exponential RAR stock profile, a coordinate x >= 6,
   and a nonnegative stock derivative cannot hold together. The derivative
   is computed from the actual exponential profile. The current positive
   projection drops the raw exact-profile requirement; its finite analogue
   is compatible. No complete continuum projected galaxy is proved here.

What changed relative to the quoted proposal
============================================

The proposed strategy was sound, but two factual descriptions need updating.
The current full paper already distinguishes the unbounded history archive
from finite present capacity. Also, the current ToyCDT realization supplies
concrete interpretations; it is not simply the old True-filled placeholder.
It still does not establish full physical compatibility: its same-layer
injectivity is weaker than an indefinitely faithful IID history, and its
toy geometry is not an interacting Einstein/galaxy/cosmology realization.

The four papers also contain alternative normalizations and older benchmark
branches. Examples include G_* versus the angular bare G_0 and the historical
linear-depletion fit versus the positive-allocation fit. Conjoining mutually
exclusive choices would manufacture a contradiction. Observational scores,
finite simulation outputs, and open conditional inheritance hypotheses have
not been converted into axioms or exact observational equalities here.

Remaining full-model obligations
===============================

See ASSUMPTIONS.txt for the sector inventory. The decisive unfinished step is
a common spatial dynamics and geometry: one metric and stock field must
support cosmological release, nonnegative dense-core/galaxy profiles,
reciprocal multibody transport, and the selected microscopic realization.
The finite maps and the homogeneous solution do not establish that step.

The native interacting Einstein regime, common matter cone, physical
constraint space, carrier projector, formation/transport laws, saturation
boundary, and empirical likelihood requirements remain additional work.
No claim of a full consistency proof or of agreement with nature is made.

Reproduction and handoff
=======================

Run from the workspace root:
  python -X utf8 "02 Research/Assumption compatibility 2026-10-23/verify.py" Entropic.Compatibility.Audit

The available local toolchain is Lean/mathlib 4.19; the active upstream
repository declares 4.35. The supplement uses an isolated copy of only its
required dependencies. PORTABILITY.patch records the changes needed by the
older compiler, including a freshly proved log(2) enclosure. New compatibility
sources should be integrated into Claude's 4.35 branch and checked there;
the upstream dependency copies should NOT overwrite that branch.

All 221 original source inputs were preserved byte-for-byte in
source_snapshots/20261023_170600, with SHA-256 hashes. Papers, PDFs, the active
Lean project, and simulations were left unchanged. Compiler products and all
attempt logs are retained under 05 Build Files/Assumption compatibility
2026-10-23. New builds use separate object directories to preserve prior
products. This folder is the reviewable handoff; nothing was published or
sent to another task.
```

## ASSUMPTIONS.txt (verbatim)

```
PHYSICAL-ASSUMPTION INVENTORY AND FULL-MODEL BOUNDARY

Scope: current full, compact, empirical and microstructure source snapshots
dated 2026-10-23, followed by the current Lean sources and claim ledger.
This is a sector-level inventory of premises and interfaces. It is not a new
claim that every displayed equation in the full manuscript is formalized.

Reading anchors
---------------
Full: physical commitments and faithful resolution in sections 1–4; finite
ensemble and scale chain in 5–14; galaxy/contact/carrier choices in 15–18;
cosmology in 19–20 and O.3/O.15; strong-field domains in 21 and F/N.6; history
and microscopic realization in 22–25 and H/P/Q; section 26 closure table;
J.12–J.14 connected CDT and measurement; P.9 exported record capacity.
Compact: the corresponding framework, coefficient, galaxy, source-clock,
history, microscopic and falsifiability sections, including its older
benchmarks and explicit separation of return statistics.
Empirical: all result families, with particular attention to acceleration,
retention, dwarfs, positive-allocation cosmology, clusters, cross-sector
tests and interpretation/audit. These are measurements and conditional
calculations, not a simultaneous system of exact physical equations.
Microstructure: capacity/records, coherent bonds, connected geometry,
CDT/Einstein inheritance, clock and orbital motion, refinement, comparison,
replication and appendices. Selected finite maps are distinct from a measured
interacting continuum phase.
Lean: foundation/toy interfaces; finite ensemble/root/spine; spherical law;
positive ledger/reconstruction/relaxation; history capacity and reciprocity;
the new connected-closure/contact extensions; repository scope and open-claim
triage. Existing proved claims remain claims about their explicit hypotheses.

Status key
----------
JOINT: included with a witness in EffectiveModel or an immediate theorem on it.
SECTOR: a narrower mathematical result exists, without the complete interface.
OPEN: no full realization is constructed in this supplement.
BRANCH: the premise requires a declared choice and must not be mixed with an
incompatible alternative. DATA: observational/numerical claim, not an axiom.

1. Local finite capacity and a geometric substrate — SECTOR/OPEN
   A 1680-state native statistical factor is explicit. A common spacetime
   substrate realizing that factor, all defects and interacting geometry is
   not built. Local finite capacity does not imply finite total history.

2. Geometry/capacity equivalence — OPEN/BRANCH
   Weak-field fractional deficit, clock lapse q_tau, radial mass invariant
   q_geo, and a generic covariant capacity observable are not interchangeable.
   Inside matter q_tau and q_geo generally differ. A full structure needs
   their domains and proved maps, not global equality by definition.

3. Matter as committed capacity — JOINT/OPEN
   The same positive baryon/stock inventories enter normalization and force
   algebra. The electron anchor and stable microscopic defect interpretation
   are physical inputs; a fully coupled matter action is not constructed.

4. Tetrahedral native ensemble — JOINT/SECTOR
   Four ordered distinct labels from seven, two orientations, the exact
   spectrum, stationary eta and selected sharing entropy are checked in the
   dependency chain. The physical selection of this architecture is a premise.

5. Spin matching and 16 = 7 + 9 — SECTOR/OPEN
   Sharp maximal-spin matching and the complete marked complement are selected
   microscopic conditions. Reducible complement locks allow block phases.
   No full gauge-constrained interacting spin-network witness is added here.

6. Faithful temporal resolution — JOINT/BRANCH
   Exact finite product histories at the native Gibbs law are constructed.
   Their archive grows as 1680^n. Fixed finite faithful archives are impossible.
   Infinite quantum histories, physical export, and a common geometric state
   remain open. Finite periodic dynamics cannot replace exact IID renewal.

7. Many-Pasts and operational quantum mechanics — SECTOR/OPEN
   The current toy and retained-sector theorems do not select the global
   cosmological state, actual decohering histories or durable record capacity.
   The probability/record assumptions must be interpreted on the same quantum
   system as the geometry, rather than satisfied by unrelated sample spaces.

8. Shell support and pole-mass assignment — JOINT/BRANCH
   Arithmetic mean return 720 has a nontrivial reversible witness; the selected
   muon/tau formulas use the same eta. Pole-mass identification, coherent
   overlap, charged generator and dimensional electron calibration remain
   selected physical attachments. The cycle is not the Gibbs renewal process.

9. Stiffness and physical Newton constant — SECTOR/BRANCH/OPEN
   Finite edge/source arithmetic does not determine the physical interacting
   Newton coefficient. C.5 matched G=G_* and C.8 provisional angular G_0/G_*
   about 1.03002 are different prescriptions. They cannot both be demanded as
   an exact equality to the same coefficient without an additional match.

10. Microscopic geometry and connected CDT host — SECTOR/BRANCH
    Positive pair parents, normalized chain/cycle interfaces, alpha=7 geometry,
    selected Regge weights and finite operator refinements are narrower than
    an interacting Einstein regime. The six-cell abstract network is not
    automatically a tetrahedral three-ball. Host measure and volume control
    must be common across microscopic, source and continuum calculations.

11. Interacting continuum and clock/cone matching — OPEN
    Required: one common physical constraint space, positive state/rigging
    prescription, infrared tensor sector, matter cone, source response and
    normalization. A supplied operator preserved by cochain refinement is
    not an existence proof of the native interacting limit.

12. Einstein parent and homogeneous matter — JOINT/OPEN
    Both flat homogeneous Einstein equations and the positive-interval
    baryon/donor/vacuum system are verified analytically. A Lorentzian manifold,
    full variational derivation, galaxy embedding and inhomogeneous constraints
    are not included. Time and G are fixed by the explicitly stated units.

13. Horizon/phase-cell loading — JOINT/BRANCH
    The same epsilon supplies a0=epsilon*c*H and the initial donor/baryon ratio
    1/epsilon. Their algebraic cross-sector identity is proved. Loading one
    sharing entropy in a (2*pi)^2 cell and the physical bath coupling remain
    physical premises, not consequences of compatibility alone.

14. Exact raw RAR with positive stock — INCOMPATIBLE strengthened branch
    A positive uniform core at x>=6 contradicts nonnegative stock density if
    its enclosed stock is the raw exponential target exactly. This is proved
    by IsEmpty ExactDenseCore. The current projection explicitly changes that
    target; it must not be supplemented by the discarded exact-profile clause.

15. Positive projection and finite redistribution — JOINT/OPEN
    Clipping/normalization preserves a nonzero common stock budget; finite
    redistribution preserves mass and changes a disequilibrium. Neither
    result constructs a continuum dense-core equilibrium, nor derives its
    kinetic target, energy supply, time scale or formation history.

16. Carrier labels and spatial reconstruction — SECTOR/OPEN
    Sharp projectors concern the record algebra; positive overlapping spatial
    kernels are reconstruction maps. These need not be sharp spatial masks.
    A microscopic label, common resolution and evolving carrier projector are
    still needed. The tensor/director contact's nonlinear covariant variation
    and interface forces must be checked on the same fields.

17. Reciprocity and stock inertia — JOINT/OPEN
    The common baryon-plus-stock masses yield pair reciprocity and zero total
    force. The finite stock is explicitly apportioned from the homogeneous
    retained inventory. Spatial self-consistent gravity and evolution of that
    apportionment are not proved. Baryons alone cannot absorb unequal source
    weights without the required additional momentum carrier.

18. Source recruitment and ancestral budgets — JOINT/BRANCH/OPEN
    Initial C=b/epsilon and exponential release allocation are linked.
    Label inheritance, no new recruitment of old baryons, and a formation
    vertex with an energy source remain selected microscopic conditions.

19. Composition-preserving positive release — JOINT
    One analytic solution satisfies u+R=C, q=Gamma*u, Q=eta*q,
    u'+3Hu=-q-uQ/C, R'+3HR=q-RQ/C and V'=Q. It starts with V=0 and
    remains nontrivial and positive on a proved interval. Gamma is constructed
    from that solution; no claim is made that it is the empirically selected
    assembly/mixing kernel. Global continuation is not proved.

20. New depletion action — JOINT/BRANCH/OPEN
    One positive K keeps the same cosmological solution in the original dust
    branch locally. An intermediate state is explicitly admissible as well.
    The cubic completion and floor are constitutive choices; nonzero-null
    interfaces, caustics, multistream evolution and global regularity remain
    unresolved. The theorem never assumes that an arbitrary drain preserves
    positivity forever.

21. Finite-work contact and warm stress — SECTOR/BRANCH/OPEN
    Nonzero heat/work and admissible register endpoints coexist. Existing
    contact identities and characteristic bounds are checked dependencies.
    They do not select the thermal target, spatial force law, rate, work
    reservoir or warm exponent, and do not prove a coupled spatial solution.

22. Clusters and Bullet — DATA/OPEN
    A positive transport inventory is not an assembly history. Central pair
    events conserve momentum/energy in the effective model, but the Bullet
    few-kpc alignment is below the illustrative simulation resolution. A
    common fit to lensing, gas, offsets and isolated stability is still needed.

23. Bounded capacity, horizons and strong fields — BRANCH/OPEN
    Radial q_geo=0 can mark a marginal surface. Domain termination at exhaustion,
    causal saturation dynamics, boundary action and reflectivity do not follow
    from that equality. Nonspherical/rotating capacity maps remain required.

24. Vacuum normalization and initial vacuum — BRANCH/OPEN
    Energy-origin invariance of probabilities does not itself fix gravitational
    vacuum stress. The analytic example adopts V(0)=0 and generates positive V.
    Physical selection of that condition and of the regulator subtraction is
    not established by the witness.

25. Empirical agreement — DATA
    Approximate mass ratios, RAR residuals, CMB/lensing likelihoods, dwarf and
    high-redshift tests, cluster maps and tensor comparisons are not exact
    simultaneous equality assumptions. The empirical paper identifies tensions,
    overlapping datasets, historical controls and unconverged components. A
    future full model must make forward predictions with declared uncertainties;
    adding reported central values as axioms would be unjustified.

Concrete next theorem for the full program
-----------------------------------------
Construct a nonempty class of one-metric spatial solutions with:
  - positive initial baryon and donor fields with the native formation budget;
  - the selected local action and covariant conserved total stress;
  - nonnegative stock through dense cores and a specified projection/contact;
  - nonzero two-body dynamics and homogeneous expanding limits;
  - fixed carrier/release laws, causal local bounds and admissible boundaries;
  - a microscopic state/operator family whose coarse observables are THESE
    fields, with one physical G and a common matter/tensor cone.
The existing sector constructions and the new mass-budget link are useful
constraints on that task. They do not supply its missing spatial existence
and microscopic matching theorems.
```
