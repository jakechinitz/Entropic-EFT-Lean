# Full compatibility closure (2026-10-23)

Source: Sol and Fable / 02 Research / Full compatibility closure 2026-10-23 (built there with Lean 4.19). Integrated here on Lean 4.35 against the unchanged upstream modules and the active `Entropic.StockSettling`; the 4.19 portability patch is not used. Porting changes: closers after `convert ... using 1` (4.35 leaves the function-equality goal), `HasDerivAt.fun_sub`, `Real.log_prod` implicit arguments, `abs_add_le`, spaces around `≤` (the 4.35 parser rejected forms such as `0≤s`), commuted nonzero hypotheses for `field_simp`, `field_simp <;> ring` where `field_simp` now closes the goal, and lower-case emphasis in doc comments. GPT's standalone `Audit.lean` is replaced by the repository axiom audit. The coordinate Einstein-tensor reduction is checked by `tools/completion_metric_check.py` (SymPy, 18 checks), outside the Lean kernel; the repository copy differs from the source only in writing its report to a temporary directory.

## RESULTS.txt (verbatim)

```
FULL COMPATIBILITY: RESULTS AND LIMITS
23 October 2026. Local files only. Read alongside VERIFICATION.json.

The main missing classical interface now has a concrete example. A single
inhomogeneous expanding metric supports positive baryons, unreleased donor,
retained stock, one source clock, one vacuum history, and the native eta and
epsilon. Its future comoving proper time is unbounded. The same eta defines
an actual infinite probability space with the exact native Gibbs marginals.
This is a common effective construction, not a derivation of the metric from
individual microscopic histories. That latter interface remains open.

158 explicit theorem declarations in the new Completion modules compile.
The kernel audit covers 228 Completion theorem constants and 457 imported
Entropic theorem constants, with no nonstandard axioms. The difference from
158 includes generated declarations. Some proofs adapt existing identities;
these counts do not mean 158 independent new physical predictions.
The allowed foundations are propext, Classical.choice and Quot.sound.
There are no sorry/admit/custom-axiom/native_decide admissions in the supplement.
The independent SymPy calculation passes all 18 tensor/coordinate checks.
The tensor calculation itself has NOT been formalized in Lean.

The locally available Lean/mathlib checker is 4.19. The active project declares
4.35. Integration and rechecking on that branch remain a separate build task.
Claude's active files, all four publications, PDFs and simulations are unchanged.
All 221 snapshotted input hashes still match their active originals. Publication
organization check: OK. No files were deleted, published or sent elsewhere.

WHAT HAS BEEN CLOSED

1. Exact native histories, with the actual nonuniform 1680-state measure.
InfiniteHistory uses Measure.infinitePi, not a symbol that merely assumes IID.
Every finite cylinder has the product probability. The integer-time shift is
invertible and preserves the stationary measure. A separate rooted measure
has blank past and exact native future marginals. The root is an initial-state
choice; it does not follow from a finite accessible register.

Entropy connects those marginals to the existing native gshare, proves
H(p^n)=n*gshare and the seven-channel determinant exp(-7*gshare). This supplies
a compatible infinite-history probability model for that part of the G* chain.
It does not provide a physical fresh-record supply or identify the determinant
with an electron energy gap. The two-sided stationary measure and the rooted
initial measure are alternatives, not simultaneously imposed symmetries.

2. One inhomogeneous, global-in-time effective spacetime.
In units c=8*pi*G=1, use e-fold coordinate s>=0 and define

  F=1-exp(-s), b_bg=epsilon exp(-3s),
  C_bg=exp(-3s-eta F),
  V(s)=integral_0^s eta C_bg(z) exp(-z) dz,
  H=sqrt((b_bg+C_bg+V)/3), Q=H V_s.

Lean proves positive H and densities, Friedmann, Raychaudhuri, the exact
component balances, and unbounded proper time integral ds/H. Gamma=H is a
chosen release law for this existence witness, not a derived assembly kernel.

For the spatial extension, put

  E=exp(-3s), I(s)=integral_0^s E(z)/H(z) dz,
  h(r)=delta/(1+r), j(r)=delta(1+r/3)/(1+r)^2,
  P_h=1+h I, P_j=1+j I,
  R=r exp(s) P_h^(2/3), J=P_h P_j/E,
  alpha=3H/2+h E/P_h, beta=3H/2+j E/P_j,
  rho=4 alpha beta/3 - V,
  b(r,s)=[epsilon/(1+epsilon)] rho(r,0)/J,
  C=rho-b, u=(1-F)C, retained=F C.

The metric is
  ds_metric^2=-H(s)^(-2) ds^2 + R_r^2 dr^2 + R^2 dOmega^2.
Its domain is r>0; no smooth central completion is claimed. It is not a bound
galaxy or a static dense core. For sufficiently small positive delta, Lean
proves C>0 for every s>=0 and every r>=0 used in the scalar formulas. It also
proves strictly different densities at r=1 and r=2 at EVERY epoch, positive
b,u,retained for every s>0, and the two independent pressure equations.

The decisive global estimate is
  J C > exp(-eta)/2.
The amplitude bound is explicit and has a proved positive solution. It keeps
the initial local baryon allocation below the surviving comoving donor mass.
R_r remains positive in the coordinate calculation, avoiding shell crossing
in this particular expanding family. This is not a theorem that arbitrary
initial data or collapsed multistream halos remain regular.

3. The background/local release distinction is respected.
The global example uses local q=H*u, which generally varies in space, and
uniform Q=H*eta*C_bg*exp(-s). Its local equations are precisely
  u_dot+theta*u=-q-u*Q/C,
  retained_dot+theta*retained=q-retained*Q/C.
At the homogeneous reference h=j=0, C=C_bg and Q=eta*q_bg. This realizes the
paper's prescribed background law. It does not identify a spatial ensemble
average with that reference without an additional averaging definition.
The earlier local example also works, but chooses a specially tuned rate
for which the stronger pointwise equality happens to hold. That equality
must not be promoted to the general theory.

4. Compatibility with the selected depletion action, on a proved interval.
Both spatial constructions have a positive initial interval satisfying BOTH
K>V and C>3(K-V) with a fixed positive K, so the selected action equals the
dust action there. The new global dust solution stays positive for all future
time, but its first proposed floor K=min(donorBound/6,V(1)/2) eventually fails
K>V. GlobalFloor.current_floor_fails_global_domain proves this failure.
Thus the compiled theorem does NOT certify the depletion action forever.

A better constant K=V_infinity appears to remove this particular obstruction
for this example. GLOBAL FLOOR CANDIDATE.txt gives the full analytic estimate
using the native eta<1/7 and a smaller positive delta. The remaining integral
bounds and identification of K-V with the positive tail are not in the Lean
certificate. This distinction matters; an inequality omitting K>V is inadequate.

5. Moving-body reciprocity and finite propagation with bounds.
Motion extends Claude's central-contact momentum/angular-momentum identities
to kick-then-drift trajectories and finite sequences. Positions actually move.
It does not prove a kinetic or relativistic continuum limit, energy conservation
for arbitrary contacts, or coupling to the inhomogeneous metric above.
CausalBounds supplies a discrete local update preserving 0<=capacity<=1 and
an n-step finite domain of dependence. This is an explicit candidate repair;
it is not a proof that the manuscript's unmodified telegrapher PDE preserves
bounds or that this lattice update has the required Lorentzian limit.

WHAT IS INCOMPATIBLE, AND THE REPAIR

A. Fixed finite total faithful archive + nontrivial exact IID alternatives at
all durations: impossible (the earlier FiniteArchive certificate is imported).
Repair: unbounded exported history, as the current paper already permits; or
finite-window/average-return claims, as Claude's FiniteRenewal permits. The
latter does not automatically inherit the indefinite entropy-rate G* argument.

B. Nonnegative stock density + the exact raw exponential RAR throughout a
uniform sufficiently dense core: impossible (earlier ExactDenseCore proof).
Repair: an admissible positive projection or a changed constitutive target.
The new positive_profile_error_floor quantifies the minimum unavoidable error:
if the raw cumulative target drops by D, a monotone cumulative mass cannot
approximate both endpoints more accurately than D/2. Compatibility therefore
does not guarantee the requested observational tolerance.

C. One nonzero exchange vector parallel to two different unit-time streams:
impossible. The common geodesic clock is valid in the single-stream family;
a multistream kinetic exchange law, forces, or additional clocks are needed
for general halo continuation. This is not a contradiction of the existing
single-stream equations.

D. Uniform eta and local rate plus pointwise Q=eta*Gamma*u in regions with
different u: impossible. Use the manuscript's background Q prescription.
It already avoids this extra, incorrectly strengthened local requirement.

E. G0=c*G* with c>1 AND G0=G* with no matching factor: impossible.
Keep G*, bare G0, and interacting GR distinct. A positive matching factor
can reconcile them algebraically; that does not derive the factor physically.
The current compact and CDT papers already make the distinction.

F. Continuing an integrated drain past the available positive donor budget:
impossible. The global clock example avoids overdraw. Its extension through
the selected nonlinear pressure branch is a separate issue from donor positivity.

THE G DERIVATION

Nothing here disproves the existing electron-anchored G* calculation.
The native count/eta/entropy and marked-generator arithmetic remain intact.
The existing EFT.Scale.Gstar_closed_form theorem establishes
  G*=(9/4)(hbar*c/me^2) Ze^2 log(1-exp(-7*gshare))^2.
The infinite-history and entropy constructions now show that the exact native
probabilistic premises can coexist, without replacing them by a finite register.

Physical G=G* still uses the stated Einstein/horizon/source normalization.
The full paper, Section 10 (around lines 928-962), says this explicitly; the
compact paper around lines 579-687 and CDT chapter 07 agree. The microscopic
selection of the charged gap, the common causal-length conversion, and the
interacting source response remain physical obligations.

Obstructions.two_distinct_matchings proves the logical gap precisely: with
G* and a positive bare factor fixed, two positive matching factors can give
G* and 2G*. The arithmetic alone cannot choose between them. Adding the
paper's physical matching premise chooses a branch, but is not a derivation
of that premise. This is not a claim that its matched branch is inconsistent.
The quoted numerical agreement is a postdiction in the paper's own accounting.
No new CODATA comparison or empirical inference was made here.

WHAT STILL CANNOT HONESTLY BE CALLED FINISHED

* One interacting microscopic model whose physical states, history measure,
  metric/clock map, matter propagation, stock, and continuum dynamics produce
  THIS effective solution. Sharing eta and placing a measure beside a metric
  does not supply the missing dynamics or prove the correspondence.
* A common interacting matter/gravity cone, the long-distance source response
  GR and its matching to G*, inhomogeneous physical constraints, and a common
  refinement/continuum limit. Finite inverse realizations and conditional
  inheritance theorems remain conditional at this interface.
* An independently selected galactic target, carrier/formation map, assembly
  release kernel and finite-work contact. A positive rate does not select its
  equilibrium target; the new relaxation countermodel makes that explicit.
* General multistream, shocks, pressure/depletion, strong-field saturation and
  bounded causal continuum dynamics on the same solution. The explicit regular
  family is not an existence theorem for all those regimes together.
* Joint empirical validation using frozen physical inputs and consistent model
  branches. The current fits and simulation outcomes are evidence, not axioms
  to be made true by selecting an example. No simulations or likelihoods reran.

These are missing specifications or substantial unproved physics, not problems
that can be closed by declaring additional axioms. I tested constructive routes
where the documents supplied equations; for selection gaps, the two-matching
and arbitrary-target constructions show why those equations underdetermine the
answer. Full-theory compatibility therefore remains open, but the earlier
absence of any common inhomogeneous clock/stock spacetime is no longer the
right description of the effective subsystem.

REVIEW AND REPRODUCTION

Main certificates:
  Entropic.Completion.global_effective_assumptions_compatible
  Entropic.Completion.GlobalModel.positive_fields
  Entropic.Completion.GlobalModel.inhomogeneous_every_epoch
  Entropic.Completion.GlobalModel.future_proper_time
  Entropic.Completion.GlobalModel.selected_depletion_initial_interval
  Entropic.Completion.spatial_history_assumptions_compatible

OBLIGATIONS.csv is the item-by-item resolution map with source locations.
UPSTREAM LEDGER.csv preserves all 1,437 claim rows; UPSTREAM UNFINISHED.csv
extracts the 386 partial/not-formalized/physical-premise rows. Their statuses
are unchanged: 90 partial, 143 not formalized, 153 physical premises. The new
coordinate example does not silently promote the generic GR/action claims.

VERIFICATION.json records exact current source hashes, passing build records,
the full axiom audit and symbolic tensor results. PORTABILITY.patch contains
only the cross-product notation adaptation for the copied StockSettling module.
The prior supplement's portability changes remain in that supplement's patch.
CLAUDE HANDOFF.txt gives integration instructions. No active upstream source
has been overwritten with an older compiler adaptation.
```

## OBLIGATIONS.csv (verbatim)

```
﻿id,obligation,status,evidence,document_location,remaining_or_repair
H1,Exact native infinite histories,CLOSED mathematically,InfiniteHistory; Entropy,Full H.4/P.9; compact 1162,Physical fresh-capacity supply and quantum implementation remain open.
H2,Record root,"COMPATIBLE choice, not forced by finite accessible capacity",InfiniteHistory.rootedLaw; integer_time_has_no_first,"Full P.9; compact 1162,2033",Current compact explicitly includes total history capacity/no external archive. Do not delete these qualifications.
H3,Finite reversible renewal replacement,CLOSED finite/average branch only,Claude FiniteRenewal; imported finiteArchive_isEmpty,Stock settling and finite renewal 2026-10-23/NOTE.txt,Finite-window exactness does not establish indefinite native Gibbs renewal or transfer G* to that branch.
G1,Native entropy and G* arithmetic,CLOSED conditional mathematics,Entropy.block_entropy; seven_channel_determinant; existing EFT/Scale/Electron,"Full section 10; compact 444,579-687",Selected charged gap and electron anchor remain explicit.
G2,Physical G=G*,OPEN physical selection,Obstructions.two_distinct_matchings,Full 928-962; compact 579-687,Measure/derive the low-energy source/horizon matching in the same interacting model.
G3,"G*, bare G0 and interacting GR",NO contradiction when kept distinct,Obstructions.bare_matched_normalizations_conflict; renormalization_can_match,CDT chapters/07_comparison.tex,No unrenormalized simultaneous equality for the 1.03002 bare branch.
S1,Common inhomogeneous effective spacetime,"CLOSED example, scalar Lean plus independent tensor check",GlobalSpatial; GlobalRelease; GlobalModel,Full O.3 13444-13585,"Radial punctured domain, chosen expanding family; no central/bound-halo or microscopic realization."
S2,Positive donor for full future,CLOSED for chosen clock law,GlobalSpatial.comoving_donor_positive; GlobalModel.future_proper_time,Full O.3,"Gamma=H is chosen for existence, not empirically derived."
S3,Background/local exchange,CLOSED within chosen reference prescription,GlobalRelease.local_balances; reference_matches_background,Full 13535-13578,No unjustified replacement of Q by eta*q(x); a spatial averaging construction remains separate.
S4,Selected depletion action,CLOSED initial interval; global candidate outside certificate,GlobalFloor.selected_action_local_domain; current_floor_fails_global_domain,Full 13738-13796,First global floor fails K>V. See GLOBAL FLOOR CANDIDATE.txt for replacement and unformalized integral bounds.
S5,Raw RAR plus positive dense-core stock,INCOMPATIBLE exact combination,Earlier ExactDenseCore; Obstructions.positive_profile_error_floor,Earlier ASSUMPTIONS.txt; full galactic target discussion,Use admissible projection; its nonzero necessary error must meet data tolerance.
S6,Projected bound galaxy in cosmological metric,OPEN,Earlier positive finite projection; global expanding example,Full O.3 and galactic carrier sections,Construct a bound galaxy/positive transport solution with boundary and assembly data.
S7,Actual moving-body reciprocity,CLOSED finite kick/drift model,Motion.evolution_conserves,Claude StockSettling; full carrier contact discussion,No coupled relativistic kinetic limit or full energy law established.
S8,Single clock in multistream flow,INCOMPATIBLE if nonzero exchange forced parallel to distinct streams,Obstructions.two_stream_clock_obstruction,Full O.3 single geodesic source clock,Supply a covariant kinetic exchange law or additional fields with stress/momentum balance.
S9,Causal propagation plus capacity bounds,CLOSED discrete candidate; continuum OPEN,CausalBounds.invariant_all_times; finite_domain_of_dependence,Full 5883-5903,Invariant-domain nonlinear continuum law and physical selection remain needed.
S10,Target selection from settling rate,UNDERDETERMINED,Obstructions.relaxation_rate_does_not_select_target,Claude StockSettling and NOTE.txt,Derive work/supply/target relation from independent microdynamics; rate alone cannot choose it.
M1,Microscopic history-to-metric correspondence,OPEN central interface,GlobalModel comment explicitly excludes it,"CDT chapters/04_cdt_einstein,05_clock_matter,06_refinement,07_comparison","One interacting construction must satisfy geometry, source, clock, history and stock simultaneously."
M2,Interacting Einstein phase and source response,OPEN conditional inheritance,Current CDT finite tests retained,CDT abstract; chapters/07_comparison final GR discussion,Show phase/start independence and universal long-distance source response; finite inverse construction is insufficient.
M3,Common matter and gravity cone,OPEN,Existing microscopic finite clock tests,CDT abstract and chapters/05_clock_matter,Derive common interacting characteristic cone; choosing equal speeds is only algebraic compatibility.
M4,Physical constraints and refinement,OPEN beyond specified finite/homogeneous models,Current upstream ledger G10; CDT refinement chapter,Compact 2053; CDT chapters/06_refinement,"Inhomogeneous constraint space, rigging and compatible refinement/continuum maps."
M5,Fresh history capacity and energy,OPEN resource realization,"InfiniteHistory is mathematical, not an energy source",Full P.9 15640-15722,Provide recoverable capacity with physical entropy/energy/gravity accounting.
M6,Gauge/species/native interacting matter,OPEN beyond established finite identities,"Upstream ledger G1,G2,G7,G10",Full H/I/Q; CDT comparison table,Existing conditional kinematics is not a complete interacting/chiral matter theory.
C1,Horizon loading and carrier map,OPEN physical identification,Existing conditional ensemble/action statements,Empirical 06_interpretation_and_audit.tex table,"Select phase loading, mode-energy map, carriers and horizon contact independently."
C2,Formation abundance and release history,OPEN independent selection,Chosen global Gamma is not fitted assembly law,"Empirical 06_interpretation_and_audit.tex; full 14211,14457-14498","Derive pre-acoustic formation vertex, retention gate, labels and mixing from fixed physics."
E1,Joint empirical viability,OPEN empirical work,Saved fits and simulation evidence unchanged,Empirical publication and full O.12,Freeze inputs and model branch; evaluate remaining dwarfs/clusters/Galactic mass/high-z/release constraints.
F1,All generic formalization obligations,OPEN as recorded upstream,UPSTREAM UNFINISHED.csv,ledger/OPEN_TRIAGE.md and LEDGER.md,"143 not formalized,90 partial,153 physical-premise rows preserved; no automatic regrading."
F2,Native 4.35 integration,OPEN build integration,Isolated 4.19 audit passed,VERIFICATION.json; CLAUDE HANDOFF.txt,"Port only Completion modules, reuse native StockSettling, recheck against active 4.35 dependencies."
```

## GLOBAL FLOOR CANDIDATE.txt (verbatim)

```
GLOBAL DEPLETION FLOOR: ANALYTIC CONTINUATION, NOT YET IN THE LEAN CERTIFICATE

This repairs the failed global K=min(donorBound/6,V(1)/2) proposal for the
specific GlobalSpatial family. It does not prove evolution for arbitrary data
or through pressure-branch shocks. The argument below uses ordinary calculus;
its two integral estimates still need formalization in Lean.

Let x=exp(-s), so 0<x<=1. Then
  F=1-x, C_bg=x^3 exp[-eta(1-x)],
  V_s=eta x^4 exp[-eta(1-x)].
Choose the constant
  K=eta integral_0^1 z^3 exp[-eta(1-z)] dz.
Changing variable z=exp(-s) in V gives exactly
  K-V(s)=eta integral_0^x z^3 exp[-eta(1-z)] dz.
This is strictly positive at every finite future s. Since eta>0, the integrand's
exponential factor is at most exp[-eta(1-x)] on 0<=z<=x. Consequently
  0<K-V(s)<=eta*x*C_bg(s)/4<=eta*x^4/4.
For the homogeneous model, eta<4/3 immediately gives 3(K-V)<C_bg for all s.

For the inhomogeneous model use the stronger native bound 0<eta<1/7.
It follows from the already certified native eta bracket (eta is about 0.02987).
Because exp(-eta)>=1-eta>3/4 and V>=0,
  H^2=(epsilon*x^3+C_bg+V)/3 > x^3/4,
  H>x^(3/2)/2.
Hence
  I(s)=integral_0^s exp(-3z)/H(z) dz
      <2 integral_0^s exp(-3z/2) dz <4/3.

Choose the positive amplitude delta to satisfy BOTH the existing Lean-proved
small-amplitude condition and delta<=3/4. Such a choice exists: decreasing a
positive admissible amplitude preserves its upper bounds. Then
  1<=P_h,P_j<=2, J=P_h*P_j/x^3<=4/x^3.
The existing Lean theorem supplies J*C_local>exp(-eta)/2, so
  C_local>exp(-eta)*x^3/8.
Finally eta<1/7 implies 6*eta<1-eta<=exp(-eta). Combining the bounds gives
  3(K-V)<=3*eta*x^4/4<=3*eta*x^3/4
         <exp(-eta)*x^3/8<C_local.
Thus BOTH K>V and C_local>3(K-V) hold for every finite s>=0 and every r>0.
The particular global dust solution then stays on the selected action's dust
branch; it need not enter its pressure branch. K-V tends to zero only at
infinite time. The proper-time lower bound already proves that s->infinity
requires unbounded comoving proper time.

What must still enter Lean before upgrading the global depletion claim:
1. The finite-integral change-of-variable identity for K-V and its positive
   tail upper bound.
2. The integrated H lower bound giving I(s)<4/3.
3. Package the smaller amplitude and these bounds in GlobalModel.

No axiom asserting these steps has been added. The published verification
manifest certifies only the initial depletion interval. This analytic route
is included so the unproved formal step has a concrete target rather than
an unspecified existence claim. It does not resolve the native microscopic
selection, general multistream evolution, or galaxy-target obligations.
```
