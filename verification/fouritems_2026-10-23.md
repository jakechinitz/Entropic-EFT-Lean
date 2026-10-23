# Four open items (2026-10-23)

Source: Sol and Fable / 02 Research / Four open items 2026-10-23 (built there with Lean 4.19). Integrated on Lean 4.35; porting changes: spaces around `≤` and one `ring` after `field_simp` in `Streams.exact_budget`. GPT's standalone `Audit.lean` is replaced by the repository axiom audit. `tools/fouritems_bianchi_tensor.py` differs from the source `bianchi_tensor.py` only in writing its report to a temporary directory.

## RESULTS.txt (verbatim)

```
FOUR OPEN ITEMS — LOCAL LEAN AND APPENDIX FOLLOW-THROUGH
23 October 2026

RESULT AND SCOPE

This continuation makes two constructive advances: an explicit multistream
vacuum-exchange rule with positive finite updates and a coupled expanding
Einstein example; and an energy-conserving reset using a finite compensating
register and zero-energy exported history. These are selected extensions with
stated assumptions. Neither establishes the complete microscopic theory.

I also attempted an independent retention-gate extraction from the saved
hydrodynamic catalogs. It did not select the needed gate. The finite native
geometry and source-response records likewise do not establish the required
interacting physical gravitational state. The precise surviving gaps are below.

No current paper, PDF, active Lean source, or original simulation was changed.
The new calculations and proofs are isolated here for review and integration.

LOCAL LEAN CHECK

The active project is:
  02 Research/Unified closure 2026-10-21/formalization
Its selected toolchain is 4.35. The saved compatibility verification reports
3160 Entropic theorem constants and 727 EFT theorem constants, with no
nonstandard axioms. Those are saved upstream results, not a freshly rerun
4.35 build in this continuation. The local Completion directory contains
InfiniteHistory.lean; the larger GlobalModel remains in the separate Full
compatibility closure supplement.

I inspected that GlobalModel's actual fields and theorem statements. Its
native parameter, positive inhomogeneous expanding fields and rooted-history
measure are specified; it explicitly does not supply a history-to-metric map
or bound galaxy, and its selected depletion action is certified on an initial
interval. Thus the existing Nonempty result has a meaningful, narrower scope
than a full four-item closure. A theorem count cannot enlarge its statement.

The new Entropic.FourItems modules are checked separately with the available
Lean/mathlib 4.19 runtime. See VERIFICATION.json for final hashes and counts.
The tensor reduction, ODE calculations and matrix controls are separately
identified; they are not presented as Lean proofs of a full continuum.

1. GALAXIES, MULTISTREAM STOCK AND COSMOLOGICAL EXCHANGE

What was already present:
O.3 gives a prescribed clock potential, positive internal allocation, a
mass-preserving positive galactic target, a spherical kinetic equilibrium,
Vlasov transport and selected depletion/contact laws. N.8 gives the director
energy and its stock-density variation. These are credited, not rediscovered.

New selected covariant exchange rule:
Use signature (-,+,+,+). Let n be the unit future-directed clock vector,
grad(V)=-Q n, Q>=0. For stream a let u_a.u_a=-1 and
T_a^{mu nu}=rho_a u_a^mu u_a^nu. Choose nonnegative weights w_a summing to one.
Set

  J_a^nu := div T_a = -Q w_a n^nu,
  gamma_a := -u_a.n,
  div(rho_a u_a) = -Q w_a gamma_a,
  rho_a (u_a.grad)u_a = Q w_a (gamma_a u_a-n).

The force is orthogonal to u_a, and the rest-energy loss plus force reconstructs
J_a exactly. Summing J_a cancels the vacuum source +Q n. Distinct streams need
not be parallel to the clock. Nonzero exchange does require the displayed
force. Requiring those streams to remain geodesic would discard this solution.
In a clock inertial frame the source removes energy without net spatial
momentum. At fixed momentum this increases speed as rest mass decreases; it
does not create energy. When Q=0 it reduces to collisionless transport.

A useful constitutive choice for finite source updates is the available
timelike energy reserve. Define, relative to n,

  e_a=T_a(n,n), j_a=-h_n T_a n, A_a=e_a-|j_a|>0,
  w_a=A_a/sum_b A_b.

For dust A_a=rho_a/(1+|v_a|). This is covariant once the existing clock n is
specified. On the cold common-flow branch it reduces to w_a=rho_a/sum rho,
so it retains the paper's composition-preserving drain. It is an additional
choice for the multistream extension, not uniquely selected by conservation.

Exact positive finite update:
For a source substep in a local clock frame write P_a=(E_a,p_a), E_a>|p_a|,
A=sum_a(E_a-|p_a|), and select vacuum increment 0<=DeltaV<A. Then

  s=1-DeltaV/A,
  E'_a=|p_a|+s(E_a-|p_a|),   p'_a=p_a,   V'=V+DeltaV.

Every updated stream is future timelike, total spatial momentum is unchanged,
and sum E'+V'=sum E+V exactly. The infinitesimal limit is the source rule
above. A cold stream gives E'=sE, recovering O.3. Internal unresolved/retained
labels can be updated with the actual mass survival factor sigma=m'/m:

  U'=sigma(1-p_release)U,
  R'=sigma(R+p_release U).

These preserve positive labels and their mass sum. For a moving stream sigma
is generally NOT the reserve survival s; in the cold limit they coincide.
This distinction is necessary for relativistic bookkeeping.

The two-stream Lean witness uses E_1=E_2=2, p_1=1, p_2=-1, s=1/2. Both final
energies are 3/2, with nonzero masses, distinct velocities and vacuum gain 1.
The general finite budget and source decomposition are also proved. The
three-dimensional numerical controls test 300 collections of 17 momenta;
maximum energy residual was 2.14e-14, and all timelike margins stayed positive.

Actual coupled spacetime witness:
Use an axisymmetric Bianchi-I metric

  ds^2=-dt^2+a_x(t)^2 dx^2+a_y(t)^2(dy^2+dz^2).

Two equal counterstreams have opposite x momenta, total number density N,
particle energy E, momentum magnitude p, stock energy C=NE, and longitudinal
pressure P=N p^2/E. Baryons have dust density b. In units 8*pi*G_matched=c=1,

  theta=H_x+2H_y,
  H_x'=(b+C+2V+P)/2-theta H_x,
  H_y'=(b+C+2V-P)/2-theta H_y,
  b'=-theta b,  N'=-theta N,
  p'=-H_x p,  E'=-H_x p^2/E-Q/N,  V'=Q.

The constraint K=2H_x H_y+H_y^2-b-C-V satisfies K'=-2 theta K.
This identity and total energy balance are Lean-proved. Independent symbolic
calculation of Christoffels, Ricci and Einstein tensors verifies the metric
reduction, including all off-diagonal components (18 checks).

Q(t) is computed from an independent homogeneous reference using the native
eta=0.029866844393522... and epsilon=0.187945730194412..., with Gamma_clock=H_ref.
It is then prescribed to the beam universe; it is not redefined using the
beam universe's local densities. F'=Gamma_clock(1-F) supplies the same positive
internal label fraction. Its release rate per stream proper time is
Gamma_a=gamma_a Gamma_clock. This recovers O.3 in the common-flow limit.

For initial momenta 0, 0.2 and 0.7, integrations through t=20 retained positive
mass squared, stock and baryons. Maximum relative Einstein-constraint error
was below 8.92e-12. Tightening tolerance changed all sampled state variables by
at most 4.45e-10. The zero-momentum solution agrees with the reference FLRW
solution to 1.34e-12. The moving examples have genuine anisotropic expansion.

There is also an analytic local existence statement: these ODE right-hand
sides are smooth for N>0 and E>|p|; the initial data lie strictly inside that
open domain and satisfy K=0. Ordinary local ODE existence and constraint
propagation yield a positive-duration exact solution. This standard analytic
argument is distinct from the numerical extension to t=20 and is not a Lean
formalization of the ODE existence theorem.

What this closes: the claimed kinematic obstruction between distinct streams,
one vacuum clock and energy-momentum conservation, within an explicitly
selected positive-domain extension; and a concrete expanding beam example.

What it does NOT close: a forming bound galaxy with the projected RAR target,
all N.8 director/support forces, and cosmological exchange in one solution.
The Bianchi example is homogeneous and has no bound halo. It does not include
the depleted pressure branch. Arbitrary inhomogeneous cells may exhaust their
reserve; imposing a local shutoff while keeping a spatially uniform V requires
additional exchange dynamics, as O.3 already says. A general shock/caustic
theorem is a stronger robustness task, not necessary merely to exhibit one
allowed compatible solution.

2. THE NATIVE MICROSCOPIC INTERACTING REALIZATION

What was already present:
H.9a gives the common Einstein-Dirac EFT. H.10 supplies conditional physical
inner products and renewal preservation. H.15 supplies a finite coupled
geometry/matter operator and exact inverse-metric refinements. C.5 supplies
the matched G derivation. None of these is removed from the completed work.

Attempt A: use exact source-dependent operator lifting to close the response.
I tested an interacting four-dimensional coarse Hamiltonian, an exact
six-dimensional lift, and a source family. H_f J=J H_c holds exactly, and
the retained-state source response is preserved. But the unconditioned fine
thermal state includes the additional sector. In this illustrative control,
the dimensionless log-partition second derivative is 0.638763 for the coarse
and retained systems, versus 0.534228 for the full trace. Step halving leaves
that difference intact. This is not native-geometry evidence or a contradiction
in H.15: H.15 already specifies the retained sector and warns about state and
discarded-sector factors. It demonstrates why a physical-state prescription
cannot be supplied by intertwining alone.

Attempt B: use the saved native source response as the missing gravitational
measurement. The existing newton_history_response_protocol.json correctly
requires calibrated metric sources, a massless momentum window, matching
tensor/matter responses and the actual signed measure. The saved local
source_response_bounds_results.json explicitly tests an unreduced trial ground
state and finds a large finite-box gap. It is not the missing physical ensemble.
Reusing it as a Newtonian result would contradict its own scope. No physical
G_R estimate is manufactured from those data.

G clarification:
C.5 already establishes G/G_*=S0/S_infinity; its selected S_infinity=S0 gives
G=G_*. The new algebraic certificate only shows that omitting that physical
selection leaves beta=S_infinity/S0 free. It does not refute the matched branch.
Uniqueness of the matching is not required for a compatibility witness.

Surviving task: realize the specified matter/source response in the chosen
native interacting physical state and geometric dynamics, including the
constraints and common propagation properties identified in Q.13. This is
substantial physics. An explicit host/state selection is permitted for an
existence claim; deriving or validating that selection is the stronger open
claim. The supplied finite calculations cannot establish it by algebra alone.

3. INDEPENDENT COSMOLOGICAL NORMALIZATION

Attempt A: reproduce the existing kernel calculation without rerunning a
simulation or changing original caches. All 15 gate/partition/label cases
were recomputed from the saved host kernels and first-entry histories.

  17 km/s, original labels:  I_rel=75.40--75.88
  14 km/s, original labels:  I_rel=93.12--96.73
  12 km/s, original labels:  I_rel=108.01--109.94
  17 km/s, grouped labels:   I_rel=56.48--65.24
  17 km/s, earlier labels:   I_rel=81.67--82.87

The legacy linear-depletion comparison target is 94.2. It is NOT automatically
the comparison target for the current direct positive-allocation likelihood.
For the same frozen reference histories, replacing dF by exp(-eta F)dF changes
these integrals by only about 0.19--0.21%. That calculation neither updates the
likelihood nor removes the gate/label selection problem.

For K(tau)=K0+(1-K0)K_tail(tau), the linear integral is exactly

  I=I_tail+K0(I_immediate-I_tail).

The affine identity, inverse target-matching formula and admissible interval
are Lean-proved. This makes the degeneracy explicit: matching a normalization
can select K0 when the target lies between the two endpoints; it cannot count
as an independent prediction of K0.

The saved raw coarse information-loss estimates sometimes decrease (largest
single drop about 0.091). This may be sampling noise or information return;
it is not proof that a latent irreversible release law is impossible. The
monotone exponential fit imposes the desired shape. The coarse observable's
physical monotonicity remains to be established, exactly as O.14 states.

Attempt B: extract a gate directly from saved hydro catalogs, without using
dark-energy normalization. RETENTION TEST PROTOCOL.txt fixes the method before
its result: half-retention of the cosmic baryon fraction, quarter/three-quarter
sensitivity, minimum 256 DM particles and eight groups per velocity bin, then
a stricter 1024-particle control. No selection on gas count is used.

Across 31 pre-reference-reionization snapshots, 17 had populated qualifying
bins. Every such bin's median retained fraction exceeded 3/4. Thus no 1/4,
1/2 or 3/4 upward retention crossing was measured. The remaining 14 snapshots
lacked sufficient populated bins. At the 1024-particle cut none of the 31
epochs supported the required bin statistics.

A separately declared star-forming-fraction crossing occurred in eight epochs,
at 9.295--9.804 km/s. It is not a baryon-retention threshold and has not been
substituted for one. Repeated snapshots are not independent halo samples.
The catalog component-mass mismatch is below 1.8e-5 relative and is recorded.
FOF association is not a binding-energy test. The Release zoom/run folder has FOF
catalogs but no particle snapshots from which to reconstruct gas escape or
the original labels.

Result: the available catalogs do not independently select 14 or 17 km/s under
this operational retention criterion. This is a failed candidate route, not a
falsification of the theory. It identifies why the saved data cannot close the
normalization. A physical source-record observable, a resolved mass/redshift
kernel and a fixed-history direct likelihood test remain necessary. The
existing good conditional fit remains a good conditional fit.

4. PHYSICAL HISTORY CAPACITY

What was already present:
P.9 permits an unbounded non-geometric archive and excludes fixed total finite
de Sitter Hilbert space. InfiniteHistory supplies exact native product laws.
H.10 proves that the selected renewal can preserve persistent coupled dynamics.
Those mathematical compatibility results are retained.

Attempt A: an energy-conserving swap tape.
Swapping a present register with a pre-supplied fresh register is reversible
and conserves their shared additive Hamiltonian. The swap identities are
Lean-proved for arbitrary alphabets; every one of the 243 basis words of a
three-symbol, four-step control was recovered by reverse evolution. This
constructs a mechanism using a supply; it does not generate that supply.
Ordinary exported registers also carry their energy, so this alone does not
implement the paper's zero-leading-stress history assumption.

Attempt B: finite compensating register with zero-energy output.
Let the native register have eigenstates r, energies E_r, probabilities p_r.
Choose T=max E_r and an auxiliary register with states B_r and nonnegative
energies T-E_r. Work on the code |r,B_r>, whose total energy is T. Define

  W |r,B_r> = sum_s sqrt(p_s) |s,B_s> tensor |r,s>_history.

Give each fresh history factor zero Hamiltonian. Then:
  * W is an isometry: the record indices make distinct input columns orthogonal
    and sum_s p_s=1 fixes each column norm.
  * Tr_history W rho W^dagger is the fixed mixture
      sum_s p_s |s,B_s><s,B_s| Tr rho.
    The register marginal is exactly the native Gibbs law.
  * Every term has total energy T. The compensating register exchanges
    E_old-E_new and stays within a finite energy band at every reset.
  * An independent persistent geometry/matter unitary can be tensored with W,
    preserving that persistent dynamics and avoiding new path-dependent export
    when the reset coefficients are independent of its state/source.

For the native dimensionless energies K^2 in [122/3,170/3], the compensating
register lies in [0,16]. The algebraic energy/bound certificates and general
finite-alphabet Gram identity are Lean-proved. A coherent three-level control
verifies reset, isometry and energy intertwining at machine precision.

This construction uses a fresh d^2-dimensional factor per step; the successive
records are constrained by adjacency, so with a fixed initial input the
actually populated N-step alternatives number d^N. It makes no claim of
minimal allocated memory. Its finite-step isometry can be completed to a
unitary on a larger energy-degenerate space with a blank ancillary state.
The unlimited sequence still presupposes those spaces and preparation; no
autonomous physical clock/creation mechanism is derived here.

Result: unlimited recoverable records need not force an unlimited growth of
the energy in the present register. This explicit selected dilation addresses
energy bookkeeping without hiding an infinite-energy battery. It still has
unbounded logical capacity, an auxiliary coupling, and exactly zero-energy
record degrees of freedom as assumptions. To interpret that archive as having
no metric stress also requires the metric/source-independent coupling specified
by P.9; zero Hamiltonian in one chosen frame alone would not prove it.

The physical origin of that unbounded non-geometric factor is therefore still
open. No finite device or finite total Hilbert space has been claimed to create
indefinitely many exactly recoverable alternatives.

WHAT REMAINS AFTER THESE ATTEMPTS

1. A joint galaxy/stock/director/cosmological-exchange realization. The distinct
   stream source allocation is now supplied on a positive domain, with a
   coupled expanding example; bound-galaxy formation and full force matching
   remain beyond it.
2. The native interacting physical gravitational state and its matter/source
   response. Supplied effective and finite realizations already exist; their
   full physical matching is not established by the current data.
3. An independently selected physical release observable/gate/kernel, followed
   by the direct fixed-history observational test. The saved catalogs do not
   resolve that selection.
4. A physical origin for the unbounded stress-free archive. A finite-energy
   reset realization is supplied conditional on that archive, not a mechanism
   for producing the archive from a finite total resource.

These are not four demonstrated contradictions in the current paper. They
also are not all solved by the new constructions. Compatibility of an allowed
selected branch is a narrower claim than microscopic selection or empirical
success. The completed narrower results should be credited without promoting
them into those stronger claims.

REPRODUCTION

From the workspace root:
  python -X utf8 "02 Research/Four open items 2026-10-23/verify.py" Entropic.FourItems.Streams Entropic.FourItems.Selection Entropic.FourItems.Audit
  python -X utf8 "02 Research/Four open items 2026-10-23/calculate.py"
  python -X utf8 "02 Research/Four open items 2026-10-23/bianchi_tensor.py"
  .venv-well/Scripts/python.exe -X utf8 "02 Research/Four open items 2026-10-23/retention_catalogs.py"

All attempts, including failed proof drafts and the overly tight initial
catalog mass-rounding check, are preserved in the run directories. The final
manifest distinguishes final successful records from those earlier attempts.
```

## STATUS.csv (verbatim)

```
item,topic,achieved,still_open,source_anchors
1,Stream exchange,Selected positive-domain construction and coupled beam witness,"Bound galaxy, projected target and all director/support forces in the same evolving spacetime","O.3 13520-13585, 13630-13661; N.8 12315-12327; RESULTS.txt item 1"
2,Native interacting gravity,Existing EFT/finite results credited; source-state closure attempt remains conditional,"Native interacting physical state, constraints and calibrated matter/gravity response",H.10 8539-8575; H.15 9870-10067; C.5 4906-4919; Q.13 17095-17100
3,Predictive cosmology,Saved kernels reproduced; target-independent catalog gate extraction attempted without a retention crossing,Independent physical record/gate/kernel and a direct fixed-history likelihood,O.14 14592-14606; RETENTION TEST PROTOCOL.txt; retention_catalogs.py
4,History resource,"Finite-energy reset with zero-energy history constructed, conditional on fresh archive factors",Physical supply and metric-independent realization of unlimited non-geometric history capacity,P.9 15628-15681; H.10 8539-8560; RESULTS.txt item 4
```
