# Changelog

Dated notes for the Lean library, newest first. They were the opening sections of the README until 2026-11-08.

## Appendix T: the matter excess and the formation charge (2026-11-20, second entry; paper text only)

Full paper synced (440 pages). New Appendix T states what produces the conserved baryonic charge on which the formation
map of O.15 acts. T.1: the specified transfer has no reaction that changes baryon or lepton number, and its closure
weights, gluing characters and renewal channel carry no CP-odd bias. T.2: a conditional completion with an added
pseudoscalar and scalar triplet gives the lepton-number-violating coefficient
`κ_W(F) = κ_ν R(F)[1 + iς a_CP (1 − F)]`, whose interference invariant is proportional to `ς a_CP (F₁ − F₂)`. T.3: two
coupling sets reach `η_B = 6.1e-10` at fitted `a_CP = 2.17` and `3.27`; the yield is zero at `a_CP = 0`, reverses with
`ς`, and runs from `1.60` to `−2.26` of the reference as the starting temperature goes from `1.0` to `2.0 T_c`, so the
excess is a fit in the coupling and the thermal history. T.4: the handedness operator `q = J₁·(J₂×J₃)` of the spin-3
cell gives the exact response `−(C_j/3)⟨q⟩ d(1−r)³/dt` with `C_3 = 45/16807`; its sign depends on the record kernel.
T.5: the ratio of committed stock to baryonic mass holds for any value of the excess. O.15, Section 20 and the status
table point to the appendix; six references added. The ledger does not yet extract Appendix T. No Lean source changed.

## Cell specification, third epoch of the bath temperature, exact lag bounds (2026-11-20; paper and ledger text only)

Full paper synced (436 pages). N.8 states the specification of the response cell: the sign of the dipole is a thermal
variable, so the finite-frame numbers are those of a signed axis on the whole sphere; the grip required by the Planck
ratio is `3.1`, `3.6`, `4.3` under three counts of the density of a finite frame (600, 680, 810 registers) and `6.1`,
`7.9`, `8.5` for a dipole held at the down-field end; the ladder condition is a condition on participation,
`N_p = 1/ΣP_i²` in the place of `N`; the terms of the register action between registers do not supply the coordinate.
Appendix L, Appendix O.3 and the status row of the RAR law point to it. Section 15 adds a third epoch,
`f = 1.007 (+0.027, −0.023)` at `z = 0.97` from the MOND-based fit of the MUSE sample (`1.08` and `1.10` from the
dark-halo decompositions of the same galaxies), and states the lag exactly: `τ < 4.1 Gyr` at `z = 0` (the earlier
`6.7 Gyr` was first order in the lag) and `τ < 0.66 Gyr` at `z = 0.97`, both for a static baryonic field. Section 27.3
cites the bounds. The source also carries two wording changes in the colour sector made in the author's workspace on
19 November. Ledger C05-90 notes the numbers. No Lean source changed.

## Bath temperature and the tightened rigidity requirement (2026-11-19, fifth entry; paper and ledger text only)

Full paper synced. Section 15 states the horizon-bath temperature as a measured quantity, `k_BT = f ħH/2π` with
`f = 0.997 ± 0.012` at formation (abundance) and `f = 0.99 (+0.07, −0.08)` today (44 SPARC galaxies with ladder
distances), the exclusion of the surface-gravity temperature of the apparent horizon, and the lag bound `τ < 6.7 Gyr`;
Section 27.3 cites the bound. N.8 states the abundance-tightened rigidity requirement (`κ = Nεx² ≥ 3.1` at formation)
and the tested frames (UV-size frames, horizon registers resident in a cell). Ledger C05-90 notes the numbers. No Lean
source changed.

## Response ladders and bulk equipartition (2026-11-19, fourth entry)

`Entropic/Extensions20261119/Ladders` (2 theorems): `T_U/T_H = εx²` (`unruh_ratio`), so the harmonic requirement on
a locked group reads as its summed Unruh grip exceeding about `2.5 k_BT_H`; bulk-equipartition counts, `E/(½k_BT)`, of
the mutual field at `T_H` and of the baryonic field at `T_U` give `n(1+n)εx²` ladders per displaced nat, the O.3
density (`ladders_per_nat`). Ledger: new row C05-90. The full paper is synced to the version in which N.8 states the
measured rigidity requirement and identifies the equipartition premise with bulk equipartition (Padmanabhan 2012),
and Section 20 restricts single occupancy to each source's own commitment (38 SPARC points exceed 1 + 1/ε). J.14 now
reports the vertex-order alternation at the registered 32k and 64k volumes and that the published bifurcation line runs
nearly parallel to the α = 7 count line.

## Equipartition over the tilt polarizations (2026-11-19, third entry)

`Entropic/Extensions20261119/Equipartition` (5 theorems). For `m` tilt polarizations, `q` field units per quantum and
O.3 matching coefficient `λ`, the mean mutual field energy per cell is `Θ(1+qmn)/(2qλ(1+n))` (`cell_energy`); it is
`mΘ/2` for every occupation if and only if `λ = 1` and `qm = 1` (`equipartition_iff`), and the mean response is then
`1 + n` (`mean_response`), the exponential law, from the two tilt polarizations of N.8 with half a field unit each.
A mass with `2πMcR/ħ` displaced nats has `ħ/(2πcR)` per nat, the N.8 horizon nat (`displaced_nat_mass`), and
`n_nat k_BT_U = g²/(4πG)` (`holographic_equipartition`). Ledger: new rows C05-88 and C05-89; C05-87 note updated. The
full paper is synced to the version in which N.8 derives the half unit from the O.3 half-Θ rule read per
polarization, with the abundance and SPARC measurements, and Section 20 reads single occupancy through the horizon
nats of N.8 and the per-defect exclusivity of Section 3.2. A consistency sweep then updated the O.3 field-unit sentence,
the premise of the Section 15 RAR derivation and the per-ladder counting of Section 20, and the premise sentences of
the compact paper (with one sentence on the cap) and of the empirical-results paper (sections 1 and 2). Built with `lake env lean` against the Mathlib cache. The equipartition identification, single occupancy and
the numerical measurements `λqm = 0.997 ± 0.012` and `qm = 0.991 ± 0.029` are inputs or data.

## Response-cell density and the single thermal ladder (2026-11-19, second entry)

`Entropic/Extensions20261119/CellDensity` and `Polarizations` (12 theorems) formalize the statements added to O.3 and
N.8 of the full paper on 19 November 2026. `CellDensity`: the O.3 equipartition density gives half a `k_BT_H` per cell
equal to the mutual field energy (`half_theta_mutual`); with the lever and the register grip, the grip of one cell is
`(4π/g) ħc/L_* / C_E(x)`, so in the deep regime every cell grips the baryonic field with `1.694 ħc/L_*` (`cell_grip`);
the density over the bulk density of horizon nats is `(2/3)ε²x⁴n(1+n)` (`horizon_fraction`), and `x⁴n(1+n) ≤ 24`
(`x4_einstein_le`) keeps it below one for `ε ≤ 1/5` (`horizon_bound`, `eps_le`); the two-polarization thermal tilt
spread is `(1 + 2n)/(εx)` (`tilt_spread`). `Polarizations`: the three rigid-frame responses `1/(1 − e^{−x})`,
`coth(x/2)` and `coth x` (`one_ladder`, `two_ladders`, `two_ladders_coth`, `zero_m`) and the factor four in the deep
scale (`deep_scale`). Ledger: new rows C05-86 and C05-87. Built with the pinned Lean 4.35.0 against the Mathlib cache;
the 12 names depend only on `propext`, `Classical.choice` and `Quot.sound`. The equipartition matching of O.3, the
single ladder per cell and the SPARC comparison are inputs.

## Angular rule, host couplings and cavity ensemble (2026-11-19)

`Entropic/Extensions20261119/` (three modules, 17 theorems) formalizes statements added to the full paper on 18 and
19 November 2026. `AngularRule`: a positive, continuous, multiplicative wedge factor with `2k(2π) = 1` is
`e^{−θ ln 2/(2π)}` (`flat_subdivision_fixes_rule`, through the Cauchy step of `BlackHole.lapse_is_power`); any other
amplitude leaves a flat hinge with log-weight `ln 2 − 2πb'` (`wrong_amplitude_weight`); the hinge weight is exactly
linear in the deficit (`hinge_linear`); the amplitude is `AppQ.bH` (`bFlat_eq_bH`). `HostCount`: with the counting
identities of causal triangulations, the hinge traces give `κ₀ + 6Δ = 2r ln 2` whatever the per-simplex factors
(`logW_counts`, `einstein_coefficient`, `six_ln_two`), the angular amplitude sets `Δ` (`delta_from_amplitude`), and a
centring term moves the couplings along `κ₀ + 6Δ = const` (`centring_shift`). `Cavity`: the reduced weight
`τ(1 − √(1−x)) − x²` has its coexistence point at `τ = 32/27`, `x = 8/9` (`F_critical_nonneg`, `F_critical_zero`,
`gas_wins`, `cap_wins`, `coexistence`), stationary caps need `τ ≤ 8√3/9` (`stationary_bound`), and a boundary weight
leaves the equilibrium temperature at `T_H` only when it vanishes (`unbiased_boundary`). Ledger: C03-44 and C15-50
updated; new rows C05-84, C05-85, C10-115, C10-116; notes in `ledger/ANGULAR_RULE_HOST_CAVITY_20261119.md`. Each
module was built with the pinned Lean 4.35.0 on Linux against the Mathlib cache and the modules it imports; the 17
cited names resolve and depend only on `propext`, `Classical.choice` and `Quot.sound`. The angle-locality of the
wedge factor, the counting identities and the reduced cavity weight are inputs.

## Direction records, clock attachment and scale-chain tests (2026-11-15)

`Entropic/Extensions20261115/` (five modules, 56 theorems) formalizes the statements added to the full paper on
15 November 2026. `DirectionRecord`: for the four port phases of a Bloch wave on the diamond bonds, the Wilson
function is the direction record, `W = (3/2)|V|² = 8(1 − |f|²/16)` (`wilson_identity`), `W/8` is the weight of the
port vector outside the symmetric state (`direction_weight`), the hop is `−it σ·V` (`hop_eq_sigma_dot`, `hop_det`),
`W ≤ (8/3)|k|²` (`wilson_le_sq`), and the sum of cell projectors `Σ_b (I − P_b)` acts on a Bloch wave as `W/2`
(`record_symbol`), which gives the renewal decay generator and `γ_W = (d/4L_*) s` (`decay_symbol`, `gammaW_eq`).
`ClockCoupling`: `d/L_* = 1.07306…` and `γ_W = 0.26826…` from the C.8 volume identification (`bond_length_value`,
`gammaW_value`); a change of background by an admissible field leaves the relaxed total field and its minimum
unchanged (`relaxed_field_invariance`); the offsets of the four clock-attachment rows against the references
(`independent_row_offsets`, `renewal_triangle_offsets`, `reference_between`); one-loop running through fixed
thresholds carries a shift of `α⁻¹(μ_*)` unchanged, so `Δ ln Λ₃ = −(2π/9)Δα⁻¹` (`runChain_shift`,
`scale_sensitivity`) with ratios `0.51` and `4.1` (`scale_ratios`). `ScaleChainTests`, on the certified brackets
of `Spine` and `AppCDE`: the measured `G` selects a return coefficient in `(7.02, 7.04)` with one-σ ends near
`6.60` and `7.46` (`return_coefficient_fit`), seven is the only integer `n ≥ −200` within two σ
(`return_integer_unique`); the tau mass selects a second-shell coefficient in `(0.286, 0.288)` with ends near
`0.277` and `0.297` (`second_shell_fit`), and `2/7` is the only rational with denominator at most eleven within
one σ (`second_shell_rational_unique`); the muon offset at tenfold precision is `5.34…5.37σ` (`muon_forward`).
`ChainConstant`: the C.8 calibration at `m₄ = 2.3219` and at the fixed-exponent fits (`calibration_23219`,
`calibration_fixed_exponent`). `LabelRing`: `Tr (NT)^q = Tr T^q` for even `q` (`orientation_even`) and
`½ ln(27/8)` (`tree_density`). Ledger: C01-04, C01-05 and C01-17 updated; new rows C01-64, C03-175, C03-176,
C05-83, C10-105 to C10-114; notes in `ledger/CLOCK_AND_SCALE_CHAIN_20261115.md`. Each module was compiled with
the pinned Lean 4.35.0 on Linux against the Mathlib cache and the modules it imports; the namespace audit reports
zero nonstandard axioms and all 44 cited names resolve. The matched couplings, the chain constants and the
measured values are inputs; the clock attachment, the Wilson-mass identification and the Section 27 forecast
probabilities are not formalized. This entry also adds `ledger/INVERSION_GLUING_20261114.md`, which the entry
below cites.

## Inversion gluing (2026-11-14)

`Entropic/InversionGluing/` (two modules, 57 theorems) identifies the diamond graph with the cell complex
developed by point inversions through face centres. `Core` has no imports: the development (`develop`), the
closure rule (`closed_iff_balanced`: a word closes exactly when every port is used equally often from the two
orientation classes), the classification of closed six-words as three-port hexagons (`six_ring_iff`), and the
integer form of the statement that regular mirror-glued cells close no ring (`cheb_ne_pow`). `Bridge` proves
that `DiamondGreen.dNbr` is that neighbour rule (`embed_nbr`, `embed_injective`, `embed_walk`), keeps the
half-turn frame transport of `AppP.Num.mirror` (the plane reflection is its negative), and gives
`inversion_vacuum_compatible` and `joint_with_effective_model`. Ledger: C07-101 (girth), C07-128 to C07-133,
C03-157 and C07-107 rescoped; notes in `ledger/INVERSION_GLUING_20261114.md`. Both files were compiled with
the pinned Lean 4.35.0 on Windows against the existing build; the selection of the inversion vacuum by the
host dynamics is not formalized.

## Contact ledger, release ledger and redshift law (2026-10-29)

Three modules port the general parts of the 2026-10-26 held-out-test formalization, restated on the existing library. `Entropic/ContactLedger.lean`: for any sequence of proposed stock contacts under the acceptance rule and work register of Appendix O.3, kinetic energy plus register changes only by credits, the register never goes negative, heating is bounded by the initial register plus credits, and once both are spent the stock cannot end hotter (`run_heating_bounded`, `spent_register_no_heating`); the mismatch never rises. `Entropic/ReleaseLedger.lean`: committed plus released stock is conserved, the vacuum density is nonnegative and one-signed, `I_rel ≥ F(1)`, and some release happens at `a³ ≤ F(1)/I_rel`; for the paper's reference history (`F(1) = 0.6633922061`, `I_rel = 94.2116`) some release precedes redshift 4.2 (`reference_history_releases_early`), and for the standard-configuration fit (`I_rel = 92.327`) redshift 4.18 (`fitted_history_releases_early`). `Entropic/RAR/Redshift.lean`: with `a₀(z) = ε c H(z)` in `GalacticLaw.gObs`, the boost at fixed baryonic acceleration rises with `H(z)`, `cH/a₀ = 1/ε` at every redshift, and the deep-regime Tully–Fisher zero point moves as `M(z)/M(0) = H(0)/H(z)` (`btfr_redshift`). The held-out record itself, with its 2026-10-26 numbers and the two flags checked on 2026-10-29, is archived in [held-out record](verification/heldout_bestfit_2026-10-26.md).

## Regge graviton (2026-10-28)

`Entropic/ReggeGraviton/` (sixteen modules) proves the graviton step of Appendix H.10 at quadratic
order for a regular metric-Regge lattice, with the lattice symbol computed rather than cited. On the
Freudenthal–Kuhn triangulation of `ℤ⁴` (24 simplices per hypercube; the length-Regge lattice of
Dittrich et al., arXiv:2105.10808, not the centrally subdivided lattice of the cited symbol), the
quadratic Regge action reduces, after the four body diagonals are integrated out (`KC_eq`,
`Kred_schur`), to a Hermitian symbol on metric perturbations with `ε⁻² Kred(εk) → KEH(k)`
(`symbol_limit`), the Fourier kernel of `(√g R)⁽²⁾` (`KEH_quad`). So `∑_t A_t ε_t = ½∫√g R` at quadratic
order with coefficient exactly 1. In Frobenius-normalized coordinates the transverse-traceless
polarizations are an eigenspace with eigenvalue `−¼|k|²` (`KEHg_TT`), and the lattice operators converge
to the linearized Einstein operator in the strong-resolvent sense (`regge_strong_resolvent_normalized`).
The one input not derived in Lean is the exact flat Hessian of one Kuhn simplex (`hzL`). Record, the
independent review and the scope: [Regge graviton](verification/regge_graviton_2026-10-28.md).

## Effective dynamics and cluster extensions (2026-10-23)

Six modules under `Entropic/Extensions20261023` add 119 explicit theorem declarations to the import graph. The status table below counts them. The normal pinned Lean 4.35 build and module-based axiom audit include all six modules. Their earlier standalone checks used Lean/mathlib 4.19. See [extension scope and provenance](verification/extensions_2026-10-23.md) for the distinction between conditional mathematics and empirical calculations.

## Stock settling and finite renewal (2026-10-23)

Two modules address open points from an external review. See [scope and reading](verification/settling_renewal_2026-10-23.md).

- `Entropic/FiniteRenewal.lean`: Kac's return-time identity for any finite reversible dynamics, and a finite shift register whose readings have the product law on every window up to its length (ensemble over register states). The charged-lepton shell load 720^N holds exactly without memorylessness. The G_* chain does not transfer as derived: every finite reversible renewal is periodic with entropy rate zero, which the maximum-entropy-rate selection of App. H.4 rejects.
- `Entropic/StockSettling.lean`: any schedule of central pair contacts conserves linear and angular momentum; reversible maps preserve fine-grained Casimirs; on a signed work ledger the population at supply exhaustion does not depend on the contact rate; and with work proportional to σ² the settled fraction is min(1, σ_c²/σ²). The σ² scaling and the fixed supply per unit stock are stated hypotheses.

## Diamond-lattice Green function (2026-10-27)

`Entropic/DiamondGreen/` (six modules) closes the source-side lattice constant of Appendix C.5. Proved
unconditionally: the manuscript's Brillouin-zone integral `(2π)⁻³ ∫ 4/(16 − |1 + e^{ik₁} + e^{ik₂} + e^{ik₃}|²)`
equals the walk series of `[(4 − A)⁻¹]₀₀` (`greenDiamond_eq_integral`); on one sublattice two diamond steps
are `4 + (fcc step)`, so closed diamond walks of length `2n` number `∑ₖ C(n,k) 4^(n−k)` closed fcc walks of
length `k` (`dWalks_even`) and `G_tet(0) = P_fcc/3` (`greenDiamond_eq`); `G_tet(0) < ∞` (`greenDiamond_lt_top`);
the fcc integral representation of `P_fcc` (`returnFCC_eq_integral`); and the enclosure
`0.44822039438838 < √3/(4 agm(1, cos 15°)²) < 0.44822039438839` (`watsonAGM_bounds`). One classical result
is cited as a hypothesis, `WatsonFCC`: Watson's 1939 evaluation of the fcc integral, in Gauss's AGM form.
Given it, `G_tet(0)`, `S₀ = 3 ln 2/(32π G_tet(0))` and the source amplitude `ln(7/6)/(π G_tet(0))` are
bracketed (`manuscript_Gtet`, `SInfCell_bounds`, `source_amplitude_bounds`). Scope and independent
checks: [diamond Green function](verification/diamond_green_2026-10-27.md).

## Assumption compatibility (2026-10-23)

**Standalone build.** The compatibility result is its own Lake target and CI job:

```sh
lake exe cache get
lake build Compatibility
lake env lean scripts/CompatibilityAudit.lean
```

`Compatibility.lean` imports `Entropic.Compatibility.All` and `Entropic.Completion.All`, so the target builds 33 of the library's modules and nothing else. The audit checks every theorem in `Entropic.Compatibility` (147) and `Entropic.Completion` (228): none depends on an axiom beyond `propext`, `Classical.choice` and `Quot.sound`. It also prints the axioms of the three existence theorems, `effective_assumptions_compatible`, `spatial_history_assumptions_compatible` and `global_effective_assumptions_compatible`. Log: `verification/compatibility_audit_2026-10-28.log`. The `compatibility` badge above tracks this job.

`Entropic/Compatibility` proves `Nonempty EffectiveModel` (`Entropic.Compatibility.effective_assumptions_compatible`): one structure carrying the native closure root η and ε, the 1680-state Gibbs histories, the 720-state shell cycle, a finite positive stock shared by reconstruction, redistribution and nonzero reciprocal Newton forces, and an explicit expanding homogeneous Einstein solution with positive energy transfer, tied to the finite model through the same mass budget. It also proves that a fixed finite faithful archive and an exact dense-core RAR profile are each impossible. This is an effective subsystem, not a consistency proof of the full theory: the finite force system is not embedded in the expanding metric. `Entropic/Completion/InfiniteHistory.lean` gives one probability space for all integer times with the native Gibbs marginal and a measure-preserving reversible shift. Provenance and scope: [compatibility record](verification/compatibility_2026-10-23.md).

The completion modules extend this to `Nonempty GlobalModel` (`Entropic.Completion.global_effective_assumptions_compatible`): the exact native rooted history measure with the unique native η, and a global inhomogeneous clock/stock family with positive baryons, donor and retained stock, active release, radial contrast at every epoch and unbounded future proper time. The local pressure equations, density and volume evolution and component positivity are kernel checked; the coordinate Einstein-tensor reduction is checked separately in SymPy (`tools/completion_metric_check.py`). `Obstructions`, with `Compatibility.exact_dense_core_isEmpty`, records four incompatibilities (fixed finite archive against recoverable IID history, positive stock against the exact raw dense-core profile, one exchange vector against distinct streams, and bare against physical G without matching). `GlobalFloor.current_floor_fails_global_domain` proves that its first floor constant leaves the depletion-action domain; the selected-action certificate is local in time. This is not a microscopic or full-theory compatibility proof. Provenance, the 27 obligations and the global-floor candidate: [completion record](verification/completion_2026-10-23.md).

`Entropic/FourItems` adds two follow-up modules. `Streams`: a covariant 1+1 source/force decomposition for multistream exchange with energy conservation, positive internal allocation, an explicit two-stream witness and Bianchi-I constraint propagation (the Bianchi-I metric reduction is checked in SymPy, `tools/fouritems_bianchi_tensor.py`). `Selection`: matching underdetermination when the selected C.5 premise is omitted, affine kernel-normalization degeneracy, reversible energy-preserving swaps, and finite compensating-register bounds for an energy-conserving reset. These are not physical-selection proofs and contain no bound galaxy or native gravitational state. Record: [four open items](verification/fouritems_2026-10-23.md).

## Halo envelope premises (2026-10-24)

`Entropic/MicroEnvelope3D.lean` (GPT, ported) gives the pressure and depletion-floor identities, a weighted Schur bound and the matched-family stability margins of the isentropic envelope. `Entropic/EnvelopePremises.lean` separates its premises: the exponent γ = 2 is the stiffest member of the warm family that stays causal at every density (`causal_iff`, `stiff_limit`); a universal pair kernel has bounded range across compositions (`pair_coefficient_bounds`), so the matched coefficient ζ ∝ M_b must be a state label; matching gives `g(a) = 2η(1+η)a₀` and a closed-form envelope solution and stock (`envelope_mass_matched`); a stock reaching radius L needs a stock-to-baryon ratio of at least (L/r_M − 1)/2 (`stock_ratio_lower_bound`); and the retained and detected baryon fractions `k/S` and `(1+k)/(1+S)` are distinguished (`retained_fraction`, `detected_fraction_formula`). Scope and the weak-lensing comparison: [envelope premises](verification/envelope_premises_2026-10-24.md).

## Electromagnetic extension (2026-10-24)

`Entropic/Electromagnetism/` holds the algebra behind Appendix S of the manuscript, in seven modules with 105 theorems. `Gauge` and `Spectrum` cover the charged hopping and Gauss-law algebra, closed-graph neutrality, the rotor shift identity on sequences, and the lattice Maxwell symbol with exactly two transverse directions at nonzero momentum. `Mechanisms` covers projective phase freedom, the finite-matrix rotor obstruction, Gaussian square completion, the composite Berry connection's vanishing linear term and the leading loop coefficient. `NativeSelection` covers the native bridge traces and its common-average coefficients, the aligned exchange spectrum and the empty fermion vacuum. `Coupling` covers the commutants, central-transfer freedom, response algebra, the diamond matching condition and the unified-normalization scale bound. `Stiffness` covers the algebra of S.9 and S.10: the cubic invariant and mean-field coupling of the native gluing, the bound keeping its induced stiffness below the compact $U(1)$ deconfinement value, the lepton bound $\alpha^{-1}<33$, the $SU(2)_L$ coefficient and the positivity of an asymptotically free inverse coupling, and the Haar-averaged transfer eigenvalue $1-2(1-k)/(d+1)$ with its color instance $13/14$. `ReadableLink` covers the qutrit-qubit link as the candidate electroweak record: its central charge acts on the link as $3-2=1$, giving hypercharge $1/6$; a cube root of unity on the qutrit has determinant one, acts on the link as $\omega$ and is invisible to every conjugation channel (triality); the isotropic channel compressed to a two-dimensional support keeps its traceless multiplier, so a qubit record carried through the color channel gets $13/14$, a pinned record gets $1$, and the required $SU(2)_L$ multiplier $0.94915$ lies strictly between; the read cap $d_1d_2\le6$ enters as a named hypothesis citing Størmer, Woronowicz and Choi. The operator relations are hypotheses: the modules do not derive electromagnetism from the native vertex, fix the electric charge, or select a Coulomb phase. Scope: `ledger/ELECTROMAGNETISM_20261024.txt`, `ledger/EM_STIFFNESS_20261024.txt` and `ledger/READABLE_LINK_20261025.txt`.

## Contact selection (2026-10-24)

`Entropic/ContactSelection.lean` gives the statistical and mechanical identities behind a stock-contact selection rule. It does not give a microscopic exchange operator, a rate, a cluster gate or halo formation. The Section 15 gap function is the relative entropy of geometric distributions: it is nonnegative and vanishes at the Bose occupation (`boseGap_eq_relEnt`, `relEnt_nonneg`, `boseGap_at_nStar`), with curvature `1/(n(1+n))` (`boseGap_second_derivative`). The quadratic field mismatch `(δg)²/8πG` is its Gaussian limit exactly under the equipartition condition `𝒩Θ = g_b² n(1+n)/4πG` (`equipartition_matching`). Local detailed balance suppresses uphill transitions as the bath temperature goes to zero (`uphill_rate_vanishes`). A symmetric mobility on orbit populations never raises the functional (`symmetric_flow_dissipates`), and pair impulses along the separation conserve momentum and angular momentum (`pair_impulse_conserves_angular_momentum`). The module also holds the algebra of the stiff-coupling amplification (`stiff_coupling_amplification`), the Vlasov–Poisson acceleration scaling (`vp_acceleration_scaling`) and the counterexample to clip-and-renormalise (`clip_renormalise_not_minimal`). Thirteen statements are ported from GPT's contact-bridge note. Section 3 adds eight identities used by the cluster and galaxy sections of the manuscripts: the enclosed stock-to-baryon ratio equals the occupation (`occupation_is_enclosed_ratio`), the budget clip is optimal and monotone (`clip_optimal`, `clip_monotone`), the weak-lensing stock bound (`lensing_stock_bound`), arithmetic checks on the X-COP comparison (`field_response_misses_clusters`, `cohort_between_xcop`) and on the redshift test (`redshift_ratio_precision`), and the bookkeeping statement `no_cells_no_bias`. Section 4 adds the response-cell energy reservoir: in the Rayleigh-Jeans regime the cell energy density is `g a0 (1+x)/4πG` (`cell_energy_density_RJ`), which gives `V_f²` per unit supported stock in the deep regime (`cell_reservoir_deep`), and a numerical bound on the X-COP core reservoirs (`cluster_core_reservoir_small`). Cluster protection is a premise, not a theorem: observed-cluster runs of the ungated rule rearrange cluster stock. Scope: [contact selection](verification/contact_selection_2026-10-24.md).

`Entropic/RAR/Pendular.lean` gives the algebra of the Section 15 response cell read as the horizon-thermal tilt mode of the transverse frame, with lever `ℓ = g_share,eff c/H`. A pendulum potential `M g ℓ (1 − cos θ)` has `ω² = g/ℓ` (`tilt_frequency_sq`). With `x = 2πω/H` (a definition: `ħω/k_BT_H` at `T_H = ħH/2πk_B`), `x² = g/a₀` with `a₀ = g_share,eff cH/4π²` (`gap_sq`, `gap_eq`), `x = 1` exactly at `g = a₀` (`unit_gap_iff`), the projected-field gap is `x√cos δ` (`gap_tilt`), and the excess `g·n_B(x)` lies between `√(g a₀) − g/2` and `√(g a₀)` (`excess_bounds`). A local relativistic director tilt, `ω = c/ξ`, has a horizon gap above one for every `ξ < 2πc/H` (`local_mode_frozen`), and it matches the cell gap only when `ξ² = c²ℓ/g` (`coherence_length`). The Unruh form is `x² = (2π)²(g/c)/(κH)` (`gap_unruh`). The tilt-mode identification, its horizon thermalization and the lever are physical premises (ledger C02-04) and are not derived here. The thermodynamic lever gives the algebra of the lever coefficient: a static frame holding an oriented record of entropy `s` at the Unruh temperature of the projected field has free energy `−s T_U cos δ` and pull `s T_U (1 − cos δ)` (`grip_free_energy`, `grip_stiffness`); with the register enthalpy `S k_B T_H` as inertia at the arm `c/H`, `ω² = g/((S/s)c/H)`, so `κ = S/s` (`thermo_lever`, `thermo_gap_sq`). The RAR window excludes `s = ln 2` and `s = 3/2` and contains one nat (`one_bit_excluded`, `three_halves_excluded`, `one_nat_allowed`), and `S = βU + ln Z` with `βU = 3/2` gives the transverse pair exactly one nat (`closure_split`). The Unruh reading and the one-nat record are premises.
