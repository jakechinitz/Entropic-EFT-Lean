import EntropicEFT.Representation.FusionSpec

/-!
# EntropicEFT.Marked.SingleStrandRecord

LOCAL CONTRACT
* Manuscript: repaired H.9 and Appendix O.13 record-energy reading.
* Purpose: make the "one response strand versus two deposits" distinction explicit in types.
* Closed finite mathematics:
  - the response index has three modes;
  - a selected single canonical response phase space therefore has three coordinate/momentum pairs;
  - its unit-frequency zero-point ledger is `3/2`;
  - the first-level operator record has labels `(a,b)` and therefore nine matrix-unit labels;
  - the standard matrix-unit Hilbert--Schmidt Gram is the identity;
  - the commutator/Liouvillian eigenvalue on the degenerate first-excitation record level is zero;
  - an explicit two-deposit countermodel has six canonical pairs and vacuum energy `3`.
* External analytic mathematics: identifying `exp (-ξ^2/2)` with the unnormalized
  coordinate wavefunction of the three-mode unit-frequency oscillator.
* Conditional realization: the Hubbard--Stratonovich auxiliary is physically/canonically
  realized by this one phase space; the history index is the dual/operator end of the same
  strand; `W_*` uses the commutator (difference-sign) record dynamics and prepares a fresh
  strand per renewal vertex.
* Important nonclaim: a three-variable Hubbard--Stratonovich integral, by itself, does NOT
  logically manufacture conjugate momenta or a physical oscillator Hamiltonian.  The
  canonical single-strand realization is a named model identification, not a theorem of
  Gaussian integration alone.
-/

namespace EntropicEFT.Marked

/-- Spatial response modes of the closure vector. -/
abbrev ResponseMode := Fin 3

/-- Number of independent response coordinates. -/
def responseModeCount : ℕ := Fintype.card ResponseMode

theorem responseModeCount_eq_three : responseModeCount = 3 := by
  simp [responseModeCount]

/-- A finite-level bookkeeping model of one response Fock strand: vacuum plus one
first excitation carrying a spatial-vector index.  This is enough for the record-label
and zero-point-energy audit; it is not a truncation used in the physical dynamics. -/
inductive FirstLevelFock where
  | vacuum
  | one (a : ResponseMode)
  deriving DecidableEq

/-- Occupation number on the finite bookkeeping model. -/
def FirstLevelFock.occupation : FirstLevelFock → ℕ
  | .vacuum => 0
  | .one _ => 1

/-- Number of canonical coordinate/momentum pairs in the selected one-strand realization. -/
def singleStrandCanonicalPairCount : ℕ := responseModeCount

theorem singleStrandCanonicalPairCount_eq_three : singleStrandCanonicalPairCount = 3 := by
  simp [singleStrandCanonicalPairCount, responseModeCount]

/-- Unit-frequency zero-point energy of the selected response phase space. -/
def singleStrandZeroPointEnergy : ℚ := (singleStrandCanonicalPairCount : ℚ) / 2

theorem singleStrandZeroPointEnergy_eq_three_halves :
    singleStrandZeroPointEnergy = 3/2 := by
  norm_num [singleStrandZeroPointEnergy, singleStrandCanonicalPairCount, responseModeCount]

/-- First-level diagonal Hamiltonian ledger `N + 3/2`.  It is the finite-level form of
`sum_a a_a† a_a + 3/2` needed by the audit. -/
def FirstLevelFock.energy : FirstLevelFock → ℚ
  | .vacuum => singleStrandZeroPointEnergy
  | .one _ => 1 + singleStrandZeroPointEnergy

theorem vacuum_energy_eq_three_halves :
    FirstLevelFock.energy .vacuum = 3/2 := by
  norm_num [FirstLevelFock.energy, singleStrandZeroPointEnergy,
    singleStrandCanonicalPairCount, responseModeCount]

/-- All three first excitations are degenerate in the canonical unit-frequency frame. -/
theorem first_excitation_energy (a : ResponseMode) :
    FirstLevelFock.energy (.one a) = 5/2 := by
  norm_num [FirstLevelFock.energy, singleStrandZeroPointEnergy,
    singleStrandCanonicalPairCount, responseModeCount]

/-- One canonical phase-space point.  The fact that the selected realization contains this
structure ONCE is the type-level meaning of "one symplectic sector". -/
structure SingleResponsePhasePoint where
  ξ : ResponseMode → ℝ
  π : ResponseMode → ℝ

/-- A single renewal event in the selected canonical realization. -/
structure SingleStrandEvent where
  response : SingleResponsePhasePoint

/-- The nine record labels are matrix-unit/operator labels, not nine independent oscillators. -/
abbrev RecordLabel := ResponseMode × ResponseMode

/-- Exact cardinality of the first-excitation operator record. -/
def recordLabelCount : ℕ := Fintype.card RecordLabel

theorem recordLabelCount_eq_nine : recordLabelCount = 9 := by
  simp [recordLabelCount]

/-- Standard Hilbert--Schmidt Gram of matrix-unit labels `|a><b|`.
Using matrix-unit coordinates makes the identity Gram explicit without importing an
infinite-dimensional Fock-space construction. -/
def hsGram (x y : RecordLabel) : ℚ := if x = y then 1 else 0

theorem hsGram_self (x : RecordLabel) : hsGram x x = 1 := by
  simp [hsGram]

theorem hsGram_offdiag {x y : RecordLabel} (h : x ≠ y) : hsGram x y = 0 := by
  simp [hsGram, h]

/-- Energy of either first-excitation endpoint of a record matrix unit. -/
def endpointEnergy (_a : ResponseMode) : ℚ := 5/2

/-- Difference-sign generator on the operator record: the finite matrix-unit form of
`L=[H,·]`. -/
def recordLiouvillianEigenvalue (r : RecordLabel) : ℚ :=
  endpointEnergy r.1 - endpointEnergy r.2

/-- The nine transition labels are stationary under the difference-sign generator because
the first-excitation triplet is degenerate. -/
theorem recordLiouvillianEigenvalue_eq_zero (r : RecordLabel) :
    recordLiouvillianEigenvalue r = 0 := by
  norm_num [recordLiouvillianEigenvalue, endpointEnergy]

/-- The O.13 stationary one-sided energy ledger associated with the selected single strand. -/
noncomputable def stationaryRecordEnergy : ℚ := singleStrandZeroPointEnergy

noncomputable def stationaryRecordEnergyR : ℝ := (stationaryRecordEnergy : ℝ)

theorem stationaryRecordEnergy_eq_three_halves : stationaryRecordEnergy = 3/2 := by
  exact singleStrandZeroPointEnergy_eq_three_halves

theorem stationaryRecordEnergyR_eq_three_halves : stationaryRecordEnergyR = 3/2 := by
  norm_num [stationaryRecordEnergyR, stationaryRecordEnergy,
    singleStrandZeroPointEnergy, singleStrandCanonicalPairCount, responseModeCount]

/-- A record matrix-unit label does not add a one-particle occupation to the stationary
energy ledger; it is an operator/transition label. -/
theorem no_extra_quantum_from_record_label (r : RecordLabel) :
    stationaryRecordEnergy + recordLiouvillianEigenvalue r = 3/2 := by
  simp [recordLiouvillianEigenvalue, endpointEnergy, stationaryRecordEnergy_eq_three_halves]

/-- Explicit countermodel with two genuinely independent response phase spaces.  This is a
different type from `SingleStrandEvent`; it is what a literal two-deposit interpretation
would have to add. -/
structure TwoDepositEvent where
  present : SingleResponsePhasePoint
  history : SingleResponsePhasePoint

/-- Six canonical pairs in the explicit two-copy countermodel. -/
def twoDepositCanonicalPairCount : ℕ := 2 * singleStrandCanonicalPairCount

theorem twoDepositCanonicalPairCount_eq_six : twoDepositCanonicalPairCount = 6 := by
  norm_num [twoDepositCanonicalPairCount, singleStrandCanonicalPairCount,
    responseModeCount]

/-- Ground-state energy of two genuinely independent three-mode sectors. -/
def twoDepositZeroPointEnergy : ℚ := 2 * singleStrandZeroPointEnergy

theorem twoDepositZeroPointEnergy_eq_three : twoDepositZeroPointEnergy = 3 := by
  norm_num [twoDepositZeroPointEnergy, singleStrandZeroPointEnergy,
    singleStrandCanonicalPairCount, responseModeCount]

/-- Ordinary analytic input used to interpret the normalized three-variable Gaussian kernel
as the coordinate ground-state wavefunction of a unit-frequency oscillator.  This package is
mathematics, but it is not proved in this finite audit module. -/
structure ThreeModeGroundStateMath where
  gaussianKernelIsVacuumWavefunction : Prop
  unitFrequencyHamiltonian : Prop
  threeIndependentModes : Prop

/-- Representation-theory input for the operator doubling.  In three spatial dimensions the
vector representation is self-dual, so the operator labels carry `V1 ⊗ V1*`, equivalently
`V1 ⊗ V1`, and decompose as `V0 ⊕ V1 ⊕ V2`.  The finite cardinality/Gram statements above
are already closed; this structure isolates the SU(2)/SO(3) representation theorem. -/
structure OperatorDoublingRepresentationMath where
  vectorSelfDual : Prop
  decomposesAsZeroOneTwo : Prop

/-- The selected physical/model identification connecting the repaired H.9 HS auxiliary to
the finite one-strand record model.  This is the exact place where the construction chooses
operator doubling rather than two independent oscillator deposits. -/
structure SingleStrandCanonicalRealization where
  groundStateMath : ThreeModeGroundStateMath
  representationMath : OperatorDoublingRepresentationMath
  hsAuxiliaryIsCanonicalResponseCoordinate : Prop
  oneHSAuxiliaryPerRenewal : Prop
  canonicalFrameMatchesClosureCoupling : Prop
  recordIsOperatorDoublingOfSameStrand : Prop
  wStarUsesDifferenceSignLiouvillian : Prop
  freshStrandPerRenewalVertex : Prop

namespace SingleStrandCanonicalRealization

/-- Conjunction used by downstream physical bridges. -/
def holds (R : SingleStrandCanonicalRealization) : Prop :=
  R.groundStateMath.gaussianKernelIsVacuumWavefunction ∧
  R.groundStateMath.unitFrequencyHamiltonian ∧
  R.groundStateMath.threeIndependentModes ∧
  R.representationMath.vectorSelfDual ∧
  R.representationMath.decomposesAsZeroOneTwo ∧
  R.hsAuxiliaryIsCanonicalResponseCoordinate ∧
  R.oneHSAuxiliaryPerRenewal ∧
  R.canonicalFrameMatchesClosureCoupling ∧
  R.recordIsOperatorDoublingOfSameStrand ∧
  R.wStarUsesDifferenceSignLiouvillian ∧
  R.freshStrandPerRenewalVertex

end SingleStrandCanonicalRealization

/-- Competing amortized chain reading.  It can reuse one strand across adjacent events and
therefore need not double the average zero-point cost, but it generically introduces an
adjacent-record correlation question.  No inhabitant is selected by this repository. -/
structure ChainRecordAlternativeSpec where
  reusesStrandAcrossAdjacentVertices : Prop
  adjacentRecordCorrelationsDerived : Prop

end EntropicEFT.Marked
