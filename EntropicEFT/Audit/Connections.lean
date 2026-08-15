import EntropicEFT.Gravity.Static
import EntropicEFT.Cosmology.SaturatedDust
import EntropicEFT.Gauge.ProjectiveColor
import EntropicEFT.Marked.CorrectedH9
import EntropicEFT.Marked.SingleStrandRecord

/-!
# EntropicEFT.Audit.Connections

LOCAL CONTRACT
* Purpose: collect cross-sector identities discovered by dependency auditing.
* Every theorem here is exact algebra imported from the sector modules; none is new physics.
* These results are useful precisely because they show when two apparent checks are NOT independent.
-/

namespace EntropicEFT.Audit
open EntropicEFT.UV EntropicEFT.Edge EntropicEFT.Gravity
open EntropicEFT.Cosmology EntropicEFT.Marked EntropicEFT.Gauge

/-- H.9 repair: the full Gibbs cost contains a vector mean-closure piece and a scalar
irreducible quantum-variance piece. -/
theorem h9_closure_is_two_piece (b : BoundaryCode) :
    quantumK2R b = classicalClosureSqR b + quantumVarianceR b :=
  closure_decomposition_real b

/-- The scalar quantum-variance term can never be silently dropped on the 1680-state ensemble. -/
theorem h9_quantum_variance_strictly_positive :
    ∀ b ∈ boundaryStates, 22 ≤ quantumVarianceR b := by
  intro b hb
  have h := (quantumVariance3_bounds b hb).1
  have hr : (66 : ℝ) ≤ (quantumVariance3 b : ℝ) := by exact_mod_cast h
  simp [quantumVarianceR]
  linarith


/-- In the selected single-strand canonical realization, the response phase space has exactly
three canonical pairs and therefore zero-point ledger `3/2`. -/
theorem single_strand_record_ledger :
    singleStrandCanonicalPairCount = 3 ∧ stationaryRecordEnergy = 3/2 := by
  constructor
  · exact singleStrandCanonicalPairCount_eq_three
  · exact stationaryRecordEnergy_eq_three_halves

/-- Operator doubling changes the record-label cardinality to nine without doubling the
number of canonical response pairs. -/
theorem operator_doubling_is_label_not_pair_doubling :
    recordLabelCount = 9 ∧ singleStrandCanonicalPairCount = 3 := by
  exact ⟨recordLabelCount_eq_nine, singleStrandCanonicalPairCount_eq_three⟩

/-- A literal two-deposit countermodel is visibly a different finite ledger. -/
theorem literal_two_deposit_countermodel :
    twoDepositCanonicalPairCount = 6 ∧ twoDepositZeroPointEnergy = 3 := by
  exact ⟨twoDepositCanonicalPairCount_eq_six, twoDepositZeroPointEnergy_eq_three⟩

/-- Matched weak-field G and electron-induced G are the same normalization identity once the
source map and cell normalization are substituted; they are not independent measurements. -/
theorem matched_G_is_induced_G {hbar c L G0 : ℝ}
    (hh : hbar ≠ 0) (hc : c ≠ 0) (hL : L ≠ 0)
    (hG : G0 ≠ 0) (hlog : Real.log 2 ≠ 0) :
    matchedG hbar c L G0 = inducedG c hbar L :=
  matchedG_eq_inducedG hh hc hL hG hlog

/-- Galactic acceleration and pinned committed abundance cancel the shared epsilon exactly. -/
theorem galactic_abundance_reciprocity {g c H : ℝ}
    (he : epsilon g ≠ 0) :
    galacticScaleFromEpsilon g c H * committedAbundance g = c*H :=
  acceleration_abundance_identity he

/-- Primitive open-route recoupling contains the exact rational 7/6. -/
theorem projective_route_ratio :
    routeDoubletEigenvalue / routeSingletEigenvalue = (7/6 : ℚ) :=
  primitive_route_ratio

/-- Three appearances of `3/2` play different algebraic roles.  Under the selected
single-strand realization the closure-evidence weight and O.13 zero-point ledger share the
same underlying three-coordinate response count, so they must NOT be advertised as
independent numerical evidence.  The electron `3/2` remains the reciprocal of the separate
`2/3` transverse export factor. -/
def threeHalvesRoleAudit : List String :=
  ["closure evidence: determinant weight of 3 closure-response coordinates",
   "O.13 selected realization: zero-point ledger of the same 3 response modes",
   "electron scale: reciprocal of the separate 2/3 transverse export"]

end EntropicEFT.Audit
