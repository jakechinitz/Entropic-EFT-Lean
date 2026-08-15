import EntropicEFT.Core.Prelude

/-!
# EntropicEFT.Representation.SpinDimensions

LOCAL CONTRACT
* Manuscript: Appendix B.4.2e; H.9.
* Encodes twice-spin as a natural number, avoiding half-integer arithmetic.
* Closed outputs: the dimension/complement arithmetic and unique endpoint match.
* Does not prove: Clebsch--Gordan decomposition itself; see `FusionSpec`.
-/

namespace EntropicEFT.Representation

/-- Dimension of V_j when `twoJ = 2j`: 2j+1. -/
def spinDim (twoJ : ℕ) : ℕ := twoJ + 1

/-- Dimension of the maximal coupled multiplet V_(2j): 4j+1. -/
def maximalFusionDim (twoJ : ℕ) : ℕ := 2*twoJ + 1

/-- Dimension left after removing V_(2j) from V_j tensor V_j. -/
def nonmaxComplementDim (twoJ : ℕ) : ℕ :=
  spinDim twoJ ^ 2 - maximalFusionDim twoJ

/-- Algebraically the complement dimension is `(2j)^2`. -/
theorem nonmaxComplementDim_eq_square (twoJ : ℕ) :
    nonmaxComplementDim twoJ = twoJ^2 := by
  unfold nonmaxComplementDim spinDim maximalFusionDim
  ring_nf
  omega

/-- A spin-s present/history pair has dimension `(2s+1)^2`. -/
def markedDim (twoS : ℕ) : ℕ := (twoS + 1)^2

/-- Endpoint equality of the multiplicity-free representation ranges is `2j = 2s+1`. -/
def ComplementEndpointMatch (twoJ twoS : ℕ) : Prop := twoJ = twoS + 1

theorem closure_vector_selects_three_halves : ComplementEndpointMatch 3 2 := by
  simp [ComplementEndpointMatch]

theorem primitive_dim_three_halves : spinDim 3 = 4 := by norm_num [spinDim]
theorem transmitted_dim_three_halves : maximalFusionDim 3 = 7 := by norm_num [maximalFusionDim]
theorem complement_dim_three_halves : nonmaxComplementDim 3 = 9 := by norm_num [nonmaxComplementDim, spinDim, maximalFusionDim]
theorem marked_vector_pair_dim : markedDim 2 = 9 := by norm_num [markedDim]
theorem sixteen_split : spinDim 3 ^ 2 = maximalFusionDim 3 + nonmaxComplementDim 3 := by norm_num [spinDim, maximalFusionDim, nonmaxComplementDim]

end EntropicEFT.Representation
