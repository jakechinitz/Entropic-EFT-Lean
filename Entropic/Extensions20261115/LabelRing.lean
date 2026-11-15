import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Labels on the inversion complex (Appendix J.4)

* For the ring transfer matrix `T` and the label reversal `N` with `NT = TN` and `N² = I`,
  `Tr (NT)^q = Tr T^q` for even `q` (`orientation_even`): on the inversion complex, whose elementary
  rings have six cells, the two label-orientation readings coincide. For odd `q` the oriented reading
  is `Tr (N T^q)` (`orientation_odd`).
* The four-regular tree value of the Gaussian determinant density, `½ ln(27/8) = 0.60820`
  (`tree_density`).

The numerical ring residuals and determinant densities of J.4 are computed in
`02 Research/Label sector on inversion complex 2026-11-14` and are not formalized.
-/

noncomputable section
namespace Entropic.Extensions20261115.LabelRing
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- J.4: a label reversal commuting with the ring transfer and squaring to the identity drops out of
every even power. -/
theorem orientation_even (N T : Matrix n n R) (hc : N * T = T * N) (hN : N * N = 1) (k : ℕ) :
    (N * T) ^ (2 * k) = T ^ (2 * k) ∧ trace ((N * T) ^ (2 * k)) = trace (T ^ (2 * k)) := by
  have hcomm : Commute N T := hc
  have h1 : (N * T) ^ (2 * k) = T ^ (2 * k) := by
    rw [hcomm.mul_pow, pow_mul, pow_two, hN, one_pow, one_mul]
  exact ⟨h1, by rw [h1]⟩

/-- J.4: for an odd ring the oriented reading keeps one reversal, `(NT)^{2k+1} = N T^{2k+1}`. -/
theorem orientation_odd (N T : Matrix n n R) (hc : N * T = T * N) (hN : N * N = 1) (k : ℕ) :
    (N * T) ^ (2 * k + 1) = N * T ^ (2 * k + 1) := by
  have hcomm : Commute N T := hc
  rw [hcomm.mul_pow, pow_succ N, pow_mul, pow_two, hN, one_pow, one_mul]

/-- The elementary rings of the inversion complex have six cells: the orientation fork vanishes. -/
theorem orientation_six (N T : Matrix n n R) (hc : N * T = T * N) (hN : N * N = 1) :
    trace ((N * T) ^ 6) = trace (T ^ 6) := (orientation_even N T hc hN 3).2

/-- J.4: the four-regular tree spectral density gives `½ ln(27/8) ∈ (0.60819, 0.60821)`. -/
theorem tree_density : 0.60819 < (1/2) * Real.log (27/8) ∧ (1/2) * Real.log (27/8) < 0.60821 := by
  have e : Real.log (27/8) = 3 * (-Real.log (1 - 1/3)) := by
    rw [show (27 : ℝ) / 8 = ((1 - 1/3 : ℝ)⁻¹) ^ 3 by norm_num, Real.log_pow, Real.log_inv]; push_cast; ring
  have hs := Real.abs_log_sub_add_sum_range_le (show |(1/3 : ℝ)| < 1 by norm_num) 12
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  rw [abs_le] at hs
  rw [e]
  constructor <;> linarith [hs.1, hs.2]

end Entropic.Extensions20261115.LabelRing
