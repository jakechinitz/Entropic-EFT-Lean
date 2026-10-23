import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Positivity of classical mass reconstruction is componentwise, distinct from
Hilbert-space isometry. This finite theorem is the source-kernel counterpart of
the operator results. Causality/locality are additional conditions on the map. -/
noncomputable section
namespace Entropic.PositiveReconstruction
open Finset
variable {n m : Type*} [Fintype n] [Fintype m]

def reconstruct (C : Matrix m n ℝ) (x : n → ℝ) (i : m) := ∑ j, C i j * x j

theorem nonnegative (C : Matrix m n ℝ) (x : n → ℝ)
    (hC : ∀ i j, 0 ≤ C i j) (hx : ∀ j, 0 ≤ x j) :
    ∀ i, 0 ≤ reconstruct C x i := by
  intro i
  exact sum_nonneg fun j _ => mul_nonneg (hC i j) (hx j)

theorem total_preserved (C : Matrix m n ℝ) (x : n → ℝ)
    (hC : ∀ j, ∑ i, C i j = 1) :
    ∑ i, reconstruct C x i = ∑ j, x j := by
  unfold reconstruct
  rw [sum_comm]
  simp_rw [← sum_mul, hC, one_mul]

theorem source_adjoint (C : Matrix m n ℝ) (x : n → ℝ) (f : m → ℝ) :
    ∑ i, f i * reconstruct C x i = ∑ j, x j * (∑ i, C i j * f i) := by
  simp only [reconstruct, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro i _
  ring

/-- Effect convention: amplitudes are square roots. -/
theorem effect_complement {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1) :
    Real.sqrt e ^ 2 + Real.sqrt (1 - e) ^ 2 = 1 := by
  rw [Real.sq_sqrt h0, Real.sq_sqrt (sub_nonneg.mpr h1)]
  ring

/-- Using e as the transmitted amplitude but 1-e as the complementary
probability is normalized only in the sharp cases. -/
theorem mixed_convention_iff (e : ℝ) : e ^ 2 + (1 - e) = 1 ↔ e = 0 ∨ e = 1 := by
  constructor
  · intro h
    have : e * (e - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with hz | ho
    · exact Or.inl hz
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num

end Entropic.PositiveReconstruction
