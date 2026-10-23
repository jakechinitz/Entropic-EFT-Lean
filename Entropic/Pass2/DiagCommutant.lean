import Mathlib.Tactic

/-! Second pass, chunk 15: C14-73 (c). The commutant of J_z ⊗ J_z on V_{3/2} ⊗ V_{3/2} consists of the
matrices supported on pairs (i, j) with equal eigenvalue, and there are 48 such pairs. -/

namespace Entropic.Pass2.DiagCommutant
open Matrix

/-- Matrices commuting with a diagonal matrix are those supported on its eigenvalue blocks. -/
theorem comm_diagonal_iff {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℂ) (X : Matrix n n ℂ) :
    X * diagonal d = diagonal d * X ↔ ∀ i j, d i ≠ d j → X i j = 0 := by
  constructor
  · intro h i j hij
    have h2 : X i j * d j = d i * X i j := by
      simpa only [Matrix.mul_diagonal, Matrix.diagonal_mul] using congrFun (congrFun h i) j
    have h3 : X i j * (d j - d i) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h3 with h' | h'
    · exact h'
    · exact absurd (sub_eq_zero.mp h').symm hij
  · intro h; ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : d i = d j
    · rw [hij, mul_comm]
    · rw [h i j hij]; ring

/-- 4 J_z ⊗ 4 J_z on the product ladder basis (index 4a + b, weights 3, 1, −1, −3). -/
def dzz (i : Fin 16) : ℤ := (3 - 2 * (i.val / 4 : ℤ)) * (3 - 2 * (i.val % 4 : ℤ))

/-- C14-73 (c): the commutant of J_z ⊗ J_z is the space of matrices supported on the 48 index pairs
with equal eigenvalue (eigenvalue multiplicities 2, 2, 4, 4, 2, 2; 2² + 2² + 4² + 4² + 2² + 2² = 48). -/
theorem jzz_commutant (X : Matrix (Fin 16) (Fin 16) ℂ) :
    X * diagonal (fun i => (dzz i : ℂ)) = diagonal (fun i => (dzz i : ℂ)) * X ↔
      ∀ i j, dzz i ≠ dzz j → X i j = 0 := by
  rw [comm_diagonal_iff]
  simp only [ne_eq, Int.cast_inj]

theorem jzz_support_card : (Finset.univ.filter fun p : Fin 16 × Fin 16 => dzz p.1 = dzz p.2).card = 48 := by
  decide +kernel

end Entropic.Pass2.DiagCommutant
