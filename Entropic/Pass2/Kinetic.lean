import Mathlib.Tactic

/-! Second pass, chunk 18: C15-30. For an isometry L (L Lᵀ = I) with P_Q = Lᵀ L and P₃ = I − P_Q, and
φ = Lᵀ d, the derivative ∂φ = (∂Lᵀ) d + Lᵀ ∂d splits orthogonally:
|∂φ|² = |∂d + A d|² + |B d|² with A = L ∂Lᵀ and B = P₃ ∂Lᵀ (one direction μ; sum over μ termwise).
C15-43 (characters): det(I + P_g)·χ_std(g) equals 48 at the identity and 0 on the other four classes of S₄,
the character of two copies of the regular representation tensored with ℂ². -/

namespace Entropic.Pass2.Kinetic
open Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- C15-30: |M d + Lᵀ d'|² = |d' + (L M) d|² + |(1 − Lᵀ L) M d|² when L Lᵀ = 1. -/
theorem kinetic_split (L : Matrix m n ℝ) (hL : L * Lᵀ = 1) (M : Matrix n m ℝ) (d d' : m → ℝ) :
    (M *ᵥ d + Lᵀ *ᵥ d') ⬝ᵥ (M *ᵥ d + Lᵀ *ᵥ d') =
      (d' + (L * M) *ᵥ d) ⬝ᵥ (d' + (L * M) *ᵥ d) + ((1 - Lᵀ * L) * M) *ᵥ d ⬝ᵥ ((1 - Lᵀ * L) * M) *ᵥ d := by
  set v := M *ᵥ d
  set w := d' + L *ᵥ v
  have hw : (L * M) *ᵥ d = L *ᵥ v := by rw [← Matrix.mulVec_mulVec]
  have hP : ((1 - Lᵀ * L) * M) *ᵥ d = v - Lᵀ *ᵥ (L *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  have hsplit : v + Lᵀ *ᵥ d' = Lᵀ *ᵥ w + (v - Lᵀ *ᵥ (L *ᵥ v)) := by
    simp only [w, Matrix.mulVec_add]; abel
  have hiso : ∀ x : m → ℝ, Lᵀ *ᵥ x ⬝ᵥ Lᵀ *ᵥ x = x ⬝ᵥ x := by
    intro x
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]
  have horth : Lᵀ *ᵥ w ⬝ᵥ (v - Lᵀ *ᵥ (L *ᵥ v)) = 0 := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_sub,
      Matrix.mulVec_mulVec (L *ᵥ v) L Lᵀ, hL, Matrix.one_mulVec, sub_self, zero_dotProduct]
  rw [hw, hP, hsplit]
  rw [add_dotProduct (Lᵀ *ᵥ w), dotProduct_add, dotProduct_add, hiso, horth,
    dotProduct_comm (v - Lᵀ *ᵥ (L *ᵥ v)) (Lᵀ *ᵥ w), horth]
  ring

/-- Permutation matrix of g : Fin 4 → Fin 4. -/
def pmat (g : Fin 4 → Fin 4) : Matrix (Fin 4) (Fin 4) ℤ := fun i j => if g j = i then 1 else 0

/-- Character of Λ(ℂ⁴) ⊗ V_std at g: det(I + P_g) · (#fix(g) − 1). -/
def chi (g : Fin 4 → Fin 4) : ℤ := (1 + pmat g).det * (((Finset.univ.filter fun i => g i = i).card : ℤ) - 1)

/-- C15-43 (characters): on the class representatives e, (12), (12)(34), (123), (1234) the character of
Λ(ℂ⁴) ⊗ V_std is 48, 0, 0, 0, 0, the character of ℂ[S₄] ⊗ ℂ² (dimension 48). -/
theorem s4_characters :
    chi ![0, 1, 2, 3] = 48 ∧ chi ![1, 0, 2, 3] = 0 ∧ chi ![1, 0, 3, 2] = 0 ∧ chi ![1, 2, 0, 3] = 0 ∧
      chi ![1, 2, 3, 0] = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [chi, pmat, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Finset.filter, Fin.succAbove] <;> decide


end Entropic.Pass2.Kinetic
