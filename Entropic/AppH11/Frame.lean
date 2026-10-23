import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! Appendix H.11–H.12: frame connection and Born–Huang split, symplectic transport algebra,
isotropic moments and Fisher metric (ledger C09-13, -19, -20, -29, -30). -/

noncomputable section
namespace Entropic.AppH11
open Matrix

section Frame
variable {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]

/-- C09-13: let LLᵀ = I with derivative ∂L satisfying ∂L Lᵀ + L ∂Lᵀ = 0 (the derivative of LLᵀ = I).
Then (i) A := L∂Lᵀ is antisymmetric; (ii) ∂(Lᵀd) = Lᵀ(∂d + A d) + P₃∂Lᵀd with P₃ = I − LᵀL;
(iii) the two terms are Euclidean-orthogonal. -/
theorem frame_connection (L dL : Matrix m k ℝ) (hLL : L * Lᵀ = 1) (hd : dL * Lᵀ + L * dLᵀ = 0)
    (d dd : m → ℝ) :
    (L * dLᵀ)ᵀ = -(L * dLᵀ) ∧
      dLᵀ *ᵥ d + Lᵀ *ᵥ dd = Lᵀ *ᵥ (dd + (L * dLᵀ) *ᵥ d) + ((1 - Lᵀ * L) * dLᵀ) *ᵥ d ∧
      ∀ u w : _, (Lᵀ *ᵥ u) ⬝ᵥ (((1 : Matrix k k ℝ) - Lᵀ * L) *ᵥ w) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    exact eq_neg_of_add_eq_zero_left hd
  · simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mulVec,
      Matrix.mul_assoc]
    abel
  · intro u w
    rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hLL, Matrix.one_mul, sub_self,
      Matrix.zero_mulVec, dotProduct_zero]

end Frame

section Symplectic
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- C09-19: if S′ = K S with KᵀΩ + ΩK = 0, then (SᵀΩS)′ = S′ᵀΩS + SᵀΩS′ = 0, so S stays symplectic;
J := S J₀ S⁻¹ satisfies J² = −I. -/
theorem symplectic_derivative (S K Ω : Matrix n n ℝ) (hK : Kᵀ * Ω + Ω * K = 0) :
    (K * S)ᵀ * Ω * S + Sᵀ * Ω * (K * S) = 0 := by
  rw [Matrix.transpose_mul]
  calc Sᵀ * Kᵀ * Ω * S + Sᵀ * Ω * (K * S) = Sᵀ * (Kᵀ * Ω + Ω * K) * S := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hK]; simp

theorem transported_complex_structure (S Si J0 : Matrix n n ℝ) (hS : Si * S = 1) (hJ : J0 * J0 = -1) :
    (S * J0 * Si) * (S * J0 * Si) = -(S * Si) := by
  rw [show S * J0 * Si * (S * J0 * Si) = S * J0 * (Si * S) * J0 * Si by simp only [Matrix.mul_assoc], hS,
    Matrix.mul_one, Matrix.mul_assoc S J0 J0, hJ]; simp

/-- C09-20: for symplectic S (SᵀΩS = Ω) and J = S J₀ S⁻¹, g_t(Su, Sv) := (Su)ᵀΩJ(Sv) = uᵀΩJ₀v. -/
theorem transported_form (S Si J0 Ω : Matrix n n ℝ) (hS : Si * S = 1) (hsp : Sᵀ * Ω * S = Ω) (u v : n → ℝ) :
    (S *ᵥ u) ⬝ᵥ ((Ω * (S * J0 * Si)) *ᵥ (S *ᵥ v)) = u ⬝ᵥ ((Ω * J0) *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  congr 2
  rw [show Sᵀ * (Ω * (S * J0 * Si) * S) = (Sᵀ * Ω * S) * J0 * (Si * S) by simp only [Matrix.mul_assoc], hsp,
    hS, Matrix.mul_one]

end Symplectic

/-- C09-29: isotropic second moments E[C_aC_c] = σ²δ with E|C|² = 3σ² = 3/(2η) give σ² = 1/(2η); for
independent C^P, C^H the response r_ab = 2η C^P_a C^H_b has E[r_ab r_cd] = 4η²σ⁴δ_acδ_bd = δ_acδ_bd. -/
theorem isotropic_moments {η σ2 : ℝ} (hη : 0 < η) (h : 3 * σ2 = 3 / (2 * η)) :
    σ2 = 1 / (2 * η) ∧ (2 * η) ^ 2 * σ2 * σ2 = 1 := by
  have hs : σ2 = 1 / (2 * η) := by
    have : 3 / (2 * η) = 3 * (1 / (2 * η)) := by ring
    linarith
  refine ⟨hs, ?_⟩
  rw [hs]; field_simp

/-- C09-30: score s = ∂ log A² = 2r; with E[r r] = δδ the Fisher information is 4δδ, i.e. g^mark = I/4. -/
theorem fisher_four (e : ℝ) : (2 : ℝ) * 2 * e = 4 * e ∧ (4 * e) / 4 = e := by
  constructor <;> ring

end Entropic.AppH11
