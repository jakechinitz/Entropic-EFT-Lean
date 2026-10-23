import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Chunk 14 sweep: C07-55, Hermite product basis (Gaussian moments) and the SO(3) splitting
ℝ³ ⊗ ℝ³ = 1 ⊕ 3 ⊕ 5. -/

noncomputable section
namespace Entropic.Sweep.Gauss
open MeasureTheory ProbabilityTheory Matrix

abbrev γ1 : Measure ℝ := gaussianReal 0 1
abbrev γ3 : Measure (Fin 3 → ℝ) := Measure.pi (fun _ => γ1)

theorem second_moment_1d : ∫ x, x ^ 2 ∂γ1 = 1 := by
  have h := variance_eq_sub (μ := γ1) (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by norm_num))
  have h2 : ∫ x, id x ∂γ1 = 0 := integral_id_gaussianReal
  rw [variance_id_gaussianReal, h2] at h
  simp only [Pi.pow_apply, id, NNReal.coe_one] at h
  linarith

theorem first_moment_1d : ∫ x, x ∂γ1 = 0 := integral_id_gaussianReal

/-- E[ξ_a ξ_c] = δ_ac for a standard Gaussian vector in ℝ³. -/
theorem cov3 (a c : Fin 3) : ∫ x, x a * x c ∂γ3 = if a = c then 1 else 0 := by
  set f : Fin 3 → ℝ → ℝ := fun i t => (if i = a then t else 1) * (if i = c then t else 1)
  have hprod : ∀ x : Fin 3 → ℝ, x a * x c = ∏ i, f i (x i) := by
    intro x; simp only [f, Finset.prod_mul_distrib]
    rw [Finset.prod_ite_eq' Finset.univ a, Finset.prod_ite_eq' Finset.univ c]; simp
  simp_rw [hprod]
  rw [integral_fintype_prod_eq_prod (μ := fun _ => γ1) f]
  by_cases hac : a = c
  · subst hac
    rw [if_pos rfl, Finset.prod_eq_single a]
    · simp only [f, if_true]; rw [← second_moment_1d]; congr 1; ext t; ring
    · intro i _ hi; simp [f, hi]
    · simp
  · rw [if_neg hac, Finset.prod_eq_zero (Finset.mem_univ a)]
    simp only [f, if_true, if_neg hac, mul_one]; exact first_moment_1d

/-- C07-55: for independent standard Gaussian vectors ξ^P, ξ^H ∈ ℝ³,
E[ξ^P_a ξ^H_b ξ^P_c ξ^H_d] = δ_ac δ_bd (Gram matrix I₃ ⊗ I₃ = I₉). -/
theorem hermite_gram (a b c d : Fin 3) :
    ∫ z, z.1 a * z.2 b * z.1 c * z.2 d ∂(γ3.prod γ3) = (if a = c then 1 else 0) * (if b = d then 1 else 0) := by
  have e : (fun z : (Fin 3 → ℝ) × (Fin 3 → ℝ) => z.1 a * z.2 b * z.1 c * z.2 d) =
      fun z => (z.1 a * z.1 c) * (z.2 b * z.2 d) := by ext z; ring
  rw [e, integral_prod_mul (fun x : Fin 3 → ℝ => x a * x c) (fun y : Fin 3 → ℝ => y b * y d), cov3, cov3]

/-! ### SO(3) splitting of 3 × 3 matrices -/

def Tpart (X : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (X.trace / 3) • 1
def Apart (X : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (1/2 : ℝ) • (X - Xᵀ)
def Spart (X : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (1/2 : ℝ) • (X + Xᵀ) - Tpart X

/-- C07-55 (decomposition): X = (tr X/3)I + antisymmetric part + symmetric traceless part (dimensions
1 + 3 + 5 = 9); the parts are of the stated types and each commutes with X ↦ R X Rᵀ for orthogonal R. -/
theorem so3_split (X R : Matrix (Fin 3) (Fin 3) ℝ) (hR : Rᵀ * R = 1) :
    X = Tpart X + Apart X + Spart X ∧ (Apart X)ᵀ = -Apart X ∧ (Spart X)ᵀ = Spart X ∧ (Spart X).trace = 0 ∧
      Tpart (R * X * Rᵀ) = R * Tpart X * Rᵀ ∧ Apart (R * X * Rᵀ) = R * Apart X * Rᵀ ∧
      Spart (R * X * Rᵀ) = R * Spart X * Rᵀ := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  have htr : (R * X * Rᵀ).trace = X.trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hR, Matrix.one_mul]
  have hT : Tpart (R * X * Rᵀ) = R * Tpart X * Rᵀ := by
    simp only [Tpart, htr, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hR']
  have hA : Apart (R * X * Rᵀ) = R * Apart X * Rᵀ := by
    simp only [Apart, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_, ?_, hT, hA, ?_⟩
  · simp only [Tpart, Apart, Spart]; module
  · simp only [Apart, Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_transpose]; module
  · simp only [Spart, Tpart, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_add,
      Matrix.transpose_transpose, Matrix.transpose_one]; congr 2; abel
  · simp only [Spart, Tpart, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_transpose,
      Matrix.trace_one, Fintype.card_fin, smul_eq_mul]; ring
  · simp only [Spart]; rw [hT]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

end Entropic.Sweep.Gauss
