import Entropic.AppQ.Weights
import Entropic.Sweep.Gaussian

/-! Second pass, chunk 15: C09-09 (invariant real forms of V₀, V₁, V₂) and C14-75 (a) (weight count for
V_{3/2}^{⊗4}). -/

namespace Entropic.Pass2.RealForms
open Matrix

/-- Real generators of so(3) (rotations about the three axes). -/
def A1 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 0, -1; 0, 1, 0]
def A2 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 0, 0, 0; -1, 0, 0]
def A3 : Matrix (Fin 3) (Fin 3) ℝ := !![0, -1, 0; 1, 0, 0; 0, 0, 0]

def ad (A X : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ := A * X - X * A

/-- The adjoint Casimir on 3 × 3 real matrices: Σ_a [A_a, [A_a, X]] = −6X + 2(X − Xᵀ) + 2 tr(X) I. -/
theorem ad_casimir (X : Matrix (Fin 3) (Fin 3) ℝ) :
    ad A1 (ad A1 X) + ad A2 (ad A2 X) + ad A3 (ad A3 X) = (-6 : ℝ) • X + (2 : ℝ) • (X - Xᵀ) + (2 * X.trace) • 1 := by
  ext i j
  simp only [ad, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three, Matrix.smul_apply,
    Matrix.transpose_apply, Matrix.trace, Matrix.diag, Matrix.one_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [A1, A2, A3] <;> ring

/-- C09-09: ℝ³ ⊗ ℝ³ = M₃(ℝ) splits into the SO(3)-invariant real subspaces of scalars, antisymmetric and
symmetric traceless matrices (`Sweep.Gauss.so3_split`), on which the Casimir −Σ ad(A_a)² takes the values
J(J + 1) = 0, 2, 6: they are real forms of V₀, V₁, V₂, and together give Q_R ≅ ℝ⁹. -/
theorem real_forms (X : Matrix (Fin 3) (Fin 3) ℝ) :
    (∀ c : ℝ, ad A1 (ad A1 (c • 1)) + ad A2 (ad A2 (c • 1)) + ad A3 (ad A3 (c • 1)) = 0) ∧
      (Xᵀ = -X → ad A1 (ad A1 X) + ad A2 (ad A2 X) + ad A3 (ad A3 X) = (-2 : ℝ) • X) ∧
      (Xᵀ = X → X.trace = 0 → ad A1 (ad A1 X) + ad A2 (ad A2 X) + ad A3 (ad A3 X) = (-6 : ℝ) • X) := by
  refine ⟨fun c => ?_, fun h => ?_, fun h ht => ?_⟩
  · rw [ad_casimir]; simp [Matrix.trace_smul, Matrix.trace_one]; module
  · rw [ad_casimir, h]
    have : X.trace = 0 := by
      have := congrArg Matrix.trace h; rw [Matrix.trace_transpose, Matrix.trace_neg] at this; linarith
    rw [this]; simp; module
  · rw [ad_casimir, h, ht]; simp

/-- C14-75 (a): in V_{3/2}^{⊗4} the total weight 0 occurs 44 times and weight 1 occurs 40 times, so the
invariant space has dimension c₀ − c₁ = 4 (character formula). -/
theorem four_slot_weights :
    let r := List.replicate 4 1
    let p := Entropic.AppQ.W.pmul (Entropic.AppQ.W.pmul (Entropic.AppQ.W.pmul r r) r) r
    p.getD 6 0 = 44 ∧ p.getD 7 0 = 40 := by decide +kernel

end Entropic.Pass2.RealForms
