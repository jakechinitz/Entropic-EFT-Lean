import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-! Common finite operator identities. An actual isometry/positive covariance is
required. Neither dimensional counting nor an idempotent oblique projection is
a substitute. Analytic functional calculus and continuum limits are not claimed. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Entropic.IsometricReduction
variable {n m k : Type*} [Fintype n] [Fintype m] [Fintype k]
variable [DecidableEq n] [DecidableEq m] [DecidableEq k]

def lift (J : Matrix m n ℂ) (A : Matrix n n ℂ) := J * A * Jᴴ

theorem code_projector (J : Matrix m n ℂ) (hJ : Jᴴ * J = 1) :
    (J * Jᴴ) * (J * Jᴴ) = J * Jᴴ := by
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ J Jᴴ, hJ, Matrix.one_mul]

theorem lift_product (J : Matrix m n ℂ) (hJ : Jᴴ * J = 1)
    (A B : Matrix n n ℂ) : lift J A * lift J B = lift J (A * B) := by
  unfold lift
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ J, hJ, Matrix.one_mul]

theorem lift_compress (J : Matrix m n ℂ) (hJ : Jᴴ * J = 1)
    (A : Matrix n n ℂ) : Jᴴ * lift J A * J = A := by
  unfold lift
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ J, hJ, Matrix.one_mul,
    ← Matrix.mul_assoc A Jᴴ J, Matrix.mul_one]

theorem lift_positive (J : Matrix m n ℂ) {A : Matrix n n ℂ}
    (hA : A.PosSemidef) : (lift J A).PosSemidef :=
  hA.mul_mul_conjTranspose_same J

theorem lift_trace (J : Matrix m n ℂ) (hJ : Jᴴ * J = 1)
    (A : Matrix n n ℂ) : Matrix.trace (lift J A) = Matrix.trace A := by
  unfold lift
  rw [Matrix.trace_mul_cycle, hJ, Matrix.one_mul]

/-- Orthogonal projectors provide a normalized two-output sharp channel. -/
theorem sharp_complement (P : Matrix n n ℂ) (hP : P * P = P)
    (hHerm : Pᴴ = P) : Pᴴ * P + (1 - P)ᴴ * (1 - P) = 1 := by
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hHerm,
    sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, hP]
  abel

/-- Exact source/evolution intertwining is stronger than compression alone. -/
theorem intertwining_compress (J : Matrix m n ℂ) (hJ : Jᴴ * J = 1)
    (H : Matrix m m ℂ) (A : Matrix n n ℂ) (h : H * J = J * A) :
    Jᴴ * H * J = A := by
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, hJ, Matrix.one_mul]

theorem intertwining_pow (J : Matrix m n ℂ) (H : Matrix m m ℂ)
    (A : Matrix n n ℂ) (h : H * J = J * A) (p : ℕ) :
    H ^ p * J = J * A ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih,
      Matrix.mul_assoc, ← pow_succ]

theorem isometries_compose (J : Matrix m n ℂ) (K : Matrix k m ℂ)
    (hJ : Jᴴ * J = 1) (hK : Kᴴ * K = 1) :
    (K * J)ᴴ * (K * J) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Kᴴ K,
    hK, Matrix.one_mul, hJ]

def response (C : Matrix m n ℂ) (A : Matrix n n ℂ) := C * A * Cᴴ

theorem response_positive (C : Matrix m n ℂ) {N : Matrix n n ℂ}
    (hN : N.PosSemidef) : (response C N).PosSemidef :=
  hN.mul_mul_conjTranspose_same C

/-- Same scalar FDT multiplier survives source-adjoint reduction. This theorem
does not assert that any proposed fine spectra actually satisfy quantum KMS. -/
theorem response_fdt (C : Matrix m n ℂ) (N D : Matrix n n ℂ) (a : ℂ)
    (h : N = a • D) : response C N = a • response C D := by
  simp [response, h, Matrix.mul_smul, Matrix.smul_mul]

theorem response_compose (C : Matrix m n ℂ) (B : Matrix k m ℂ)
    (A : Matrix n n ℂ) : response B (response C A) = response (B * C) A := by
  simp [response, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end Entropic.IsometricReduction
