import Entropic.AppH10.Legendre
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Appendix H.10: Gaussian elimination with sources and the Gaussian-KL identification
(ledger C08-05, -06, -10). -/

noncomputable section
namespace Entropic.AppH10
open Matrix Real MeasureTheory

variable {n m : ℕ}

/-- The source action S(x,y) = ½xᵀAx + xᵀBy + ½yᵀDy − j_xᵀx − j_yᵀy. -/
def srcAction (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (D : Matrix (Fin m) (Fin m) ℝ)
    (jx : Fin n → ℝ) (jy : Fin m → ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ) : ℝ :=
  (1/2) * (x ⬝ᵥ (A *ᵥ x)) + x ⬝ᵥ (B *ᵥ y) + (1/2) * (y ⬝ᵥ (D *ᵥ y)) - jx ⬝ᵥ x - jy ⬝ᵥ y

/-- The stationary point y* = D⁻¹(j_y − Bᵀx). -/
def ystar (B : Matrix (Fin n) (Fin m) ℝ) (D : Matrix (Fin m) (Fin m) ℝ) (jy : Fin m → ℝ) (x : Fin n → ℝ) :
    Fin m → ℝ := D⁻¹ *ᵥ (jy - Bᵀ *ᵥ x)

/-- C08-05 (i): S(x, y) = S(x, y*) + ½(y − y*)ᵀD(y − y*) for symmetric invertible D; hence for
D > 0 the minimum over y is S(x, y*), attained only at y*. -/
theorem complete_square_matrix (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (D : Matrix (Fin m) (Fin m) ℝ) (hDs : Dᵀ = D) (hD : IsUnit D.det) (jx : Fin n → ℝ) (jy : Fin m → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) :
    srcAction A B D jx jy x y = srcAction A B D jx jy x (ystar B D jy x) +
      (1/2) * ((y - ystar B D jy x) ⬝ᵥ (D *ᵥ (y - ystar B D jy x))) := by
  set ys := ystar B D jy x
  have hDy : D *ᵥ ys = jy - Bᵀ *ᵥ x := by
    simp only [ys, ystar, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hD, Matrix.one_mulVec]
  have hsym : ∀ u v : Fin m → ℝ, u ⬝ᵥ (D *ᵥ v) = v ⬝ᵥ (D *ᵥ u) := by
    intro u v
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hDs, dotProduct_comm]
  have hB : ∀ v : Fin m → ℝ, x ⬝ᵥ (B *ᵥ v) = v ⬝ᵥ (Bᵀ *ᵥ x) := by
    intro v; rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  have r1 : y ⬝ᵥ (D *ᵥ ys) = y ⬝ᵥ jy - x ⬝ᵥ (B *ᵥ y) := by
    rw [hDy, dotProduct_sub, hB]
  have r2 : ys ⬝ᵥ (D *ᵥ ys) = ys ⬝ᵥ jy - x ⬝ᵥ (B *ᵥ ys) := by
    rw [hDy, dotProduct_sub, hB]
  have r3 : ys ⬝ᵥ (D *ᵥ y) = y ⬝ᵥ (D *ᵥ ys) := hsym ys y
  unfold srcAction
  simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
  rw [dotProduct_comm jy y, dotProduct_comm jy ys]
  linear_combination r1 - r2 + (1/2 : ℝ) * r3

theorem complete_square_min (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (D : Matrix (Fin m) (Fin m) ℝ) (hDpd : D.PosDef) (jx : Fin n → ℝ) (jy : Fin m → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) :
    srcAction A B D jx jy x (ystar B D jy x) ≤ srcAction A B D jx jy x y ∧
      (srcAction A B D jx jy x y = srcAction A B D jx jy x (ystar B D jy x) → y = ystar B D jy x) := by
  have hDs : Dᵀ = D := by
    have := hDpd.1; rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hD : IsUnit D.det := (det_pos_of_posDef hDpd).ne'.isUnit
  have h := complete_square_matrix A B D hDs hD jx jy x y
  have hnn : 0 ≤ (y - ystar B D jy x) ⬝ᵥ (D *ᵥ (y - ystar B D jy x)) := by
    have := hDpd.posSemidef.dotProduct_mulVec_nonneg (y - ystar B D jy x)
    simpa using this
  refine ⟨by linarith, fun heq => ?_⟩
  have h0 : (y - ystar B D jy x) ⬝ᵥ (D *ᵥ (y - ystar B D jy x)) = 0 := by linarith
  by_contra hne
  have hpos := hDpd.dotProduct_mulVec_pos (x := y - ystar B D jy x) (sub_ne_zero.mpr hne)
  rw [star_trivial] at hpos; linarith

/-- C08-05 (ii): −ln ∫ e^{−S(x,y)} dy = S(x, y*) + ½ ln det D − (m/2) ln 2π for D > 0. -/
theorem eliminate_integral (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (D : Matrix (Fin m) (Fin m) ℝ) (hDpd : D.PosDef) (jx : Fin n → ℝ) (jy : Fin m → ℝ) (x : Fin n → ℝ) :
    -Real.log (∫ y, Real.exp (-srcAction A B D jx jy x y)) =
      srcAction A B D jx jy x (ystar B D jy x) + (1/2) * Real.log D.det - (m / 2 : ℝ) * Real.log (2 * π) := by
  have hDs : Dᵀ = D := by
    have := hDpd.1; rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hD : IsUnit D.det := (det_pos_of_posDef hDpd).ne'.isUnit
  have hfun : (fun y => Real.exp (-srcAction A B D jx jy x y)) =
      fun y => Real.exp (-srcAction A B D jx jy x (ystar B D jy x)) * Real.exp (-(1/2) * ((y - ystar B D jy x) ⬝ᵥ (D *ᵥ (y - ystar B D jy x)))) := by
    funext y; rw [complete_square_matrix A B D hDs hD jx jy x y, ← Real.exp_add]; ring_nf
  rw [hfun, integral_const_mul,
    integral_sub_right_eq_self (fun y => Real.exp (-(1/2) * (y ⬝ᵥ (D *ᵥ y)))) (ystar B D jy x),
    gaussian_integral hDpd]
  have hdet := det_pos_of_posDef hDpd
  have hp : (0:ℝ) < (2 * π) ^ m := by positivity
  rw [Real.log_mul (Real.exp_pos _).ne' (Real.sqrt_pos.mpr (div_pos hp hdet)).ne', Real.log_exp,
    Real.log_sqrt (div_pos hp hdet).le, Real.log_div hp.ne' hdet.ne', Real.log_pow]
  ring

/-- C08-06 (determinant part): det D = det D₁₁ · det(D/D₁₁) for invertible D₁₁, so the ½ ln det
terms of successive elimination add up to the joint one. -/
theorem successive_det {p q : ℕ} (D11 : Matrix (Fin p) (Fin p) ℝ) (D12 : Matrix (Fin p) (Fin q) ℝ)
    (D21 : Matrix (Fin q) (Fin p) ℝ) (D22 : Matrix (Fin q) (Fin q) ℝ) (h : IsUnit D11.det) :
    (Matrix.fromBlocks D11 D12 D21 D22).det = D11.det * (D22 - D21 * D11⁻¹ * D12).det := by
  haveI := D11.invertibleOfIsUnitDet h
  rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]

/-- C08-10 (algebraic identification): with G = K₀^{1/2}K⁻¹K₀^{1/2} (C = K⁻¹, C₀ = K₀⁻¹),
Tr G = Tr(C₀⁻¹C) and det G = det C / det C₀, so Γ_rel[G] = ½[Tr(C₀⁻¹C) − N − ln(det C/det C₀)],
the closed form of D_KL(N(0,C) ‖ N(0,C₀)). -/
theorem gammaRel_kl_form {N : ℕ} {K0 K : Matrix (Fin N) (Fin N) ℝ} (h0 : K0.PosDef) (hK : K.PosDef) :
    gammaRel (psqrt h0 * K⁻¹ * psqrt h0) =
      (1/2) * ((K0 * K⁻¹).trace - N - Real.log (K⁻¹.det / K0⁻¹.det)) := by
  unfold gammaRel
  have hk := det_pos_of_posDef hK
  have h0d := det_pos_of_posDef h0
  have htr : (psqrt h0 * K⁻¹ * psqrt h0).trace = (K0 * K⁻¹).trace := by
    rw [Matrix.trace_mul_cycle, psqrt_mul_self]
  have hdet : (psqrt h0 * K⁻¹ * psqrt h0).det = K⁻¹.det / K0⁻¹.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Matrix.det_nonsing_inv, det_psqrt]
    try simp only [Ring.inverse_eq_inv']
    have : Real.sqrt K0.det * Real.sqrt K0.det = K0.det := Real.mul_self_sqrt h0d.le
    field_simp
    nlinarith [this]
  rw [htr, hdet]

end Entropic.AppH10
