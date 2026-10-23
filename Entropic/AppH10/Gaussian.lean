import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic

/-! Appendix H.10: finite-regulator Gaussian determinant theorem (ledger C08-02, -03, -04, -12). -/

noncomputable section
namespace Entropic.AppH10
open Matrix MeasureTheory Real

variable {N : ℕ}

/-- The orthogonal eigenvector matrix of a symmetric real matrix. -/
abbrev evec {K : Matrix (Fin N) (Fin N) ℝ} (hK : K.IsHermitian) : Matrix (Fin N) (Fin N) ℝ :=
  (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ)

theorem evec_transpose_mul {K : Matrix (Fin N) (Fin N) ℝ} (hK : K.IsHermitian) :
    (evec hK)ᵀ * evec hK = 1 := by
  have := Unitary.coe_star_mul_self hK.eigenvectorUnitary
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this

theorem evec_mul_transpose {K : Matrix (Fin N) (Fin N) ℝ} (hK : K.IsHermitian) :
    evec hK * (evec hK)ᵀ = 1 := by
  have := Unitary.coe_mul_star_self hK.eigenvectorUnitary
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this

/-- Vᵀ K V is diagonal with the eigenvalues. -/
theorem evec_diag {K : Matrix (Fin N) (Fin N) ℝ} (hK : K.IsHermitian) :
    (evec hK)ᵀ * K * evec hK = diagonal hK.eigenvalues := by
  have hs := hK.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  have hd : (diagonal (RCLike.ofReal ∘ hK.eigenvalues) : Matrix (Fin N) (Fin N) ℝ) =
      diagonal hK.eigenvalues := by
    congr 1
  have hs' : K = evec hK * diagonal hK.eigenvalues * (evec hK)ᵀ := by
    rw [hd] at hs; simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hs
  have gen : ∀ V D : Matrix (Fin N) (Fin N) ℝ, Vᵀ * V = 1 → K = V * D * Vᵀ → Vᵀ * K * V = D := by
    intro V D h1 h2
    rw [h2, show Vᵀ * (V * D * Vᵀ) * V = (Vᵀ * V) * D * (Vᵀ * V) by simp only [Matrix.mul_assoc], h1]
    simp
  exact gen _ _ (evec_transpose_mul hK) hs'

theorem abs_det_evec {K : Matrix (Fin N) (Fin N) ℝ} (hK : K.IsHermitian) : |(evec hK).det| = 1 := by
  have h := congrArg Matrix.det (evec_transpose_mul hK)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  have h2 : |(evec hK).det| ^ 2 = 1 := by rw [sq_abs]; nlinarith
  have h0 : 0 ≤ |(evec hK).det| := abs_nonneg _
  nlinarith [sq_nonneg (|(evec hK).det| - 1)]


/-- In the eigenbasis the quadratic form is Σ λᵢ yᵢ². -/
theorem quad_rotate {K : Matrix (Fin N) (Fin N) ℝ} (hK : K.IsHermitian) (y : Fin N → ℝ) :
    (evec hK *ᵥ y) ⬝ᵥ (K *ᵥ (evec hK *ᵥ y)) = ∑ i, hK.eigenvalues i * y i ^ 2 := by
  conv_lhs => arg 1; rw [← vecMul_transpose]
  rw [← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, evec_diag]
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- C08-04: ∫_{ℝᴺ} exp(−½ xᵀKx) dx = √((2π)ᴺ / det K) = (2π)^{N/2}(det K)^{−1/2} for K > 0. -/
theorem gaussian_integral {K : Matrix (Fin N) (Fin N) ℝ} (hK : K.PosDef) :
    ∫ x : Fin N → ℝ, Real.exp (-(1/2) * (x ⬝ᵥ (K *ᵥ x))) = Real.sqrt ((2 * π) ^ N / K.det) := by
  set V := evec hK.1 with hVdef
  set f := Matrix.toLin' V
  have hdet : LinearMap.det f ≠ 0 := by
    rw [LinearMap.det_toLin']; intro h0; have := abs_det_evec hK.1; rw [← hVdef, h0] at this; simp at this
  have hmap : Measure.map f volume = (volume : Measure (Fin N → ℝ)) := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := volume) hdet, LinearMap.det_toLin', abs_inv, hVdef,
      abs_det_evec]; simp
  have hfc : Continuous f := LinearMap.continuous_of_finiteDimensional f
  have hg : Continuous (fun x : Fin N → ℝ => Real.exp (-(1/2) * (x ⬝ᵥ (K *ᵥ x)))) := by fun_prop
  rw [← hmap, integral_map hfc.aemeasurable hg.aestronglyMeasurable]
  have hpt : ∀ y : Fin N → ℝ, Real.exp (-(1/2) * (f y ⬝ᵥ (K *ᵥ f y))) =
      ∏ i, Real.exp (-(hK.1.eigenvalues i / 2) * y i ^ 2) := by
    intro y
    rw [show f y = V *ᵥ y from Matrix.toLin'_apply V y, hVdef, quad_rotate, Finset.mul_sum,
      Real.exp_sum]
    exact Finset.prod_congr rfl (fun i _ => by ring_nf)
  simp_rw [hpt]
  rw [integral_fintype_prod_volume_eq_prod (fun i (t : ℝ) => Real.exp (-(hK.1.eigenvalues i / 2) * t ^ 2))]
  simp_rw [integral_gaussian]
  rw [← Real.sqrt_prod _ (fun i _ => by have := hK.eigenvalues_pos i; positivity)]
  congr 1
  rw [hK.1.det_eq_prod_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id]
  have hne : ∀ i, hK.1.eigenvalues i ≠ 0 := fun i => (hK.eigenvalues_pos i).ne'
  rw [Finset.prod_congr rfl (fun i _ => show π / (hK.1.eigenvalues i / 2) = (2 * π) / hK.1.eigenvalues i by
    field_simp [hne i]), Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]


/-! ### Symmetric square root, whitening, determinant ratio (C08-01, -02, -03, -12) -/

theorem evec_spectral {K : Matrix (Fin N) (Fin N) ℝ} (hK : K.IsHermitian) :
    K = evec hK * diagonal hK.eigenvalues * (evec hK)ᵀ := by
  have h := evec_diag hK
  calc K = (evec hK * (evec hK)ᵀ) * K * (evec hK * (evec hK)ᵀ) := by rw [evec_mul_transpose]; simp
    _ = evec hK * ((evec hK)ᵀ * K * evec hK) * (evec hK)ᵀ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h]

/-- The symmetric positive square root V diag(√λ) Vᵀ of a positive definite matrix. -/
def psqrt {K : Matrix (Fin N) (Fin N) ℝ} (hK : K.PosDef) : Matrix (Fin N) (Fin N) ℝ :=
  evec hK.1 * diagonal (fun i => Real.sqrt (hK.1.eigenvalues i)) * (evec hK.1)ᵀ

theorem psqrt_mul_self {K : Matrix (Fin N) (Fin N) ℝ} (hK : K.PosDef) : psqrt hK * psqrt hK = K := by
  unfold psqrt
  rw [show evec hK.1 * diagonal (fun i => √(hK.1.eigenvalues i)) * (evec hK.1)ᵀ *
      (evec hK.1 * diagonal (fun i => √(hK.1.eigenvalues i)) * (evec hK.1)ᵀ) =
      evec hK.1 * diagonal (fun i => √(hK.1.eigenvalues i)) * ((evec hK.1)ᵀ * evec hK.1) *
        diagonal (fun i => √(hK.1.eigenvalues i)) * (evec hK.1)ᵀ by simp only [Matrix.mul_assoc],
    evec_transpose_mul, Matrix.mul_one, Matrix.mul_assoc (evec hK.1), diagonal_mul_diagonal]
  conv_rhs => rw [evec_spectral hK.1]
  congr 3; funext i; exact Real.mul_self_sqrt (hK.eigenvalues_pos i).le

theorem psqrt_transpose {K : Matrix (Fin N) (Fin N) ℝ} (hK : K.PosDef) : (psqrt hK)ᵀ = psqrt hK := by
  unfold psqrt; simp [Matrix.transpose_mul, Matrix.mul_assoc]

theorem det_psqrt {K : Matrix (Fin N) (Fin N) ℝ} (hK : K.PosDef) :
    (psqrt hK).det = Real.sqrt K.det := by
  have h1 : (psqrt hK).det ^ 2 = K.det := by rw [sq, ← Matrix.det_mul, psqrt_mul_self]
  have h2 : 0 ≤ (psqrt hK).det := by
    unfold psqrt
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
    have : (evec hK.1).det * (evec hK.1).det = 1 := by
      have := congrArg Matrix.det (evec_transpose_mul hK.1)
      rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    rw [mul_right_comm, this, one_mul]
    exact Finset.prod_nonneg (fun i _ => Real.sqrt_nonneg _)
  rw [← h1, Real.sqrt_sq h2]

theorem det_pos_of_posDef {K : Matrix (Fin N) (Fin N) ℝ} (hK : K.PosDef) : 0 < K.det := by
  rw [hK.1.det_eq_prod_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id]
  exact Finset.prod_pos (fun i _ => hK.eigenvalues_pos i)

theorem psqrt_isUnit {K : Matrix (Fin N) (Fin N) ℝ} (hK : K.PosDef) : IsUnit (psqrt hK).det := by
  rw [det_psqrt]; exact (Real.sqrt_pos.mpr (det_pos_of_posDef hK)).ne'.isUnit

/-- C08-01: Θ := K₀^{−1/2} K K₀^{−1/2} is positive definite; G := Θ⁻¹ = K₀^{1/2} K⁻¹ K₀^{1/2}. -/
def whiten {K0 K : Matrix (Fin N) (Fin N) ℝ} (h0 : K0.PosDef) (_ : K.PosDef) :
    Matrix (Fin N) (Fin N) ℝ := (psqrt h0)⁻¹ * K * (psqrt h0)⁻¹

theorem whiten_posDef {K0 K : Matrix (Fin N) (Fin N) ℝ} (h0 : K0.PosDef) (hK : K.PosDef) :
    (whiten h0 hK).PosDef := by
  unfold whiten
  have hS : ((psqrt h0)⁻¹)ᴴ = (psqrt h0)⁻¹ := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_nonsing_inv, psqrt_transpose]
  have := hK.conjTranspose_mul_mul_same (B := (psqrt h0)⁻¹)
    (Matrix.mulVec_injective_of_isUnit (((psqrt h0)⁻¹).isUnit_iff_isUnit_det.mpr
      (Matrix.isUnit_nonsing_inv_det _ (psqrt_isUnit h0))))
  rwa [hS] at this

theorem whiten_inv {K0 K : Matrix (Fin N) (Fin N) ℝ} (h0 : K0.PosDef) (hK : K.PosDef) :
    (whiten h0 hK)⁻¹ = psqrt h0 * K⁻¹ * psqrt h0 := by
  have hu := psqrt_isUnit h0
  have hK' : IsUnit K.det := (det_pos_of_posDef hK).ne'.isUnit
  unfold whiten
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mul_assoc]

theorem det_whiten {K0 K : Matrix (Fin N) (Fin N) ℝ} (h0 : K0.PosDef) (hK : K.PosDef) :
    (whiten h0 hK).det = K.det / K0.det := by
  unfold whiten
  have h0d := det_pos_of_posDef h0
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, det_psqrt, Ring.inverse_eq_inv']
  have : Real.sqrt K0.det * Real.sqrt K0.det = K0.det := Real.mul_self_sqrt h0d.le
  have hs : Real.sqrt K0.det ≠ 0 := (Real.sqrt_pos.mpr h0d).ne'
  have e : (Real.sqrt K0.det)⁻¹ * K.det * (Real.sqrt K0.det)⁻¹ =
      K.det / (Real.sqrt K0.det * Real.sqrt K0.det) := by field_simp
  rw [e, this]

/-- C08-02: Ẑ_G := ∫e^{−½xᵀKx} / ∫e^{−½xᵀK₀x} = (det Θ)^{−1/2}, no commutation required. -/
theorem determinant_theorem {K0 K : Matrix (Fin N) (Fin N) ℝ} (h0 : K0.PosDef) (hK : K.PosDef) :
    (∫ x : Fin N → ℝ, Real.exp (-(1/2) * (x ⬝ᵥ (K *ᵥ x)))) /
      (∫ x : Fin N → ℝ, Real.exp (-(1/2) * (x ⬝ᵥ (K0 *ᵥ x)))) =
      1 / Real.sqrt (whiten h0 hK).det := by
  rw [gaussian_integral hK, gaussian_integral h0, det_whiten]
  have hk := det_pos_of_posDef hK
  have h0d := det_pos_of_posDef h0
  have hp : 0 < (2 * π) ^ N := by positivity
  rw [Real.sqrt_div' _ hk.le, Real.sqrt_div' _ h0d.le, Real.sqrt_div' _ h0d.le]
  have := Real.sqrt_pos.mpr hp
  have := Real.sqrt_pos.mpr hk
  have := Real.sqrt_pos.mpr h0d
  field_simp

/-- Σᵢ ln θᵢ = ln det Θ (the trace-log of a positive definite matrix). -/
theorem sum_log_eigenvalues {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef) :
    ∑ i, Real.log (hA.1.eigenvalues i) = Real.log A.det := by
  rw [hA.1.det_eq_prod_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id]
  rw [Real.log_prod (fun i _ => (hA.eigenvalues_pos i).ne')]

/-- C08-03, C08-12: 2 ln Ẑ_G = −Tr ln Θ = −ln det Θ (= Tr ln G); ΔΓ = −ln Ẑ_G = ½ Tr ln Θ. -/
theorem trace_log_form {K0 K : Matrix (Fin N) (Fin N) ℝ} (h0 : K0.PosDef) (hK : K.PosDef) :
    2 * Real.log (1 / Real.sqrt (whiten h0 hK).det) =
      -∑ i, Real.log ((whiten_posDef h0 hK).1.eigenvalues i) ∧
    -Real.log (1 / Real.sqrt (whiten h0 hK).det) =
      (1/2) * ∑ i, Real.log ((whiten_posDef h0 hK).1.eigenvalues i) := by
  rw [sum_log_eigenvalues (whiten_posDef h0 hK)]
  have hd := det_pos_of_posDef (whiten_posDef h0 hK)
  rw [one_div, Real.log_inv, Real.log_sqrt hd.le]
  constructor <;> ring

end Entropic.AppH10
