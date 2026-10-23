import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-! Appendix H.10: resolvent bound and capacity Schur complement (ledger C08-60, -76, -77, -78, -75). -/

noncomputable section
namespace Entropic.AppH10
open Matrix InnerProductSpace

section Resolvent
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- For a symmetric operator T and v ∈ E: |Im z|‖v‖ ≤ ‖(T − z)v‖. -/
theorem resolvent_lower (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (z : ℂ) (v : E) :
    |z.im| * ‖v‖ ≤ ‖T v - z • v‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hself : (⟪v, T v⟫_ℂ).im = 0 := by
    have h2 : starRingEnd ℂ ⟪v, T v⟫_ℂ = ⟪v, T v⟫_ℂ := by rw [inner_conj_symm, hT v v]
    have := congrArg Complex.im h2
    rw [Complex.conj_im] at this; linarith
  have hin : ⟪v, T v - z • v⟫_ℂ = ⟪v, T v⟫_ℂ - z * ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]; rfl
  have him : (⟪v, T v - z • v⟫_ℂ).im = -(z.im * ‖v‖ ^ 2) := by
    rw [hin, Complex.sub_im, hself, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  have hcs : |(⟪v, T v - z • v⟫_ℂ).im| ≤ ‖v‖ * ‖T v - z • v‖ :=
    (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)
  rw [him, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖v‖ ^ 2)] at hcs
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  nlinarith

/-- C08-60: ‖(T − z)⁻¹ w‖ ≤ ‖w‖ / |Im z| for z off the real axis (stated for any right inverse R). -/
theorem resolvent_bound (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (z : ℂ) (hz : z.im ≠ 0)
    (R : E → E) (hR : ∀ w, T (R w) - z • R w = w) (w : E) : ‖R w‖ ≤ ‖w‖ / |z.im| := by
  have h := resolvent_lower T hT z (R w)
  rw [hR] at h
  rw [le_div_iff₀ (abs_pos.mpr hz)]; linarith

end Resolvent

section Schur
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- If re⟪u, Mu⟫ ≥ Δ‖u‖² and M ∘ Minv = id, then Δ‖Minv w‖ ≤ ‖w‖ and re⟪w, Minv w⟫ ≤ ‖w‖²/Δ. -/
theorem coercive_inverse (M Minv : F →L[ℂ] F) {Δ : ℝ} (hΔ : 0 < Δ)
    (hM : ∀ u, Δ * ‖u‖ ^ 2 ≤ (⟪u, M u⟫_ℂ).re) (hinv : ∀ w, M (Minv w) = w) (w : F) :
    Δ * ‖Minv w‖ ≤ ‖w‖ ∧ (⟪w, Minv w⟫_ℂ).re ≤ ‖w‖ ^ 2 / Δ := by
  set u := Minv w
  have hw : M u = w := hinv w
  have hre : (⟪w, u⟫_ℂ).re = (⟪u, M u⟫_ℂ).re := by
    rw [← hw, ← inner_conj_symm, Complex.conj_re, hw]
  have h1 : Δ * ‖u‖ ^ 2 ≤ ‖w‖ * ‖u‖ := by
    have := hM u; rw [← hre] at this
    exact this.trans ((Complex.re_le_norm _).trans (norm_inner_le_norm _ _))
  have h2 : Δ * ‖u‖ ≤ ‖w‖ := by
    rcases eq_or_lt_of_le (norm_nonneg u) with h0 | hpos
    · rw [← h0]; simp
    · nlinarith
  refine ⟨h2, ?_⟩
  rw [le_div_iff₀ hΔ]
  have h3 : (⟪w, u⟫_ℂ).re ≤ ‖w‖ * ‖u‖ := (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  nlinarith [norm_nonneg w]

/-- C08-77: ‖B M⁻¹ B†‖ ≤ ‖B‖²/Δ. -/
theorem schur_norm_bound (M Minv : F →L[ℂ] F) (B : F →L[ℂ] E) {Δ : ℝ} (hΔ : 0 < Δ)
    (hM : ∀ u, Δ * ‖u‖ ^ 2 ≤ (⟪u, M u⟫_ℂ).re) (hinv : ∀ w, M (Minv w) = w) :
    ‖B.comp (Minv.comp (ContinuousLinearMap.adjoint B))‖ ≤ ‖B‖ ^ 2 / Δ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  simp only [ContinuousLinearMap.comp_apply]
  have h1 := (coercive_inverse M Minv hΔ hM hinv (ContinuousLinearMap.adjoint B v)).1
  have hB := B.le_opNorm (Minv (ContinuousLinearMap.adjoint B v))
  have hBa := (ContinuousLinearMap.adjoint B).le_opNorm v
  rw [LinearIsometryEquiv.norm_map] at hBa
  calc ‖B (Minv (ContinuousLinearMap.adjoint B v))‖ ≤ ‖B‖ * ‖Minv (ContinuousLinearMap.adjoint B v)‖ := hB
    _ ≤ ‖B‖ * (‖ContinuousLinearMap.adjoint B v‖ / Δ) := by
        gcongr; rw [le_div_iff₀ hΔ]; linarith
    _ ≤ ‖B‖ * (‖B‖ * ‖v‖ / Δ) := by gcongr
    _ = ‖B‖ ^ 2 / Δ * ‖v‖ := by ring

/-- C08-78: if Pv = v, v ≠ 0 and ‖B‖² < Z_G Δ, then re⟪v, (Z_G P − B M⁻¹ B†) v⟫ > 0: the k²
coefficient is positive definite on Ran P_TT, so there is no extra massless pole. -/
theorem no_extra_pole (M Minv : F →L[ℂ] F) (B : F →L[ℂ] E) (P : E →L[ℂ] E) {Δ Z : ℝ} (hΔ : 0 < Δ)
    (hM : ∀ u, Δ * ‖u‖ ^ 2 ≤ (⟪u, M u⟫_ℂ).re) (hinv : ∀ w, M (Minv w) = w)
    (hB : ‖B‖ ^ 2 < Z * Δ) (v : E) (hv : v ≠ 0) (hPv : P v = v) :
    0 < (⟪v, (Z : ℂ) • P v - B (Minv (ContinuousLinearMap.adjoint B v))⟫_ℂ).re := by
  rw [hPv, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
    ← ContinuousLinearMap.adjoint_inner_left]
  have h := (coercive_inverse M Minv hΔ hM hinv (ContinuousLinearMap.adjoint B v)).2
  have hBa := (ContinuousLinearMap.adjoint B).le_opNorm v
  rw [LinearIsometryEquiv.norm_map] at hBa
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hsq : ‖ContinuousLinearMap.adjoint B v‖ ^ 2 ≤ ‖B‖ ^ 2 * ‖v‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hBa 2
  simp only [Complex.sub_re]
  have key : ((Z : ℂ) * ((‖v‖ : ℝ) : ℂ) ^ 2).re = Z * ‖v‖ ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  erw [key]
  have h4 : ‖ContinuousLinearMap.adjoint B v‖ ^ 2 / Δ ≤ ‖B‖ ^ 2 * ‖v‖ ^ 2 / Δ :=
    div_le_div_of_nonneg_right hsq hΔ.le
  have h5 : ‖B‖ ^ 2 * ‖v‖ ^ 2 / Δ < Z * ‖v‖ ^ 2 := by
    rw [div_lt_iff₀ hΔ]; nlinarith [pow_pos hvpos 2]
  linarith

/-- C08-75: if Z_G > 0 and |δZ_G| < Z_G then Z_G + δZ_G > 0. -/
theorem einstein_phase_stability {Z dZ : ℝ} (h : |dZ| < Z) : 0 < Z + dZ := by
  have := neg_abs_le dZ; linarith

end Schur

/-! ### Block elimination (C08-76) -/

section Block
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- C08-76: eliminating the capacity block of [[A, B], [B†, M]] (M invertible) at the stationary
point y = −M⁻¹B†x leaves (A − BM⁻¹B†)x and a vanishing second row; det K = det M · det K_eff. -/
theorem capacity_schur (A : Matrix m m ℂ) (B : Matrix m n ℂ) (M : Matrix n n ℂ) (hM : IsUnit M.det)
    (x : m → ℂ) :
    Matrix.fromBlocks A B Bᴴ M *ᵥ Sum.elim x (-(M⁻¹ *ᵥ (Bᴴ *ᵥ x))) =
        Sum.elim ((A - B * M⁻¹ * Bᴴ) *ᵥ x) 0 ∧
      (Matrix.fromBlocks A B Bᴴ M).det = M.det * (A - B * M⁻¹ * Bᴴ).det := by
  haveI := M.invertibleOfIsUnitDet hM
  refine ⟨?_, by rw [Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]⟩
  ext (i | i)
  · simp [Matrix.fromBlocks_mulVec, Matrix.sub_mulVec, Matrix.mulVec_neg, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, sub_eq_add_neg, Matrix.add_mulVec, Matrix.neg_mulVec]
  · simp [Matrix.fromBlocks_mulVec, Matrix.mulVec_neg, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hM]

end Block

end Entropic.AppH10
