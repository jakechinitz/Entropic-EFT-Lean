import Entropic.AppH10.Gaussian
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Appendix H.10: connected functional, exact Legendre identity, Γ_rel ≥ 0, trace-log series
(ledger C08-07, -08, -09, -14). -/

noncomputable section
namespace Entropic.AppH10
open Matrix Real

variable {N : ℕ}

/-- For positive a: a − 1 − ln a ≥ 0, with equality iff a = 1. -/
theorem scalar_rel (a : ℝ) (ha : 0 < a) : 0 ≤ a - 1 - Real.log a := by
  have := Real.log_le_sub_one_of_pos ha; linarith

theorem scalar_rel_eq {a : ℝ} (ha : 0 < a) (h : a - 1 - Real.log a = 0) : a = 1 := by
  by_contra hne
  have := Real.log_lt_sub_one_of_pos ha hne; linarith

/-- For A > 0: Tr A − ln det A − N = Σ (aᵢ − 1 − ln aᵢ) ≥ 0. -/
theorem trace_sub_logdet {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef) :
    A.trace - Real.log A.det - N = ∑ i, (hA.1.eigenvalues i - 1 - Real.log (hA.1.eigenvalues i)) := by
  rw [hA.1.trace_eq_sum_eigenvalues, ← sum_log_eigenvalues hA]
  simp only [RCLike.ofReal_real_eq_id, id, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]; ring

theorem trace_sub_logdet_nonneg {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef) :
    0 ≤ A.trace - Real.log A.det - N := by
  rw [trace_sub_logdet hA]
  exact Finset.sum_nonneg (fun i _ => scalar_rel _ (hA.eigenvalues_pos i))

theorem trace_sub_logdet_eq_zero {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    (h : A.trace - Real.log A.det - N = 0) : A = 1 := by
  rw [trace_sub_logdet hA] at h
  have hall : ∀ i, hA.1.eigenvalues i = 1 := by
    intro i
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => scalar_rel _ (hA.eigenvalues_pos i))).mp h i (Finset.mem_univ _)
    exact scalar_rel_eq (hA.eigenvalues_pos i) hz
  have hd : hA.1.eigenvalues = fun _ => 1 := funext hall
  rw [evec_spectral hA.1, hd, show (diagonal fun _ : Fin N => (1:ℝ)) = 1 from rfl, Matrix.mul_one,
    evec_mul_transpose]

theorem trace_logdet_one : (1 : Matrix (Fin N) (Fin N) ℝ).trace - Real.log (1 : Matrix (Fin N) (Fin N) ℝ).det
    - N = 0 := by simp

/-- Γ_rel[G] := ½ Tr[G − I − ln G]. -/
def gammaRel (G : Matrix (Fin N) (Fin N) ℝ) : ℝ := (1/2) * (G.trace - N - Real.log G.det)

/-- C08-09: Γ_rel[G] ≥ 0, and Γ_rel[G] = 0 iff G = I. -/
theorem gammaRel_nonneg {G : Matrix (Fin N) (Fin N) ℝ} (hG : G.PosDef) : 0 ≤ gammaRel G := by
  unfold gammaRel; have := trace_sub_logdet_nonneg hG; linarith

theorem gammaRel_eq_zero_iff {G : Matrix (Fin N) (Fin N) ℝ} (hG : G.PosDef) :
    gammaRel G = 0 ↔ G = 1 := by
  constructor
  · intro h; unfold gammaRel at h
    exact trace_sub_logdet_eq_zero hG (by linarith)
  · rintro rfl; unfold gammaRel; simp

/-- The Legendre objective ½Tr(GU) − W[U] with W[U] = −½ ln det(I − U). -/
def legendreObj (G U : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  (1/2) * (G * U).trace + (1/2) * Real.log (1 - U).det

/-- C08-08: for every symmetric U with I − U > 0, ½Tr(GU) − W[U] ≤ Γ_rel[G]; equality holds iff
U = I − G⁻¹ (the supremum is attained uniquely there). -/
theorem legendre_le {G U : Matrix (Fin N) (Fin N) ℝ} (hG : G.PosDef) (hM : (1 - U).PosDef) :
    legendreObj G U ≤ gammaRel G ∧ (legendreObj G U = gammaRel G → U = 1 - G⁻¹) := by
  set M := 1 - U with hMdef
  set S := psqrt hG
  have hSt : Sᴴ = S := by rw [Matrix.conjTranspose_eq_transpose_of_trivial, psqrt_transpose]
  have hSu : IsUnit S := (S.isUnit_iff_isUnit_det).mpr (psqrt_isUnit hG)
  have hA : (S * M * S).PosDef := by
    have := hM.conjTranspose_mul_mul_same (B := S) (Matrix.mulVec_injective_of_isUnit hSu)
    rwa [hSt] at this
  have htr : (S * M * S).trace = (G * M).trace := by
    rw [Matrix.trace_mul_cycle, ← psqrt_mul_self hG]
  have hdet : (S * M * S).det = G.det * M.det := by
    rw [Matrix.det_mul, Matrix.det_mul, ← psqrt_mul_self hG, Matrix.det_mul]; ring
  have hGd := det_pos_of_posDef hG
  have hMd := det_pos_of_posDef hM
  have hU : U = 1 - M := by rw [hMdef]; abel
  have hobj : legendreObj G U = (1/2) * G.trace - (1/2) * (S * M * S).trace + (1/2) * Real.log M.det := by
    unfold legendreObj; rw [htr, hU, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_one, sub_sub_cancel]
    ring
  have key : gammaRel G - legendreObj G U =
      (1/2) * ((S * M * S).trace - Real.log (S * M * S).det - N) := by
    rw [hobj, hdet, Real.log_mul hGd.ne' hMd.ne']; unfold gammaRel; ring
  refine ⟨by have := trace_sub_logdet_nonneg hA; linarith, fun heq => ?_⟩
  have h1 : S * M * S = 1 := trace_sub_logdet_eq_zero hA (by linarith)
  have hGinv : G⁻¹ = M := by
    rw [← psqrt_mul_self hG]
    have hSi : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S ((S.isUnit_iff_isUnit_det).mp hSu)
    have hSi' : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S ((S.isUnit_iff_isUnit_det).mp hSu)
    rw [Matrix.mul_inv_rev]
    calc S⁻¹ * S⁻¹ = S⁻¹ * (S * M * S) * S⁻¹ := by rw [h1, Matrix.mul_one]
      _ = (S⁻¹ * S) * M * (S * S⁻¹) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [hSi, hSi']; simp
  rw [hGinv, hMdef]; abel

theorem legendre_attained {G : Matrix (Fin N) (Fin N) ℝ} (hG : G.PosDef) :
    legendreObj G (1 - G⁻¹) = gammaRel G := by
  have hGd := det_pos_of_posDef hG
  have hu : IsUnit G.det := hGd.ne'.isUnit
  unfold legendreObj gammaRel
  rw [sub_sub_cancel, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_nonsing_inv _ hu, Matrix.trace_sub,
    Matrix.trace_one, Fintype.card_fin, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Real.log_inv]
  ring

/-- I − (I − G⁻¹) = G⁻¹ is positive definite, so the maximizer is admissible. -/
theorem legendre_admissible {G : Matrix (Fin N) (Fin N) ℝ} (hG : G.PosDef) :
    (1 - (1 - G⁻¹)).PosDef := by rw [sub_sub_cancel]; exact hG.inv

/-! ### Connected functional derivative (C08-07) -/

theorem hasDerivAt_det_one_add (A : Matrix (Fin N) (Fin N) ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • A).det) A.trace 0 := by
  set q := (det (1 + (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C)).divX.divX
  have hf : (fun t : ℝ => (1 + t • A).det) = fun t => 1 + A.trace * t + q.eval t * t ^ 2 := by
    funext t; exact Matrix.det_one_add_smul t A
  rw [hf]
  have h1 := ((hasDerivAt_id (0:ℝ)).const_mul A.trace).const_add 1
  have h2 := (q.hasDerivAt (0:ℝ)).mul ((hasDerivAt_id (0:ℝ)).pow 2)
  convert h1.add h2 using 1
  · funext t; simp
  · simp

/-- C08-07: with W[U] = −½ ln det(I − U) and G = (I − U)⁻¹, the directional derivative of W along
a symmetric H is ½ Tr(GH), i.e. 2 dW/dU = G under the trace pairing. -/
theorem connected_derivative {U H : Matrix (Fin N) (Fin N) ℝ} (hM : (1 - U).PosDef) :
    HasDerivAt (fun t : ℝ => -(1/2) * Real.log (1 - (U + t • H)).det)
      ((1/2) * ((1 - U)⁻¹ * H).trace) 0 := by
  set M := 1 - U
  have hMd := det_pos_of_posDef hM
  have hu : IsUnit M.det := hMd.ne'.isUnit
  have hfac : ∀ t : ℝ, (1 - (U + t • H)).det = M.det * (1 + t • (-(M⁻¹ * H))).det := by
    intro t
    rw [← Matrix.det_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_neg,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
    congr 1; simp only [M, smul_neg]; abel
  have hd := (hasDerivAt_det_one_add (-(M⁻¹ * H))).const_mul M.det
  have hpos : M.det * (1 + (0:ℝ) • (-(M⁻¹ * H))).det ≠ 0 := by simp [hMd.ne']
  have hl := (hd.log hpos).const_mul (-(1/2))
  have e : (fun t : ℝ => -(1/2) * Real.log (1 - (U + t • H)).det) =
      fun t => -(1/2) * Real.log (M.det * (1 + t • (-(M⁻¹ * H))).det) := by
    funext t; rw [hfac]
  rw [e]; convert hl using 1
  simp [Matrix.trace_neg]; field_simp

/-! ### Trace-log power series (C08-14) -/

/-- C08-14: for symmetric U with spectrum in (−1, 1), −Tr ln(I − U) = Σₙ Tr(Uⁿ)/n,
in the eigenvalue form −Σᵢ ln(1 − uᵢ) = Σₙ Σᵢ uᵢⁿ/n. -/
theorem trace_log_series {ι : Type*} [Fintype ι] (u : ι → ℝ) (hu : ∀ i, |u i| < 1) :
    HasSum (fun n : ℕ => ∑ i, u i ^ (n + 1) / (n + 1)) (-∑ i, Real.log (1 - u i)) := by
  rw [← Finset.sum_neg_distrib]
  exact hasSum_sum (fun i _ => Real.hasSum_pow_div_log_of_abs_lt_one (hu i))

/-- Tr(Uⁿ) = Σᵢ uᵢⁿ for a symmetric matrix (so the series above is the matrix series). -/
theorem trace_pow_eq {U : Matrix (Fin N) (Fin N) ℝ} (hU : U.IsHermitian) (n : ℕ) :
    (U ^ n).trace = ∑ i, hU.eigenvalues i ^ n := by
  have gen : ∀ (V : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℝ), Vᵀ * V = 1 →
      ∀ W : Matrix (Fin N) (Fin N) ℝ, W = V * diagonal d * Vᵀ → ∀ m : ℕ,
        W ^ m = V * diagonal (fun i => d i ^ m) * Vᵀ := by
    intro V d hV W hW m
    induction m with
    | zero =>
      simp only [pow_zero]
      have : V * Vᵀ = 1 := mul_eq_one_comm.mp hV
      rw [show (diagonal fun _ : Fin N => (1:ℝ)) = 1 from rfl, Matrix.mul_one, this]
    | succ k ih =>
      rw [pow_succ, ih, hW,
        show V * diagonal (fun i => d i ^ k) * Vᵀ * (V * diagonal d * Vᵀ) =
          V * diagonal (fun i => d i ^ k) * (Vᵀ * V) * diagonal d * Vᵀ by simp only [Matrix.mul_assoc],
        hV, Matrix.mul_one, Matrix.mul_assoc V, diagonal_mul_diagonal]
      simp only [pow_succ]
  have hp := gen _ _ (evec_transpose_mul hU) U (evec_spectral hU) n
  rw [hp, Matrix.trace_mul_cycle, evec_transpose_mul, Matrix.one_mul, Matrix.trace_diagonal]

end Entropic.AppH10
