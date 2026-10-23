import Entropic.AppH10.Gaussian
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Appendix H.11–H.12: the one-mark carrier, polar structure, Fubini–Study coordinates and bridge
algebra (ledger C09-10, -11, -12, -15, -16, -17, -18, -23, -25, -26, -27, -33, -45, -52, -56, -57,
-66, -69). -/

noncomputable section
namespace Entropic.AppH11
open Matrix
open scoped Kronecker

/-! ### Carrier isometry (C09-10, C09-11, C09-12) -/

section Carrier
variable {m k : ℕ}

/-- C09-10: if [F P₃; C] is an isometry with F†F = I and P₃ an orthogonal projector, then C†C = I − P₃. -/
theorem retained_gram {n v d : Type*} [Fintype n] [Fintype v] [Fintype d] [DecidableEq n]
    (F : Matrix v n ℝ) (P3 : Matrix n n ℝ) (C : Matrix d n ℝ) (hF : Fᵀ * F = 1) (hP : P3ᵀ = P3)
    (hPP : P3 * P3 = P3) (hiso : (F * P3)ᵀ * (F * P3) + Cᵀ * C = 1) : Cᵀ * C = 1 - P3 := by
  rw [Matrix.transpose_mul, hP, Matrix.mul_assoc, ← Matrix.mul_assoc Fᵀ, hF, Matrix.one_mul, hPP] at hiso
  rw [← hiso]; abel

/-- C09-11: L : ℝ^{16} → ℝ^9 with LᵀL = P (P² = P) of rank 9 has LLᵀ = I₉; and for χ = Pφ,
d = Lχ gives χ = Lᵀd. -/
theorem carrier_isometry (L : Matrix (Fin m) (Fin k) ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hL : Lᵀ * L = P) (hPP : P * P = P) (hr : P.rank = m) :
    L * Lᵀ = 1 ∧ ∀ φ : Fin k → ℝ, Lᵀ *ᵥ (L *ᵥ (P *ᵥ φ)) = P *ᵥ φ := by
  have hrank : (L * Lᵀ).rank = m := by
    rw [Matrix.rank_self_mul_transpose, ← Matrix.rank_transpose_mul_self, hL, hr]
  have hunit : IsUnit (L * Lᵀ) := by
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    have htop : LinearMap.range (L * Lᵀ).mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [show Module.finrank ℝ (LinearMap.range (L * Lᵀ).mulVecLin) = (L * Lᵀ).rank from rfl, hrank]
      simp
    intro y
    have : y ∈ LinearMap.range (L * Lᵀ).mulVecLin := by rw [htop]; trivial
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx⟩
  set M := L * Lᵀ
  have hMM : M * M * M = M * M := by
    calc M * M * M = L * ((Lᵀ * L) * (Lᵀ * L)) * Lᵀ := by simp only [M, Matrix.mul_assoc]
      _ = L * (Lᵀ * L) * Lᵀ := by rw [hL, hPP]
      _ = M * M := by simp only [M, Matrix.mul_assoc]
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hunit
  have hM : M = 1 := by
    have h1 : M⁻¹ * (M * M * M) * M⁻¹ = M⁻¹ * (M * M) * M⁻¹ := by rw [hMM]
    rw [show M⁻¹ * (M * M * M) * M⁻¹ = (M⁻¹ * M) * M * (M * M⁻¹) by simp only [Matrix.mul_assoc],
      show M⁻¹ * (M * M) * M⁻¹ = (M⁻¹ * M) * (M * M⁻¹) by simp only [Matrix.mul_assoc],
      Matrix.nonsing_inv_mul _ hdet, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul, Matrix.mul_one] at h1
    simpa using h1
  refine ⟨hM, fun φ => ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hL, hPP]

/-- C09-12: δχ = Lᵀδd gives δχᵀ H_Q δχ = δdᵀ (L H_Q Lᵀ) δd. -/
theorem inherited_hessian (L : Matrix (Fin m) (Fin k) ℝ) (H : Matrix (Fin k) (Fin k) ℝ) (d : Fin m → ℝ) :
    (Lᵀ *ᵥ d) ⬝ᵥ (H *ᵥ (Lᵀ *ᵥ d)) = d ⬝ᵥ ((L * H * Lᵀ) *ᵥ d) := by
  have hv : ∀ x : Fin m → ℝ, x ᵥ* L = Lᵀ *ᵥ x := fun x => by
    simpa using (Matrix.vecMul_transpose Lᵀ x)
  symm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hv]

/-- C09-12, C09-15: for orthogonal projectors P₀, P₁, P₂ resolving the identity,
vᵀ(6P₀ + 5P₁ + 3P₂)v ≥ 3|v|² (mismatch gap 3κ), so Ω² ≥ k² + M²/Z + 3κ/Z. -/
theorem mismatch_gap {n : Type*} [Fintype n] [DecidableEq n] (P0 P1 P2 : Matrix n n ℝ)
    (hs0 : P0ᵀ = P0) (hs1 : P1ᵀ = P1) (hs2 : P2ᵀ = P2) (hi0 : P0 * P0 = P0) (hi1 : P1 * P1 = P1)
    (hi2 : P2 * P2 = P2) (hsum : P0 + P1 + P2 = 1) (v : n → ℝ) :
    3 * (v ⬝ᵥ v) ≤ v ⬝ᵥ (((6:ℝ) • P0 + (5:ℝ) • P1 + (3:ℝ) • P2) *ᵥ v) := by
  have hnn : ∀ u : n → ℝ, 0 ≤ u ⬝ᵥ u := fun u => Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hq : ∀ P : Matrix n n ℝ, Pᵀ = P → P * P = P → v ⬝ᵥ (P *ᵥ v) = (P *ᵥ v) ⬝ᵥ (P *ᵥ v) := by
    intro P hs hi
    have hv : v ᵥ* Pᵀ = P *ᵥ v := Matrix.vecMul_transpose P v
    calc v ⬝ᵥ (P *ᵥ v) = v ⬝ᵥ ((Pᵀ * P) *ᵥ v) := by rw [hs, hi]
      _ = (P *ᵥ v) ⬝ᵥ (P *ᵥ v) := by rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hv]
  have hv : v ⬝ᵥ v = v ⬝ᵥ (P0 *ᵥ v) + v ⬝ᵥ (P1 *ᵥ v) + v ⬝ᵥ (P2 *ᵥ v) := by
    rw [← dotProduct_add, ← dotProduct_add, ← Matrix.add_mulVec, ← Matrix.add_mulVec, hsum,
      Matrix.one_mulVec]
  have e : v ⬝ᵥ (((6:ℝ) • P0 + (5:ℝ) • P1 + (3:ℝ) • P2) *ᵥ v) =
      6 * (v ⬝ᵥ (P0 *ᵥ v)) + 5 * (v ⬝ᵥ (P1 *ᵥ v)) + 3 * (v ⬝ᵥ (P2 *ᵥ v)) := by
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [e, hv, hq P0 hs0 hi0, hq P1 hs1 hi1, hq P2 hs2 hi2]
  nlinarith [hnn (P0 *ᵥ v), hnn (P1 *ᵥ v), hnn (P2 *ᵥ v)]

end Carrier

/-! ### Hamiltonian generator and polar part (C09-16, C09-17) -/

section Polar
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- C09-16: K₀ = [[0, Z⁻¹I], [−ZΩ², 0]] has −K₀² = Ω² ⊕ Ω²; J₀ := −K₀(Ω⁻¹ ⊕ Ω⁻¹) =
[[0, −(ZΩ)⁻¹], [ZΩ, 0]] and J₀² = −I. -/
theorem polar_generator (Ω : Matrix n n ℝ) (Z : ℝ) (hZ : Z ≠ 0) (hΩ : IsUnit Ω.det) :
    let K0 := Matrix.fromBlocks 0 (Z⁻¹ • (1 : Matrix n n ℝ)) (-(Z • (Ω * Ω))) 0
    let J0 := Matrix.fromBlocks 0 (-(Z⁻¹ • Ω⁻¹)) (Z • Ω) 0
    (-(K0 * K0) = Matrix.fromBlocks (Ω * Ω) 0 0 (Ω * Ω) ∧
      -K0 * Matrix.fromBlocks Ω⁻¹ 0 0 Ω⁻¹ = J0 ∧ J0 * J0 = -1) := by
  intro K0 J0
  have hl : Ω⁻¹ * Ω = 1 := Matrix.nonsing_inv_mul _ hΩ
  have hr : Ω * Ω⁻¹ = 1 := Matrix.mul_nonsing_inv _ hΩ
  refine ⟨?_, ?_, ?_⟩
  · simp only [K0, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg]
    simp [smul_smul, inv_mul_cancel₀ hZ, mul_inv_cancel₀ hZ]
  · simp only [K0, J0, Matrix.fromBlocks_neg, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc, hr]
  · simp only [J0, Matrix.fromBlocks_multiply]
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp [smul_smul, inv_mul_cancel₀ hZ, mul_inv_cancel₀ hZ, hl, hr]

/-- C09-17: g₀((q,p),(q,p)) := ω(v, J₀v) = Z qᵀΩq + Z⁻¹ pᵀΩ⁻¹p > 0 for v ≠ 0 (Ω > 0, Z > 0). -/
theorem polar_metric_pos {Ω : Matrix n n ℝ} (hΩ : Ω.PosDef) {Z : ℝ} (hZ : 0 < Z) (q p : n → ℝ)
    (hv : q ≠ 0 ∨ p ≠ 0) :
    0 < q ⬝ᵥ ((Z • Ω) *ᵥ q) - p ⬝ᵥ ((-(Z⁻¹ • Ω⁻¹)) *ᵥ p) := by
  have hinv : Ω⁻¹.PosDef := hΩ.inv
  have h1 : 0 ≤ q ⬝ᵥ (Ω *ᵥ q) := by simpa using hΩ.posSemidef.dotProduct_mulVec_nonneg q
  have h2 : 0 ≤ p ⬝ᵥ (Ω⁻¹ *ᵥ p) := by simpa using hinv.posSemidef.dotProduct_mulVec_nonneg p
  simp only [Matrix.smul_mulVec, Matrix.neg_mulVec, dotProduct_smul, dotProduct_neg,
    smul_eq_mul, sub_neg_eq_add]
  have hZi : 0 < Z⁻¹ := inv_pos.mpr hZ
  rcases hv with hq | hp
  · have := hΩ.dotProduct_mulVec_pos hq; rw [star_trivial] at this
    nlinarith [mul_pos hZ this, mul_nonneg hZi.le h2]
  · have := hinv.dotProduct_mulVec_pos hp; rw [star_trivial] at this
    nlinarith [mul_nonneg hZ.le h1, mul_pos hZi this]

/-- C09-18: with S² = ZΩ (S invertible), z := (Sq + iS⁻¹p)/√2 and Hamilton's equations
q′ = p/Z, p′ = −ZΩ²q, one has i z′ = Ωz. -/
theorem schrodinger_amplitude (Ω S Si : Matrix n n ℂ) (Z : ℂ) (hZ : Z ≠ 0) (hS : S * S = Z • Ω)
    (hSi : Si * S = 1) (hSi' : S * Si = 1) (q p : n → ℂ) :
    Complex.I • (S *ᵥ (Z⁻¹ • p) + Complex.I • (Si *ᵥ (-(Z • ((Ω * Ω) *ᵥ q))))) =
      Ω *ᵥ (S *ᵥ q + Complex.I • (Si *ᵥ p)) := by
  have hΩ : Ω = Z⁻¹ • (S * S) := by rw [hS, smul_smul, inv_mul_cancel₀ hZ, one_smul]
  have hA : Ω * Si = Z⁻¹ • S := by
    rw [hΩ, Matrix.smul_mul, Matrix.mul_assoc, hSi', Matrix.mul_one]
  have hB : Ω * S = Z • (Si * (Ω * Ω)) := by
    rw [hΩ]; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show Si * (S * S * (S * S)) = S * S * S by
      simp only [← Matrix.mul_assoc]; rw [hSi, Matrix.one_mul]]
    rw [show Z * (Z⁻¹ * Z⁻¹) = Z⁻¹ by field_simp]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec q Ω S, hB, Matrix.mulVec_smul Ω Complex.I (Si *ᵥ p),
    Matrix.mulVec_mulVec p Ω Si, hA, Matrix.mulVec_smul S Z⁻¹ p, Matrix.mulVec_neg, Matrix.mulVec_smul Si Z,
    Matrix.mulVec_mulVec q Si (Ω * Ω)]
  simp only [Matrix.smul_mulVec, smul_add, smul_neg, smul_smul]
  rw [show Complex.I * (Complex.I * Z) = -Z by rw [← mul_assoc, Complex.I_mul_I]; ring]
  module

end Polar

/-! ### Bilinear responses separate rays (C09-23) and bridge non-additivity (C09-33) -/

section Rays
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- C09-23 (iii): if z†Tz = w†Tw for every traceless Hermitian T and |z| = |w| = 1, then zz† = ww†. -/
theorem responses_separate (z w : n → ℂ) (hz : star z ⬝ᵥ z = 1) (hw : star w ⬝ᵥ w = 1)
    (h : ∀ T : Matrix n n ℂ, Tᴴ = T → T.trace = 0 → star z ⬝ᵥ (T *ᵥ z) = star w ⬝ᵥ (T *ᵥ w)) :
    Matrix.vecMulVec z (star z) = Matrix.vecMulVec w (star w) := by
  set M := Matrix.vecMulVec z (star z) - Matrix.vecMulVec w (star w)
  have hMh : Mᴴ = M := by
    simp only [M, Matrix.conjTranspose_sub]
    congr 1 <;> ext i j <;> simp [Matrix.vecMulVec_apply, mul_comm]
  have hval : ∀ T : Matrix n n ℂ, (M * T).trace = star z ⬝ᵥ (T *ᵥ z) - star w ⬝ᵥ (T *ᵥ w) := by
    intro T
    have pt : ∀ u : n → ℂ, (Matrix.vecMulVec u (star u) * T).trace = star u ⬝ᵥ (T *ᵥ u) := by
      intro u
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct,
        Matrix.mulVec, Pi.star_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by ring)
    simp only [M, Matrix.sub_mul, Matrix.trace_sub, pt]
  have htrM : M.trace = 0 := by
    have := hval 1; rw [Matrix.mul_one] at this; rw [this]; simp [hz, hw]
  have hzero := h M hMh htrM
  have h0 : (M * M).trace = 0 := by rw [hval, hzero, sub_self]
  have hMz : M = 0 := by
    have hfrob : (M * Mᴴ).trace = ∑ i, ∑ j, (Complex.normSq (M i j) : ℂ) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [Complex.star_def, Complex.mul_conj]
    rw [hMh, h0] at hfrob
    have hsum : ∑ i, ∑ j, Complex.normSq (M i j) = 0 := by exact_mod_cast hfrob.symm
    ext i j
    have hnn : ∀ i j, 0 ≤ Complex.normSq (M i j) := fun i j => Complex.normSq_nonneg _
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hnn i j))).mp
      hsum i (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn i j)).mp h1 j (Finset.mem_univ _)
    simpa using Complex.normSq_eq_zero.mp h2
  exact sub_eq_zero.mp hMz

/-- C09-23 (ii): f_T(z) = z†Tz is invariant under z ↦ e^{iθ}z. -/
theorem response_phase (T : Matrix n n ℂ) (z : n → ℂ) (θ : ℝ) :
    star (Complex.exp (θ * Complex.I) • z) ⬝ᵥ (T *ᵥ (Complex.exp (θ * Complex.I) • z)) =
      star z ⬝ᵥ (T *ᵥ z) := by
  rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_smul]
  have : star (Complex.exp (θ * Complex.I)) * Complex.exp (θ * Complex.I) = 1 := by
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]; simp [Complex.conj_ofReal]
  rw [this, one_smul]

/-- C09-33: for nonzero traceless X, Y, X ⊗ Y is not of the form A ⊗ I + I ⊗ B. -/
theorem bridge_not_additive [Nonempty n] (X Y : Matrix n n ℂ) (hX : X ≠ 0) (hY : Y ≠ 0) (htX : X.trace = 0)
    (htY : Y.trace = 0) (A B : Matrix n n ℂ) : X ⊗ₖ Y ≠ A ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix n n ℂ) ⊗ₖ B := by
  intro h
  have he : ∀ i j k l, X i j * Y k l = A i j * (if k = l then 1 else 0) + (if i = j then 1 else 0) * B k l := by
    intro i j k l
    have := congrFun (congrFun h (i, k)) (j, l)
    simpa [Matrix.kroneckerMap_apply, Matrix.one_apply] using this
  -- partial traces
  have hc : (Fintype.card n : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hA : ∀ i j, (Fintype.card n : ℂ) * A i j + (if i = j then 1 else 0) * B.trace = 0 := by
    intro i j
    have : ∑ k, X i j * Y k k = ∑ k, (A i j + (if i = j then 1 else 0) * B k k) := by
      refine Finset.sum_congr rfl (fun k _ => ?_); rw [he]; simp
    rw [← Finset.mul_sum, show ∑ k, Y k k = Y.trace from rfl, htY, mul_zero, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum] at this
    rw [show B.trace = ∑ k, B k k from rfl]; linear_combination -this
  have hB : ∀ k l, (Fintype.card n : ℂ) * B k l + (if k = l then 1 else 0) * A.trace = 0 := by
    intro k l
    have : ∑ i, X i i * Y k l = ∑ i, (A i i * (if k = l then 1 else 0) + B k l) := by
      refine Finset.sum_congr rfl (fun i _ => ?_); rw [he]; simp
    rw [← Finset.sum_mul, show ∑ i, X i i = X.trace from rfl, htX, zero_mul, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_mul] at this
    rw [show A.trace = ∑ i, A i i from rfl]; linear_combination -this
  -- so X_ij Y_kl = c δ_ij δ_kl with c := −(Tr A + Tr B)/N
  set N := (Fintype.card n : ℂ)
  have hXY : ∀ i j k l, X i j * Y k l =
      (-(A.trace + B.trace) / N) * ((if i = j then 1 else 0) * (if k = l then 1 else 0)) := by
    intro i j k l
    rw [he]
    have ha : A i j = -((if i = j then 1 else 0) * B.trace) / N := by
      field_simp; linear_combination hA i j
    have hb : B k l = -((if k = l then 1 else 0) * A.trace) / N := by
      field_simp; linear_combination hB k l
    rw [ha, hb]; field_simp; split_ifs <;> ring
  obtain ⟨i0, j0, hij⟩ : ∃ i j, X i j ≠ 0 := by
    by_contra hc'; push_neg at hc'; exact hX (Matrix.ext hc')
  obtain ⟨k0, l0, hkl⟩ : ∃ k l, Y k l ≠ 0 := by
    by_contra hc'; push_neg at hc'; exact hY (Matrix.ext hc')
  have hprod := hXY i0 j0 k0 l0
  have hne : X i0 j0 * Y k0 l0 ≠ 0 := mul_ne_zero hij hkl
  rw [hprod] at hne
  have hi : i0 = j0 := by by_contra h'; simp [h'] at hne
  have hk : k0 = l0 := by by_contra h'; simp [h'] at hne
  subst hi hk
  have hc' : X i0 i0 * Y k0 k0 = -(A.trace + B.trace) / N := by simpa using hXY i0 i0 k0 k0
  have hcne : -(A.trace + B.trace) / N ≠ 0 := hc' ▸ mul_ne_zero hij hkl
  -- every diagonal X_ii equals c / Y_{k0 k0}, so Tr X ≠ 0
  have hdiag : ∀ i, X i i = (-(A.trace + B.trace) / N) / Y k0 k0 := by
    intro i; have hh := hXY i i k0 k0
    simp only [eq_self_iff_true, if_true, mul_one] at hh
    rw [eq_div_iff hkl]; exact hh
  have htr : X.trace = N * ((-(A.trace + B.trace) / N) / Y k0 k0) := by
    rw [Matrix.trace]; simp only [Matrix.diag, hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; rfl
  rw [htX] at htr
  exact mul_ne_zero hc (div_ne_zero hcne hkl) htr.symm

end Rays

/-! ### Fubini–Study coordinates (C09-25 … C09-27) and the tautological connection (C09-45) -/

section FS
variable {n : Type*} [Fintype n]

/-- C09-25: with z_a = √P_a e^{iφ_a}, dz_a = (dP_a/(2√P_a) + i√P_a dφ_a)e^{iφ_a}, ΣP = 1, ΣdP = 0:
Σ|dz_a|² − |Σ z̄_a dz_a|² = (1/4)Σ dP_a²/P_a + Σ P_a (dφ_a − Σ_b P_b dφ_b)². -/
theorem fubini_study (P dP φ dφ : n → ℝ) (hP : ∀ a, 0 < P a) (h1 : ∑ a, P a = 1) (h0 : ∑ a, dP a = 0) :
    let z : n → ℂ := fun a => (Real.sqrt (P a) : ℂ) * Complex.exp (φ a * Complex.I)
    let dz : n → ℂ := fun a => ((dP a / (2 * Real.sqrt (P a)) : ℝ) + (Real.sqrt (P a) * dφ a : ℝ) * Complex.I) *
      Complex.exp (φ a * Complex.I)
    ∑ a, Complex.normSq (dz a) - Complex.normSq (∑ a, star (z a) * dz a) =
      (1/4) * ∑ a, dP a ^ 2 / P a + ∑ a, P a * (dφ a - ∑ b, P b * dφ b) ^ 2 := by
  intro z dz
  have hs : ∀ a, Real.sqrt (P a) ^ 2 = P a := fun a => Real.sq_sqrt (hP a).le
  have hsp : ∀ a, 0 < Real.sqrt (P a) := fun a => Real.sqrt_pos.mpr (hP a)
  have hu : ∀ a, Complex.normSq (Complex.exp (φ a * Complex.I)) = 1 := by
    intro a; rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; norm_num
  have hdz : ∀ a, Complex.normSq (dz a) = dP a ^ 2 / (4 * P a) + P a * dφ a ^ 2 := by
    intro a
    simp only [dz, Complex.normSq_mul, hu, mul_one, Complex.normSq_add_mul_I]
    have := hsp a
    rw [div_pow, mul_pow, mul_pow, hs a]; field_simp; ring
  have hzdz : ∀ a, star (z a) * dz a = ((dP a / 2 : ℝ) : ℂ) + ((P a * dφ a : ℝ) : ℂ) * Complex.I := by
    intro a
    simp only [z, dz, star_mul', Complex.star_def, Complex.conj_ofReal]
    have hconj : (starRingEnd ℂ) (Complex.exp (φ a * Complex.I)) * Complex.exp (φ a * Complex.I) = 1 := by
      rw [← Complex.exp_conj, ← Complex.exp_add]; simp [Complex.conj_ofReal]
    have := hsp a
    calc _ = (Real.sqrt (P a) : ℂ) * ((((dP a / (2 * Real.sqrt (P a))) : ℝ) : ℂ) +
            ((Real.sqrt (P a) * dφ a : ℝ) : ℂ) * Complex.I) *
            ((starRingEnd ℂ) (Complex.exp (φ a * Complex.I)) * Complex.exp (φ a * Complex.I)) := by ring
      _ = _ := by
        rw [hconj, mul_one]
        have e1 : Real.sqrt (P a) * (dP a / (2 * Real.sqrt (P a))) = dP a / 2 := by field_simp
        have e2 : Real.sqrt (P a) * (Real.sqrt (P a) * dφ a) = P a * dφ a := by
          rw [← mul_assoc, ← sq, hs a]
        rw [← e1, ← e2]; push_cast; ring
  rw [Finset.sum_congr rfl (fun a _ => hzdz a), Finset.sum_congr rfl (fun a _ => hdz a)]
  have hsum : ∑ a, (((dP a / 2 : ℝ) : ℂ) + ((P a * dφ a : ℝ) : ℂ) * Complex.I) =
      ((∑ a, P a * dφ a : ℝ) : ℂ) * Complex.I := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]; push_cast
    rw [← Finset.sum_div, show (∑ a, (dP a : ℂ)) = ((∑ a, dP a : ℝ) : ℂ) by push_cast; rfl, h0]; simp
  rw [hsum, Complex.normSq_mul, Complex.normSq_I, mul_one, Complex.normSq_ofReal]
  set m := ∑ b, P b * dφ b with hm
  have hexp : ∑ a, P a * (dφ a - m) ^ 2 = ∑ a, P a * dφ a ^ 2 - m * m := by
    have e : ∑ a, P a * (dφ a - m) ^ 2 =
        ∑ a, (P a * dφ a ^ 2 - 2 * m * (P a * dφ a) + m ^ 2 * P a) :=
      Finset.sum_congr rfl (fun a _ => by ring)
    rw [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1, ← hm]
    ring
  have h4 : ∑ a, dP a ^ 2 / (4 * P a) = 1/4 * ∑ a, dP a ^ 2 / P a := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => by have := hP a; field_simp)
  rw [hexp, Finset.sum_add_distrib, h4]; ring

/-- C09-26: Q = √(2P) cos φ, P^can = √(2P) sin φ has Jacobian ∂(Q,P^can)/∂(P,φ) = 1. -/
theorem polar_jacobian {P φ : ℝ} (hP : 0 < P) :
    HasDerivAt (fun x => Real.sqrt (2 * x) * Real.cos φ) (Real.cos φ / Real.sqrt (2 * P)) P ∧
    HasDerivAt (fun x => Real.sqrt (2 * x) * Real.sin φ) (Real.sin φ / Real.sqrt (2 * P)) P ∧
    HasDerivAt (fun t => Real.sqrt (2 * P) * Real.cos t) (-(Real.sqrt (2 * P) * Real.sin φ)) φ ∧
    HasDerivAt (fun t => Real.sqrt (2 * P) * Real.sin t) (Real.sqrt (2 * P) * Real.cos φ) φ ∧
    Real.cos φ / Real.sqrt (2 * P) * (Real.sqrt (2 * P) * Real.cos φ) -
      Real.sin φ / Real.sqrt (2 * P) * (-(Real.sqrt (2 * P) * Real.sin φ)) = 1 := by
  have h2 : 0 < 2 * P := by positivity
  have hs : HasDerivAt (fun x => Real.sqrt (2 * x)) (1 / Real.sqrt (2 * P)) P := by
    have := ((hasDerivAt_id' P).const_mul 2).sqrt h2.ne'
    convert this using 1; field_simp
  have hsp := Real.sqrt_pos.mpr h2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · convert hs.mul_const (Real.cos φ) using 1; ring
  · convert hs.mul_const (Real.sin φ) using 1; ring
  · convert (Real.hasDerivAt_cos φ).const_mul (Real.sqrt (2 * P)) using 1; ring
  · exact (Real.hasDerivAt_sin φ).const_mul _
  · field_simp; nlinarith [Real.cos_sq_add_sin_sq φ]

/-- C09-27: Σ dQ_a ∧ dP_a^can = Σ dP_a ∧ dφ_a = 2Ω_K with Ω_K = ½Σ dP_a∧dφ_a; rescaling Φ = ħφ
gives Ω_K = (1/(2ħ))Σ dP∧dΦ (coefficient bookkeeping). -/
theorem kahler_bookkeeping (ħ : ℝ) (hħ : ħ ≠ 0) (s : ℝ) : s = 2 * ((1/2) * s) ∧ (1/2) * s = (1/2) * (ħ * s / ħ) := by
  constructor <;> field_simp

/-- C09-45: A = −i z†dz is real for unit z (Re z†dz = ½d|z|² = 0), and under z ↦ e^{iθ}z,
A ↦ A + dθ. -/
theorem tautological_connection (z dz : n → ℂ) (θ dθ : ℝ) (hu : ∑ a, star (z a) * z a = 1)
    (hre : (∑ a, star (z a) * dz a).re = 0) :
    (-Complex.I * ∑ a, star (z a) * dz a).im = 0 ∧
    -Complex.I * ∑ a, star (Complex.exp (θ * Complex.I) * z a) *
        (Complex.I * dθ * Complex.exp (θ * Complex.I) * z a + Complex.exp (θ * Complex.I) * dz a) =
      -Complex.I * (∑ a, star (z a) * dz a) + dθ := by
  constructor
  · simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, hre]; ring
  · have hc : star (Complex.exp (θ * Complex.I)) * Complex.exp (θ * Complex.I) = 1 := by
      rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]; simp [Complex.conj_ofReal]
    have : ∀ a, star (Complex.exp (θ * Complex.I) * z a) *
        (Complex.I * dθ * Complex.exp (θ * Complex.I) * z a + Complex.exp (θ * Complex.I) * dz a) =
        (star (Complex.exp (θ * Complex.I)) * Complex.exp (θ * Complex.I)) *
          (Complex.I * dθ * (star (z a) * z a) + star (z a) * dz a) := by
      intro a; rw [star_mul']; ring
    simp_rw [this, hc, one_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hu]
    ring_nf; rw [Complex.I_sq]; ring

end FS

/-! ### Small scalar facts (C09-52, -56, -57, -66, -69) -/

/-- C09-52: 2^{3/2} ∈ (2.828, 2.829), exceeding the additive factor 2. -/
theorem fused_volume : 2.828 < (2:ℝ) ^ ((3:ℝ)/2) ∧ (2:ℝ) ^ ((3:ℝ)/2) < 2.829 := by
  have e : (2:ℝ) ^ ((3:ℝ)/2) = 2 * Real.sqrt 2 := by
    rw [show (3:ℝ)/2 = 1 + 1/2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  rw [e]
  constructor
  · nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2,
      show (1.414 : ℝ) < Real.sqrt 2 by rw [Real.lt_sqrt (by norm_num)]; norm_num]
  · nlinarith [show Real.sqrt 2 < 1.4145 by rw [Real.sqrt_lt' (by norm_num)]; norm_num]

/-- C09-56: 2a_s[1 − cos(π/n)] ≤ a_sπ²/n² (so the path gaps close like n⁻²). -/
theorem path_gap_bound (a : ℝ) (ha : 0 ≤ a) (n : ℝ) (hn : 0 < n) :
    2 * a * (1 - Real.cos (Real.pi / n)) ≤ a * Real.pi ^ 2 / n ^ 2 := by
  have := Real.one_sub_sq_div_two_le_cos (x := Real.pi / n)
  have e : a * Real.pi ^ 2 / n ^ 2 = 2 * a * ((Real.pi / n) ^ 2 / 2) := by field_simp
  rw [e]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

/-- C09-57: the Kuhn triangulation of the 4-cube has 4! = 24 simplices (one per permutation) and
2⁴ − 1 = 15 nonzero 0/1 edge directions. -/
theorem kuhn_counts : Fintype.card (Equiv.Perm (Fin 4)) = 24 ∧
    (Finset.univ.filter (fun v : Fin 4 → Fin 2 => v ≠ 0)).card = 15 := by
  refine ⟨by rw [Fintype.card_perm]; rfl, by decide⟩

/-- C09-66: k̂² = 4Σᵢ sin²(kᵢ/2) vanishes only when every kᵢ ∈ 2πℤ (no extra zeros at zone corners). -/
theorem lattice_symbol_zero (k : Fin 3 → ℝ) :
    4 * ∑ i, Real.sin (k i / 2) ^ 2 = 0 ↔ ∀ i, ∃ m : ℤ, k i = 2 * Real.pi * m := by
  constructor
  · intro h i
    have hnn : ∀ j, 0 ≤ Real.sin (k j / 2) ^ 2 := fun j => sq_nonneg _
    have h' : ∑ j, Real.sin (k j / 2) ^ 2 = 0 := by linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn j)).mp h' i (Finset.mem_univ _)
    have hs : Real.sin (k i / 2) = 0 := by simpa using this
    obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hs
    exact ⟨m, by linarith⟩
  · intro h
    have : ∀ i, Real.sin (k i / 2) = 0 := by
      intro i; obtain ⟨m, hm⟩ := h i
      rw [hm, show 2 * Real.pi * (m : ℝ) / 2 = (m : ℝ) * Real.pi by ring, Real.sin_int_mul_pi]
    simp [this]

/-- C09-69: Q = F(q), P = (1 − q²)^{1/4}p with F′ = (1 − q²)^{−1/4} has Jacobian F′·(1−q²)^{1/4} = 1. -/
theorem canonical_map {q : ℝ} (hq : |q| < 1) :
    (1 - q ^ 2) ^ (-(1:ℝ)/4) * (1 - q ^ 2) ^ ((1:ℝ)/4) = 1 := by
  have hpos : 0 < 1 - q ^ 2 := by nlinarith [abs_lt.mp hq, sq_abs q]
  rw [← Real.rpow_add hpos]; norm_num

end Entropic.AppH11
