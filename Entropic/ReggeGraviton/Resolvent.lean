import Mathlib

/-!
# Strong-resolvent convergence of matrix-valued Fourier multipliers

Let `K_a(k)` and `K(k)` be Hermitian `n × n` matrices depending continuously on `k ∈ ℝ⁴`, with
`K_a(k) → K(k)` pointwise as `a → 0⁺`, and let `S_a` be measurable sets exhausting `ℝ⁴`
(the rescaled Brillouin zones). For `Im z ≠ 0` and `f ∈ L²(ℝ⁴; ℂⁿ)`,

  `‖1_{S_a} (K_a − z)⁻¹ f − (K − z)⁻¹ f‖_{L²} → 0`.

This is strong-resolvent convergence of the multiplication operators, with the lattice operator
acting on its Brillouin zone and extended by zero. The proof is dominated convergence:
`‖(H − z)⁻¹‖ ≤ 1/|Im z|` for Hermitian `H`, and `R_a − R = R_a (K − K_a) R`.
-/

open Matrix Complex Filter Topology MeasureTheory

namespace Entropic.ReggeGraviton

variable {n : Type*} [Fintype n] [DecidableEq n]
set_option linter.unusedSectionVars false

/-- Squared Euclidean norm on `ℂⁿ`. -/
noncomputable def nrm2 (v : n → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

theorem nrm2_nonneg (v : n → ℂ) : 0 ≤ nrm2 v := Finset.sum_nonneg fun _ _ => by positivity

theorem nrm2_eq_zero {v : n → ℂ} : nrm2 v = 0 ↔ v = 0 := by
  rw [nrm2, Finset.sum_eq_zero_iff_of_nonneg fun _ _ => by positivity]
  simp [funext_iff]

theorem star_dot_self (v : n → ℂ) : star v ⬝ᵥ v = (nrm2 v : ℂ) := by
  simp only [dotProduct, nrm2, Pi.star_apply, ofReal_sum, ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem norm_dot_le (v w : n → ℂ) : ‖star v ⬝ᵥ w‖ ^ 2 ≤ nrm2 v * nrm2 w := by
  have h1 : ‖star v ⬝ᵥ w‖ ≤ ∑ i, ‖v i‖ * ‖w i‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    simp
  have h3 : (∑ i, ‖v i‖ * ‖w i‖) ^ 2 ≤ (∑ i, ‖v i‖ ^ 2) * (∑ i, ‖w i‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ‖star v ⬝ᵥ w‖ ^ 2 ≤ (∑ i, ‖v i‖ * ‖w i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h3

theorem nrm2_sub_le (v w : n → ℂ) : nrm2 (v - w) ≤ 2 * nrm2 v + 2 * nrm2 w := by
  simp only [nrm2, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := norm_sub_le (v i) (w i)
  simp only [Pi.sub_apply]
  have h2 := mul_self_le_mul_self (norm_nonneg _) h
  nlinarith [sq_nonneg (‖v i‖ - ‖w i‖)]

theorem continuous_nrm2 : Continuous (nrm2 : (n → ℂ) → ℝ) := by
  unfold nrm2; fun_prop

variable {A : Matrix n n ℂ}

/-- `(Im z)² ‖v‖² ≤ ‖(A − z)v‖²` for Hermitian `A`. -/
theorem herm_lower (hA : A.IsHermitian) (z : ℂ) (v : n → ℂ) :
    z.im ^ 2 * nrm2 v ≤ nrm2 ((A - z • 1) *ᵥ v) := by
  set w := (A - z • 1) *ᵥ v
  have hs : star v ⬝ᵥ w = star v ⬝ᵥ (A *ᵥ v) - z * nrm2 v := by
    simp only [w, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul,
      star_dot_self, smul_eq_mul]
  have hreal : (star v ⬝ᵥ (A *ᵥ v)).im = 0 := by
    have := hA.star_dotProduct_mulVec_comm v v
    have h2 : (starRingEnd ℂ) (star v ⬝ᵥ (A *ᵥ v)) = star v ⬝ᵥ (A *ᵥ v) := this
    exact Complex.conj_eq_iff_im.mp h2
  have him : (star v ⬝ᵥ w).im = -(z.im * nrm2 v) := by
    rw [hs, sub_im, hreal]; simp
  have hcs := norm_dot_le v w
  have habs : |(star v ⬝ᵥ w).im| ≤ ‖star v ⬝ᵥ w‖ := Complex.abs_im_le_norm _
  rw [him, abs_neg, abs_mul, abs_of_nonneg (nrm2_nonneg v)] at habs
  have hN := nrm2_nonneg v
  have hW := nrm2_nonneg w
  have hsq : (|z.im| * nrm2 v) ^ 2 ≤ nrm2 v * nrm2 w :=
    (pow_le_pow_left₀ (by positivity) habs 2).trans hcs
  rcases hN.lt_or_eq with hpos | hzero
  · have : z.im ^ 2 * nrm2 v * nrm2 v ≤ nrm2 w * nrm2 v := by
      rw [mul_pow, sq_abs] at hsq; nlinarith
    exact le_of_mul_le_mul_right this hpos
  · rw [← hzero]; simp [hW]

theorem herm_det_ne (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) : (A - z • 1).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have := herm_lower hA z v
  rw [hAv] at this
  have h0 : nrm2 (0 : n → ℂ) = 0 := by simp [nrm2]
  rw [h0] at this
  have hpos : 0 < z.im ^ 2 := by positivity
  have : nrm2 v = 0 := le_antisymm (by nlinarith [nrm2_nonneg v]) (nrm2_nonneg v)
  exact hv (nrm2_eq_zero.mp this)

theorem herm_resolvent_bound (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (w : n → ℂ) :
    z.im ^ 2 * nrm2 ((A - z • 1)⁻¹ *ᵥ w) ≤ nrm2 w := by
  have hdet := herm_det_ne hA hz
  have := herm_lower hA z ((A - z • 1)⁻¹ *ᵥ w)
  rwa [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec] at this

/-- Second resolvent identity. -/
theorem resolvent_sub {B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) :
    (B - z • 1)⁻¹ - (A - z • 1)⁻¹ = (B - z • 1)⁻¹ * (A - B) * (A - z • 1)⁻¹ := by
  have hA' := isUnit_iff_ne_zero.mpr (herm_det_ne hA hz)
  have hB' := isUnit_iff_ne_zero.mpr (herm_det_ne hB hz)
  have : A - B = (A - z • 1) - (B - z • 1) := by abel
  rw [this, Matrix.mul_sub, Matrix.sub_mul, nonsing_inv_mul _ hB', Matrix.one_mul,
    Matrix.mul_assoc, mul_nonsing_inv _ hA', Matrix.mul_one]

theorem continuous_resolvent {X : Type*} [TopologicalSpace X] {K : X → Matrix n n ℂ}
    (hK : Continuous K) (hH : ∀ x, (K x).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun x => (K x - z • 1)⁻¹ := by
  have hc : Continuous fun x => K x - z • 1 := hK.sub continuous_const
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact (hc.matrix_det.inv₀ fun x => herm_det_ne (hH x) hz).smul hc.matrix_adjugate

/-- **Strong-resolvent convergence** of Hermitian matrix multipliers, with exhausting cutoffs. -/
theorem strong_resolvent_conv
    (Ka : ℝ → (Fin 4 → ℝ) → Matrix n n ℂ) (K : (Fin 4 → ℝ) → Matrix n n ℂ)
    (S : ℝ → Set (Fin 4 → ℝ))
    (hS : ∀ k, ∀ᶠ a in 𝓝[>] (0 : ℝ), k ∈ S a) (hSm : ∀ a, MeasurableSet (S a))
    (hH : ∀ a k, (Ka a k).IsHermitian) (hHK : ∀ k, (K k).IsHermitian)
    (hlim : ∀ k, Tendsto (fun a => Ka a k) (𝓝[>] 0) (𝓝 (K k)))
    (hc : ∀ a, Continuous (Ka a)) (hcK : Continuous K)
    {z : ℂ} (hz : z.im ≠ 0) (f : (Fin 4 → ℝ) → n → ℂ) (hfm : AEStronglyMeasurable f volume)
    (hfi : Integrable (fun k => nrm2 (f k))) :
    Tendsto (fun a => ∫ k, nrm2 ((S a).indicator (fun k => (Ka a k - z • 1)⁻¹ *ᵥ f k) k -
      (K k - z • 1)⁻¹ *ᵥ f k)) (𝓝[>] 0) (𝓝 0) := by
  have him : 0 < z.im ^ 2 := by positivity
  set C : ℝ := 4 / z.im ^ 2
  -- measurability of the integrands
  have hmv : ∀ {M : (Fin 4 → ℝ) → Matrix n n ℂ}, Continuous M →
      AEStronglyMeasurable (fun k => M k *ᵥ f k) volume := by
    intro M hM
    have hG : Continuous (Function.uncurry fun (k : Fin 4 → ℝ) (v : n → ℂ) => M k *ᵥ v) := by
      have h1 : Continuous fun p : (Fin 4 → ℝ) × (n → ℂ) => M p.1 := hM.comp continuous_fst
      exact continuous_pi fun i => continuous_finsetSum _ fun j _ =>
        ((continuous_apply_apply i j).comp h1).mul ((continuous_apply j).comp continuous_snd)
    exact hG.comp_aestronglyMeasurable₂ aestronglyMeasurable_id hfm
  have hR := continuous_resolvent hcK hHK hz
  have hRa := fun a => continuous_resolvent (hc a) (hH a) hz
  have hmeas : ∀ a, AEStronglyMeasurable (fun k => nrm2 ((S a).indicator
      (fun k => (Ka a k - z • 1)⁻¹ *ᵥ f k) k - (K k - z • 1)⁻¹ *ᵥ f k)) volume := fun a =>
    continuous_nrm2.comp_aestronglyMeasurable (((hmv (hRa a)).indicator (hSm a)).sub (hmv hR))
  -- domination
  have hbound : ∀ a, ∀ᵐ k ∂(volume : Measure (Fin 4 → ℝ)), ‖nrm2 ((S a).indicator
      (fun k => (Ka a k - z • 1)⁻¹ *ᵥ f k) k - (K k - z • 1)⁻¹ *ᵥ f k)‖ ≤ C * nrm2 (f k) := by
    intro a
    refine Eventually.of_forall fun k => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (nrm2_nonneg _)]
    have b1 := herm_resolvent_bound (hH a k) hz (f k)
    have b2 := herm_resolvent_bound (hHK k) hz (f k)
    have hf0 := nrm2_nonneg (f k)
    have e1 : nrm2 ((Ka a k - z • 1)⁻¹ *ᵥ f k) ≤ nrm2 (f k) / z.im ^ 2 := by
      rw [le_div_iff₀ him]; linarith
    have e2 : nrm2 ((K k - z • 1)⁻¹ *ᵥ f k) ≤ nrm2 (f k) / z.im ^ 2 := by
      rw [le_div_iff₀ him]; linarith
    have hC : C * nrm2 (f k) = 4 * (nrm2 (f k) / z.im ^ 2) := by simp only [C]; ring
    by_cases hk : k ∈ S a
    · rw [Set.indicator_of_mem hk]
      calc _ ≤ _ := nrm2_sub_le _ _
        _ ≤ C * nrm2 (f k) := by rw [hC]; linarith
    · rw [Set.indicator_of_notMem hk, zero_sub]
      have : nrm2 (-((K k - z • 1)⁻¹ *ᵥ f k)) = nrm2 ((K k - z • 1)⁻¹ *ᵥ f k) := by
        simp [nrm2]
      rw [this, hC]
      have := nrm2_nonneg (f k)
      have : 0 ≤ nrm2 (f k) / z.im ^ 2 := by positivity
      linarith
  -- pointwise limit
  have hpt : ∀ᵐ k ∂(volume : Measure (Fin 4 → ℝ)), Tendsto (fun a => nrm2 ((S a).indicator
      (fun k => (Ka a k - z • 1)⁻¹ *ᵥ f k) k - (K k - z • 1)⁻¹ *ᵥ f k)) (𝓝[>] 0) (𝓝 0) := by
    refine Eventually.of_forall fun k => ?_
    set w := (K k - z • 1)⁻¹ *ᵥ f k
    have hd : Tendsto (fun a => (K k - Ka a k) *ᵥ w) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun a => K k - Ka a k) (𝓝[>] 0) (𝓝 (K k - K k)) :=
        tendsto_const_nhds.sub (hlim k)
      rw [sub_self] at this
      have hmv' : Continuous fun M : Matrix n n ℂ => M *ᵥ w := by fun_prop
      have := (hmv'.tendsto 0).comp this
      rw [zero_mulVec] at this
      exact this
    have hd2 : Tendsto (fun a => nrm2 ((K k - Ka a k) *ᵥ w) / z.im ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have := ((continuous_nrm2.tendsto 0).comp hd).div_const (z.im ^ 2)
      simpa [nrm2] using this
    refine squeeze_zero' (Eventually.of_forall fun _ => nrm2_nonneg _) ?_ hd2
    filter_upwards [hS k] with a ha
    rw [Set.indicator_of_mem ha]
    have hid : (Ka a k - z • 1)⁻¹ *ᵥ f k - w = (Ka a k - z • 1)⁻¹ *ᵥ ((K k - Ka a k) *ᵥ w) := by
      simp only [w, mulVec_mulVec, ← sub_mulVec, ← Matrix.mul_assoc]
      rw [← resolvent_sub (hHK k) (hH a k) hz]
    rw [hid, le_div_iff₀ him]
    have := herm_resolvent_bound (hH a k) hz ((K k - Ka a k) *ᵥ w)
    linarith
  have := tendsto_integral_filter_of_dominated_convergence (fun k => C * nrm2 (f k))
    (Eventually.of_forall hmeas) (Eventually.of_forall hbound) (hfi.const_mul C) hpt
  simpa using this

end Entropic.ReggeGraviton
