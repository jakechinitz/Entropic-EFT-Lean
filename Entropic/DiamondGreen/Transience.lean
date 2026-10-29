import Entropic.DiamondGreen.Fourier

/-!
# Transience: `G_tet(0) < ∞`, and the fcc integral representation

Two unconditional facts that shrink the cited input of `Value.lean`:

* `greenDiamond_lt_top`: the diamond lattice is transient, `G_tet(0) < ∞`. On `[-π,π]³`,
  `16 − |λ|² ≥ 2 ∑ᵢ (1 − cos kᵢ) ≥ (4/π²) |k|²`, and by the AM–GM inequality
  `1/|k|² ≤ (1/3) ∏ᵢ |kᵢ|^(-2/3)`, a product of integrable one-dimensional singularities.
* `returnFCC_eq_integral`: `|λ|² = 4 + ∑_v cos(k·v)` over the twelve fcc vectors, so the fcc return
  series is the fcc Brillouin-zone integral `(2π)⁻³ ∫ 12 / (12 − ∑_v cos(k·v))` in primitive
  coordinates.
-/

open MeasureTheory Complex Set
open scoped ENNReal Real

namespace Entropic.DiamondGreen

/-- `∑_v cos(k·v)` over the twelve fcc neighbour vectors (twelve times the fcc structure factor). -/
noncomputable def fccSum (k : ℝ × ℝ × ℝ) : ℝ := ∑ j : Fin 12, Real.cos (dot k (fcc j))

theorem phase_re (k : ℝ × ℝ × ℝ) (m : Z3) : (phase k m).re = Real.cos (dot k m) := by
  rw [phase, exp_ofReal_mul_I_re]

/-- `|λ(k)|² = 4 + ∑_v cos(k·v)`. -/
theorem normSq_lam_eq (k : ℝ × ℝ × ℝ) : normSq (lam k) = 4 + fccSum k := by
  have h := congrArg Complex.re (normSq_lam k)
  rw [ofReal_re] at h
  rw [h]
  have e := two_step_sum (fun m => phase k m) 0
  simp only [zero_add] at e
  have e' : ∑ i : Fin 4, ∑ j : Fin 4, phase k (bond i - bond j) =
      4 • phase k 0 + ∑ j : Fin 12, phase k (fcc j) := by
    exact e
  rw [e', phase_zero, add_re, re_sum, fccSum]
  simp [phase_re]

theorem fccSum_le (k : ℝ × ℝ × ℝ) :
    fccSum k ≤ 6 + 2 * (Real.cos k.1 + Real.cos k.2.1 + Real.cos k.2.2) := by
  simp only [fccSum]
  simp [Fin.sum_univ_succ, fcc, dot]
  linarith [Real.cos_le_one (k.1 + -k.2.1), Real.cos_le_one (k.1 + -k.2.2),
    Real.cos_le_one (-k.1 + k.2.1), Real.cos_le_one (k.2.1 + -k.2.2),
    Real.cos_le_one (-k.1 + k.2.2), Real.cos_le_one (-k.2.1 + k.2.2)]

/-- `1 − cos x ≥ 2x²/π²` on `[-π, π]`. -/
theorem one_sub_cos_ge {x : ℝ} (h1 : -π ≤ x) (h2 : x ≤ π) : 2 * x ^ 2 / π ^ 2 ≤ 1 - Real.cos x := by
  have hc : 1 - Real.cos x = 2 * Real.sin (|x| / 2) ^ 2 := by
    have e1 : Real.sin (|x| / 2) ^ 2 = Real.sin (x / 2) ^ 2 := by
      rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h, neg_div, Real.sin_neg]
    rw [e1]
    have := Real.cos_two_mul (x / 2)
    rw [show 2 * (x / 2) = x by ring] at this
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  have hs := Real.mul_le_sin (x := |x| / 2) (by positivity)
    (by have := abs_le.mpr ⟨h1, h2⟩; linarith)
  have hpi := Real.pi_pos
  rw [hc]
  have h0 : 0 ≤ 2 / π * (|x| / 2) := by positivity
  have : (2 / π * (|x| / 2)) ^ 2 ≤ Real.sin (|x| / 2) ^ 2 := pow_le_pow_left₀ h0 hs 2
  have e : (2 / π * (|x| / 2)) ^ 2 = x ^ 2 / π ^ 2 := by
    rw [mul_pow, div_pow, div_pow, sq_abs]; field_simp
  rw [e] at this
  have : 2 * x ^ 2 / π ^ 2 = 2 * (x ^ 2 / π ^ 2) := by ring
  linarith

/-- The one-dimensional singular weight `|x|^(-2/3)`, written as `(x²)^(-1/3)`. -/
noncomputable def wt (x : ℝ) : ℝ := (x ^ 2) ^ (-(1 / 3 : ℝ))

theorem wt_nonneg (x : ℝ) : 0 ≤ wt x := Real.rpow_nonneg (sq_nonneg x) _

theorem wt_eq (x : ℝ) : wt x = |x| ^ (-(2 / 3 : ℝ)) := by
  rw [wt, ← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg x)]; norm_num

theorem integrableOn_wt : IntegrableOn wt (Icc (-π) π) := by
  have hr : (-1 : ℝ) < -(2 / 3) := by norm_num
  have hpos : IntegrableOn (fun x : ℝ => x ^ (-(2 / 3 : ℝ))) (Icc 0 π) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le Real.pi_pos.le).mp (intervalIntegral.intervalIntegrable_rpow' hr)
  have hneg : IntegrableOn (fun x : ℝ => (-x) ^ (-(2 / 3 : ℝ))) (Icc (-π) 0) := by
    have h0 : IntervalIntegrable (fun x : ℝ => x ^ (-(2 / 3 : ℝ))) volume 0 π :=
      intervalIntegral.intervalIntegrable_rpow' hr
    have := (IntervalIntegrable.iff_comp_neg (enorm_ne_top)).mp h0
    rw [neg_zero] at this
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos])).mp this.symm
  have hu : Icc (-π) π = Icc (-π) 0 ∪ Icc 0 π := (Icc_union_Icc_eq_Icc (by linarith [Real.pi_pos])
    Real.pi_pos.le).symm
  rw [hu]
  refine IntegrableOn.union (hneg.congr_fun (fun x hx => ?_) measurableSet_Icc)
    (hpos.congr_fun (fun x hx => ?_) measurableSet_Icc)
  · rw [wt_eq, abs_of_nonpos hx.2]
  · rw [wt_eq, abs_of_nonneg hx.1]

/-- Pointwise bound `4/(16 − |λ|²) ≤ (π²/3) ∏ᵢ |kᵢ|^(-2/3)` on the cube with all `kᵢ ≠ 0`. -/
theorem integrand_le (k : ℝ × ℝ × ℝ) (hk : k ∈ cube) (h1 : k.1 ≠ 0) (h2 : k.2.1 ≠ 0)
    (h3 : k.2.2 ≠ 0) :
    4 / (16 - normSq (lam k)) ≤ π ^ 2 / 3 * (wt k.1 * (wt k.2.1 * wt k.2.2)) := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := hk
  have hpi := Real.pi_pos
  set x := k.1; set y := k.2.1; set z := k.2.2
  have hS : 16 - normSq (lam k) ≥ 4 / π ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2) := by
    rw [normSq_lam_eq]
    have := fccSum_le k
    have ex := one_sub_cos_ge a1 a2; have ey := one_sub_cos_ge b1 b2; have ez := one_sub_cos_ge c1 c2
    have : 4 / π ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2) =
        2 * (2 * x ^ 2 / π ^ 2) + 2 * (2 * y ^ 2 / π ^ 2) + 2 * (2 * z ^ 2 / π ^ 2) := by ring
    linarith
  -- AM–GM: x² + y² + z² ≥ 3 (x²)^(1/3) (y²)^(1/3) (z²)^(1/3)
  have amgm := Real.geom_mean_le_arith_mean3_weighted (w₁ := 1/3) (w₂ := 1/3) (w₃ := 1/3)
    (p₁ := x ^ 2) (p₂ := y ^ 2) (p₃ := z ^ 2) (by norm_num) (by norm_num) (by norm_num)
    (sq_nonneg _) (sq_nonneg _) (sq_nonneg _) (by norm_num)
  set P := (x ^ 2) ^ (1 / 3 : ℝ) * (y ^ 2) ^ (1 / 3 : ℝ) * (z ^ 2) ^ (1 / 3 : ℝ) with hP
  have hPpos : 0 < P := by
    have := pow_pos (sq_pos_of_ne_zero h1) 1
    positivity
  have hw : wt x * (wt y * wt z) = P⁻¹ := by
    simp only [wt, hP, Real.rpow_neg (sq_nonneg _), mul_inv]; ring
  rw [hw]
  have hden : 0 < 4 / π ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2) := by
    have := sq_pos_of_ne_zero h1; positivity
  calc 4 / (16 - normSq (lam k)) ≤ 4 / (4 / π ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2)) :=
        div_le_div_of_nonneg_left (by norm_num) hden hS
    _ ≤ 4 / (4 / π ^ 2 * (3 * P)) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = π ^ 2 / 3 * P⁻¹ := by field_simp

/-- **Transience of the diamond lattice:** `G_tet(0) < ∞`, unconditionally. -/
theorem greenDiamond_lt_top : greenDiamond < ⊤ := by
  rw [greenDiamond_eq_integral]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  -- dominating integrable function on the cube
  have hI : Integrable (fun k : ℝ × ℝ × ℝ => π ^ 2 / 3 * (wt k.1 * (wt k.2.1 * wt k.2.2)))
      (volume.restrict cube) := by
    have h23 : Integrable (fun p : ℝ × ℝ => wt p.1 * wt p.2)
        ((volume.restrict (Icc (-π) π)).prod (volume.restrict (Icc (-π) π))) :=
      Integrable.mul_prod (integrableOn_wt : Integrable wt _) (integrableOn_wt : Integrable wt _)
    have h123 := Integrable.mul_prod (integrableOn_wt : Integrable wt _) h23
    rw [Measure.prod_restrict, Measure.prod_restrict, ← Measure.volume_eq_prod,
      ← Measure.volume_eq_prod] at h123
    exact h123.const_mul _
  have hnull : ∀ᵐ k ∂(volume : Measure (ℝ × ℝ × ℝ)), k.1 ≠ 0 ∧ k.2.1 ≠ 0 ∧ k.2.2 ≠ 0 := by
    have n1 : (volume : Measure (ℝ × ℝ × ℝ)) {k | k.1 = 0} = 0 := by
      have : {k : ℝ × ℝ × ℝ | k.1 = 0} = ({0} : Set ℝ) ×ˢ univ := by ext k; simp
      rw [this, Measure.volume_eq_prod, Measure.prod_prod]; simp
    have n2 : (volume : Measure (ℝ × ℝ × ℝ)) {k | k.2.1 = 0} = 0 := by
      have : {k : ℝ × ℝ × ℝ | k.2.1 = 0} = univ ×ˢ (({0} : Set ℝ) ×ˢ univ) := by ext k; simp
      rw [this, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod,
        Measure.prod_prod]; simp
    have n3 : (volume : Measure (ℝ × ℝ × ℝ)) {k | k.2.2 = 0} = 0 := by
      have : {k : ℝ × ℝ × ℝ | k.2.2 = 0} = univ ×ˢ (univ ×ˢ ({0} : Set ℝ)) := by ext k; simp
      rw [this, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod,
        Measure.prod_prod]; simp
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp n1, measure_eq_zero_iff_ae_notMem.mp n2,
      measure_eq_zero_iff_ae_notMem.mp n3] with k e1 e2 e3
    exact ⟨e1, e2, e3⟩
  calc ∫⁻ k in cube, ENNReal.ofReal (4 / (16 - normSq (lam k)))
      ≤ ∫⁻ k in cube, ENNReal.ofReal (π ^ 2 / 3 * (wt k.1 * (wt k.2.1 * wt k.2.2))) := by
        apply lintegral_mono_ae
        rw [ae_restrict_iff' isCompact_cube.measurableSet]
        filter_upwards [hnull] with k ⟨e1, e2, e3⟩ hk
        exact ENNReal.ofReal_le_ofReal (integrand_le k hk e1 e2 e3)
    _ < ⊤ := hI.lintegral_lt_top

/-- The fcc return series is the fcc Brillouin-zone integral (primitive coordinates). -/
theorem returnFCC_eq_integral :
    returnFCC = ENNReal.ofReal ((2 * π) ^ 3)⁻¹ *
      ∫⁻ k in cube, ENNReal.ofReal (12 / (12 - fccSum k)) := by
  have h3 : returnFCC = 3 * greenDiamond := by
    rw [greenDiamond_eq, ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
  rw [h3, greenDiamond_eq_integral, ← mul_assoc, mul_comm 3, mul_assoc, ← lintegral_const_mul' _ _
    (by norm_num)]
  congr 2
  funext k
  rw [normSq_lam_eq, ← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  rw [show (16 : ℝ) - (4 + fccSum k) = 12 - fccSum k by ring]
  ring

end Entropic.DiamondGreen
