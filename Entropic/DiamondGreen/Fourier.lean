import Entropic.DiamondGreen.Series

/-!
# The Brillouin-zone integral of the manuscript is the walk series (C05-20)

Appendix C.5 defines

  `G_tet(0) = (2π)⁻³ ∫_{[-π,π]³} 4 d³k / (16 − |1 + e^{ik₁} + e^{ik₂} + e^{ik₃}|²)`.

With `λ(k) = ∑ᵢ e^{ik·δᵢ}`, the Fourier orthogonality `(2π)⁻³ ∫ e^{ik·m} = [m = 0]` gives
`(2π)⁻³ ∫ e^{ik·y} |λ|^{2n} = #(diamond walks of length 2n from A_y to A_0)`, by the same two-step
recursion that defines the walk counts. Expanding `4/(16 − |λ|²) = ∑ₙ |λ|^{2n}/4^{2n+1}` (valid
for `k ≠ 0`; the proof discards the null plane `k₁ = 0`) and integrating term by term (monotone convergence) identifies the
integral with `greenDiamond`. The integral is the Lebesgue integral of a nonnegative function,
taken in `[0, ∞]`.
-/

open MeasureTheory Complex Set
open scoped ENNReal Real

namespace Entropic.DiamondGreen

/-- `k · m` for `k ∈ ℝ³` and an integer vector `m` (primitive fcc coordinates). -/
def dot (k : ℝ × ℝ × ℝ) (m : Z3) : ℝ := k.1 * m.1 + k.2.1 * m.2.1 + k.2.2 * m.2.2

/-- The plane wave `e^{ik·m}`. -/
noncomputable def phase (k : ℝ × ℝ × ℝ) (m : Z3) : ℂ := exp ((dot k m : ℂ) * I)

/-- The diamond structure factor `λ(k) = 1 + e^{ik₁} + e^{ik₂} + e^{ik₃}`. -/
noncomputable def lam (k : ℝ × ℝ × ℝ) : ℂ := ∑ i : Fin 4, phase k (bond i)

/-- The Brillouin zone `[-π, π]³`. -/
def cube : Set (ℝ × ℝ × ℝ) := Icc (-π) π ×ˢ (Icc (-π) π ×ˢ Icc (-π) π)

theorem lam_eq (k : ℝ × ℝ × ℝ) :
    lam k = 1 + exp (k.1 * I) + exp (k.2.1 * I) + exp (k.2.2 * I) := by
  simp [lam, phase, dot, Fin.sum_univ_four, bond]

theorem dot_add (k : ℝ × ℝ × ℝ) (m m' : Z3) : dot k (m + m') = dot k m + dot k m' := by
  simp only [dot, Prod.fst_add, Prod.snd_add, Int.cast_add]; ring

theorem dot_neg (k : ℝ × ℝ × ℝ) (m : Z3) : dot k (-m) = -dot k m := by
  simp only [dot, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]; ring

theorem phase_add (k : ℝ × ℝ × ℝ) (m m' : Z3) : phase k (m + m') = phase k m * phase k m' := by
  rw [phase, phase, phase, ← exp_add, dot_add]; push_cast; ring_nf

theorem phase_zero (k : ℝ × ℝ × ℝ) : phase k 0 = 1 := by simp [phase, dot]

theorem conj_phase (k : ℝ × ℝ × ℝ) (m : Z3) : (starRingEnd ℂ) (phase k m) = phase k (-m) := by
  rw [phase, phase, ← exp_conj, dot_neg]
  simp [map_mul, conj_ofReal, conj_I]

/-- `|λ(k)|² = ∑ᵢⱼ e^{ik·(δᵢ − δⱼ)}`. -/
theorem normSq_lam (k : ℝ × ℝ × ℝ) :
    (normSq (lam k) : ℂ) = ∑ i : Fin 4, ∑ j : Fin 4, phase k (bond i - bond j) := by
  rw [← mul_conj, lam, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [conj_phase, ← phase_add, sub_eq_add_neg]

theorem continuous_phase (m : Z3) : Continuous fun k => phase k m := by
  unfold phase dot; fun_prop

theorem continuous_normSq_lam : Continuous fun k => normSq (lam k) := by
  unfold lam; exact Complex.continuous_normSq.comp (continuous_finsetSum _ fun i _ => continuous_phase _)

theorem isCompact_cube : IsCompact cube := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

/-! ### Orthogonality -/

theorem integral_circle (m : ℤ) :
    ∫ x in Icc (-π) π, exp (((x * m : ℝ) : ℂ) * I) = if m = 0 then (2 * π : ℂ) else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have e : ∀ x : ℝ, exp (((x * m : ℝ) : ℂ) * I) = exp ((m * I) * x) := fun x => by
    push_cast; ring_nf
  simp_rw [e]
  split_ifs with hm
  · subst hm; simp; ring
  · have hc : (m : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hm) I_ne_zero
    rw [integral_exp_mul_complex hc, div_eq_zero_iff]
    left
    rw [sub_eq_zero]
    have h2 : exp (m * I * ((π : ℝ) : ℂ)) = exp (m * I * ((-π : ℝ) : ℂ)) * exp (m * (2 * π * I)) := by
      rw [← exp_add]; push_cast; ring_nf
    rw [h2, exp_int_mul_two_pi_mul_I, mul_one]

theorem integral_phase (m : Z3) :
    ∫ k in cube, phase k m = if m = 0 then ((2 * π) ^ 3 : ℂ) else 0 := by
  have hf : ∀ k : ℝ × ℝ × ℝ, phase k m = exp (((k.1 * m.1 : ℝ) : ℂ) * I) *
      (exp (((k.2.1 * m.2.1 : ℝ) : ℂ) * I) * exp (((k.2.2 * m.2.2 : ℝ) : ℂ) * I)) := by
    intro k; rw [phase, dot, ← exp_add, ← exp_add]; push_cast; ring_nf
  simp_rw [hf]
  have h1 := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure (ℝ × ℝ)))
    (fun x : ℝ => exp (((x * m.1 : ℝ) : ℂ) * I))
    (fun p : ℝ × ℝ => exp (((p.1 * m.2.1 : ℝ) : ℂ) * I) * exp (((p.2 * m.2.2 : ℝ) : ℂ) * I))
    (Icc (-π) π) (Icc (-π) π ×ˢ Icc (-π) π)
  have h2 := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun x : ℝ => exp (((x * m.2.1 : ℝ) : ℂ) * I))
    (fun x : ℝ => exp (((x * m.2.2 : ℝ) : ℂ) * I)) (Icc (-π) π) (Icc (-π) π)
  rw [← Measure.volume_eq_prod] at h1 h2
  rw [cube, h1, h2, integral_circle, integral_circle, integral_circle]
  obtain ⟨a, b, c⟩ := m
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0 <;> simp [ha, hb, hc] <;> ring

/-! ### Fourier coefficients of `|λ|^{2n}` are the walk counts -/

theorem integrableOn_cube {E : Type*} [NormedAddCommGroup E] {f : ℝ × ℝ × ℝ → E} (hf : Continuous f) : IntegrableOn f cube :=
  hf.continuousOn.integrableOn_compact isCompact_cube

theorem integral_phase_normSq_pow (n : ℕ) (y : Z3) :
    ∫ k in cube, phase k y * (normSq (lam k) : ℂ) ^ n =
      (2 * π) ^ 3 * (dWalks (2 * n) (false, y) (false, 0) : ℂ) := by
  induction n generalizing y with
  | zero =>
    simp only [pow_zero, mul_one, integral_phase]
    simp [dWalks]
  | succ n ih =>
    have e : ∀ k, phase k y * (normSq (lam k) : ℂ) ^ (n + 1) =
        ∑ i : Fin 4, ∑ j : Fin 4, phase k (y + (bond i - bond j)) * (normSq (lam k) : ℂ) ^ n := by
      intro k
      rw [pow_succ', normSq_lam, ← mul_assoc, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [phase_add]
    simp_rw [e]
    have hint : ∀ m : Z3, IntegrableOn (fun k => phase k m * (normSq (lam k) : ℂ) ^ n) cube :=
      fun m => integrableOn_cube ((continuous_phase m).mul
        ((continuous_ofReal.comp continuous_normSq_lam).pow n))
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint _]
    simp_rw [integral_finsetSum _ fun j _ => hint _, ih]
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, dWalks_two]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [add_sub_assoc]

/-- `(2π)⁻³ ∫ |λ|^{2n} = #closed diamond walks of length 2n`. -/
theorem integral_normSq_pow (n : ℕ) :
    ∫ k in cube, normSq (lam k) ^ n = (2 * π) ^ 3 * (dWalks (2 * n) (false, 0) (false, 0) : ℝ) := by
  have h := integral_phase_normSq_pow n 0
  simp only [phase_zero, one_mul] at h
  have h' : ((∫ k in cube, normSq (lam k) ^ n : ℝ) : ℂ) =
      (((2 * π) ^ 3 * (dWalks (2 * n) (false, 0) (false, 0) : ℝ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]; push_cast; exact h
  exact_mod_cast h'

/-! ### The manuscript integral -/

theorem greenDiamond_even :
    greenDiamond = ∑' n : ℕ, (dWalks (2 * n) (false, 0) (false, 0) : ℝ≥0∞) / 4 ^ (2 * n + 1) := by
  unfold greenDiamond
  rw [← tsum_even_add_odd (f := fun L => (dWalks L (false, 0) (false, 0) : ℝ≥0∞) / 4 ^ (L + 1))
    ENNReal.summable ENNReal.summable]
  simp [dWalks_odd]

theorem norm_one_add_exp (x : ℝ) : ‖1 + exp (x * I)‖ ^ 2 = 2 + 2 * Real.cos x := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [add_re, one_re, exp_ofReal_mul_I_re, add_im, one_im, exp_ofReal_mul_I_im, zero_add]
  nlinarith [Real.sin_sq_add_cos_sq x]

/-- Off the plane `cos k₁ = 1`, `|λ(k)|² < 16`. -/
theorem normSq_lam_lt (k : ℝ × ℝ × ℝ) (hk : Real.cos k.1 < 1) : normSq (lam k) < 16 := by
  rw [Complex.normSq_eq_norm_sq, lam_eq]
  have h1 : ‖exp (k.2.1 * I)‖ = 1 := norm_exp_ofReal_mul_I _
  have h2 : ‖exp (k.2.2 * I)‖ = 1 := norm_exp_ofReal_mul_I _
  have ha : ‖1 + exp (k.1 * I)‖ < 2 := by
    have := norm_one_add_exp k.1
    nlinarith [norm_nonneg (1 + exp (k.1 * I))]
  have htri : ‖1 + exp (k.1 * I) + exp (k.2.1 * I) + exp (k.2.2 * I)‖ < 4 := by
    calc _ ≤ ‖1 + exp (k.1 * I) + exp (k.2.1 * I)‖ + ‖exp (k.2.2 * I)‖ := norm_add_le _ _
      _ ≤ ‖1 + exp (k.1 * I)‖ + ‖exp (k.2.1 * I)‖ + ‖exp (k.2.2 * I)‖ := by
          gcongr; exact norm_add_le _ _
      _ < 4 := by rw [h1, h2]; linarith
  nlinarith [norm_nonneg (1 + exp (k.1 * I) + exp (k.2.1 * I) + exp (k.2.2 * I))]

theorem ae_cube_lt : ∀ᵐ k ∂(volume.restrict cube), normSq (lam k) < 16 := by
  have hnull : (volume : Measure (ℝ × ℝ × ℝ)) {k | k.1 = 0} = 0 := by
    have : {k : ℝ × ℝ × ℝ | k.1 = 0} = ({0} : Set ℝ) ×ˢ univ := by ext k; simp
    rw [this, Measure.volume_eq_prod, Measure.prod_prod]; simp
  have hae : ∀ᵐ k ∂(volume : Measure (ℝ × ℝ × ℝ)), k.1 ≠ 0 := measure_eq_zero_iff_ae_notMem.mp hnull
  rw [ae_restrict_iff' (isCompact_cube.measurableSet)]
  filter_upwards [hae] with k hk hkc
  apply normSq_lam_lt
  refine lt_of_le_of_ne (Real.cos_le_one _) fun h => hk ?_
  have hk1 := hkc.1
  exact (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [hk1.1, Real.pi_pos])
    (by linarith [hk1.2, Real.pi_pos])).mp h

theorem geom_expand {N : ℝ} (h0 : 0 ≤ N) (h : N < 16) :
    ENNReal.ofReal (4 / (16 - N)) = ∑' n : ℕ, ENNReal.ofReal (N ^ n / 4 ^ (2 * n + 1)) := by
  have hr : N / 16 < 1 := by rw [div_lt_one (by norm_num)]; exact h
  have hs := (hasSum_geometric_of_lt_one (by positivity) hr).mul_left (1 / 4 : ℝ)
  have e : ∀ n : ℕ, (1 / 4 : ℝ) * (N / 16) ^ n = N ^ n / 4 ^ (2 * n + 1) := fun n => by
    rw [pow_succ, pow_mul, div_pow]; norm_num; ring
  simp_rw [e] at hs
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs.summable, hs.tsum_eq]
  congr 1
  field_simp
  ring

/-- **C05-20.** The manuscript's Brillouin-zone integral equals the diamond walk series:
`(2π)⁻³ ∫_{[-π,π]³} 4 / (16 − |1 + e^{ik₁} + e^{ik₂} + e^{ik₃}|²) d³k = greenDiamond`. -/
theorem greenDiamond_eq_integral :
    greenDiamond = ENNReal.ofReal ((2 * π) ^ 3)⁻¹ *
      ∫⁻ k in cube, ENNReal.ofReal (4 / (16 - normSq (lam k))) := by
  have hmeas : ∀ n : ℕ, AEMeasurable
      (fun k => ENNReal.ofReal (normSq (lam k) ^ n / 4 ^ (2 * n + 1))) (volume.restrict cube) :=
    fun n => by
      have := continuous_normSq_lam
      exact (ENNReal.measurable_ofReal.comp (by fun_prop :
        Continuous fun k => normSq (lam k) ^ n / 4 ^ (2 * n + 1)).measurable).aemeasurable
  have hcongr : (fun k => ENNReal.ofReal (4 / (16 - normSq (lam k)))) =ᵐ[volume.restrict cube]
      fun k => ∑' n : ℕ, ENNReal.ofReal (normSq (lam k) ^ n / 4 ^ (2 * n + 1)) := by
    filter_upwards [ae_cube_lt] with k hk
    exact geom_expand (normSq_nonneg _) hk
  rw [lintegral_congr_ae hcongr, lintegral_tsum hmeas, ← ENNReal.tsum_mul_left, greenDiamond_even]
  refine tsum_congr fun n => ?_
  have hc : Continuous fun k => normSq (lam k) ^ n / 4 ^ (2 * n + 1) := by
    have := continuous_normSq_lam; fun_prop
  have hint : Integrable (fun k => normSq (lam k) ^ n / 4 ^ (2 * n + 1)) (volume.restrict cube) :=
    integrableOn_cube hc
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun k => div_nonneg (pow_nonneg (normSq_nonneg _) _) (by positivity)),
    integral_div, integral_normSq_pow, ← ENNReal.ofReal_mul (by positivity), div_four_pow]
  congr 1
  have : (0 : ℝ) < (2 * π) ^ 3 := by positivity
  field_simp

end Entropic.DiamondGreen
