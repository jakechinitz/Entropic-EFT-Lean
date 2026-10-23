import Entropic.Main.Core
import Entropic.GalacticLaw
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Topology.ContinuousMap.CocompactMap
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Chunk 14 sweep: Gaussian and Fourier integrals for deferred claims
(C07-54, C01-56, C09-28, C12-37, C12-39, C08-67, C08-89). -/

noncomputable section
namespace Entropic.Sweep.Ana
open Real MeasureTheory Complex Filter Topology
open scoped FourierTransform

/-! ### C07-54, C01-56: the Hubbard–Stratonovich representation in ℝ³ -/

/-- C07-54, C01-56: for η ≥ 0 and C ∈ ℝ³,
∫_{ℝ³} (2π)^{−3/2} exp(−|ξ|²/2 + i√η ξ·C) d³ξ = exp(−η|C|²/2). -/
theorem gaussian_representation_3d (η : ℝ) (hη : 0 ≤ η) (C : Fin 3 → ℝ) :
    ∫ ξ : Fin 3 → ℝ, ((((2 * π) ^ (-(3:ℝ)/2) : ℝ)) : ℂ) *
        cexp (-(1/2 : ℂ) * ∑ i, (ξ i : ℂ) ^ 2 + ∑ i, (I * (Real.sqrt η : ℂ) * C i) * ξ i) =
      cexp (-(η : ℂ) * (∑ i, (C i : ℂ) ^ 2) / 2) := by
  rw [integral_const_mul, GaussianFourier.integral_cexp_neg_mul_sum_add (by norm_num : (0:ℝ) < (1/2 : ℂ).re)]
  have hs : ∑ i, (I * (Real.sqrt η : ℂ) * C i) ^ 2 = -(η : ℂ) * ∑ i, (C i : ℂ) ^ 2 := by
    rw [Finset.mul_sum]; congr 1; ext i
    rw [mul_pow, mul_pow, I_sq, ← ofReal_pow, Real.sq_sqrt hη]; ring
  rw [hs, Fintype.card_fin]
  have h2 : ((π : ℂ) / (1/2)) ^ ((3:ℕ) / 2 : ℂ) = (((2 * π) ^ ((3:ℝ)/2) : ℝ) : ℂ) := by
    rw [ofReal_cpow (by positivity)]; push_cast; ring_nf
  rw [h2, show (-(η : ℂ) * ∑ i, (C i : ℂ) ^ 2) / (4 * (1/2)) = -(η : ℂ) * (∑ i, (C i : ℂ) ^ 2) / 2 by ring,
    ← mul_assoc]
  have h3 : (((2 * π) ^ (-(3:ℝ)/2) : ℝ) : ℂ) * (((2 * π) ^ ((3:ℝ)/2) : ℝ) : ℂ) = 1 := by
    rw [← ofReal_mul, ← Real.rpow_add (by positivity)]; norm_num
  rw [h3, one_mul]

/-- C07-54 (amplitude): A_*(b) = Z^{−1/2} e^{−η K²/2} gives |A_*(b)|² = e^{−ηK²}/Z = p_*(b). -/
theorem amplitude_sq (Z η K2 : ℝ) (hZ : 0 < Z) :
    (Z ^ (-(1:ℝ)/2) * Real.exp (-(η / 2) * K2)) ^ 2 = Real.exp (-η * K2) / Z := by
  rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hZ.le, ← Real.exp_nat_mul]
  norm_num
  rw [Real.rpow_neg_one, div_eq_mul_inv, mul_comm]; congr 2; ring

/-! ### C09-28: Gaussian first-moment bridge identity -/

def gexp (s x : ℝ) : ℂ := cexp (-(1/2 : ℂ) * (x : ℂ) ^ 2 + (I * s) * x)

/-- One-dimensional first moment: ∫ x e^{−x²/2 + isx} dx = is ∫ e^{−x²/2 + isx} dx. -/
theorem moment_1d (s : ℝ) : ∫ x : ℝ, (x : ℂ) * gexp s x = (I * s) * ∫ x : ℝ, gexp s x := by
  have hf : Integrable (gexp s) := by
    have := integrable_cexp_quadratic (by norm_num : (0:ℝ) < (1/2 : ℂ).re) (I * s) 0
    refine this.congr (ae_of_all _ (fun x => ?_))
    simp only [gexp, add_zero]
  have hcont : Continuous (gexp s) := by unfold gexp; fun_prop
  have hxf : Integrable (fun x : ℝ => (x : ℂ) * gexp s x) := by
    have hb := (integrable_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)).norm
    refine hb.mono' ((continuous_ofReal.mul hcont).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    simp only [gexp, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    apply le_of_eq; congr 2
    simp [Complex.add_re, Complex.mul_re, sq]
  have hd : ∀ x : ℝ, HasDerivAt (gexp s) ((-(x : ℂ) + I * s) * gexp s x) x := by
    intro x
    have a := (hasDerivAt_pow 2 (x : ℂ)).const_mul (-(1/2 : ℂ))
    have b := (hasDerivAt_id' (x : ℂ)).const_mul (I * (s : ℂ))
    have h1 : HasDerivAt (fun y : ℂ => -(1/2 : ℂ) * y ^ 2 + (I * s) * y) (-(x : ℂ) + I * s) (x : ℂ) :=
      (a.add b).congr_deriv (by norm_num; ring)
    have := (h1.cexp).comp_ofReal
    exact this.congr_deriv (mul_comm _ _)
  have hsplit : (fun x : ℝ => (-(x : ℂ) + I * s) * gexp s x) =
      fun x : ℝ => (I * s) * gexp s x - (x : ℂ) * gexp s x := by
    ext x; ring
  have hderiv_int : Integrable (fun x : ℝ => (-(x : ℂ) + I * s) * gexp s x) := by
    rw [hsplit]; exact (hf.const_mul _).sub hxf
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable hd hderiv_int hf
  rw [hsplit, integral_sub (hf.const_mul _) hxf, integral_const_mul] at h0
  linear_combination -h0

/-- C09-28: for a ∈ {1,2,3} and s = √η C,
∫ ξ_a exp(−|ξ|²/2 + i s·ξ) d³ξ = i s_a ∫ exp(−|ξ|²/2 + i s·ξ) d³ξ. -/
theorem gaussian_first_moment (s : Fin 3 → ℝ) (a : Fin 3) :
    ∫ ξ : Fin 3 → ℝ, (ξ a : ℂ) * ∏ i, cexp (-(1/2 : ℂ) * (ξ i) ^ 2 + (I * s i) * ξ i) =
      (I * s a) * ∫ ξ : Fin 3 → ℝ, ∏ i, cexp (-(1/2 : ℂ) * (ξ i) ^ 2 + (I * s i) * ξ i) := by
  set e : Fin 3 → ℝ → ℂ := fun i x => gexp (s i) x
  set h : Fin 3 → ℝ → ℂ := fun i x => (if i = a then (x : ℂ) else 1) * e i x
  have hprod : ∀ ξ : Fin 3 → ℝ, (ξ a : ℂ) * ∏ i, e i (ξ i) = ∏ i, h i (ξ i) := by
    intro ξ
    simp only [h, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite_eq' Finset.univ a (fun i => (ξ i : ℂ))]; simp
  have lhs : ∫ ξ : Fin 3 → ℝ, (ξ a : ℂ) * ∏ i, e i (ξ i) = ∏ i, ∫ x, h i x := by
    simp_rw [hprod]; exact integral_fintype_prod_volume_eq_prod h
  have rhs : ∫ ξ : Fin 3 → ℝ, ∏ i, e i (ξ i) = ∏ i, ∫ x, e i x := integral_fintype_prod_volume_eq_prod e
  have hi : ∀ i, ∫ x, h i x = (if i = a then I * s a else 1) * ∫ x, e i x := by
    intro i
    by_cases hia : i = a
    · subst hia; simp only [h, ite_true, e]; exact moment_1d (s i)
    · simp only [h, hia, ite_false, one_mul]
  show ∫ ξ : Fin 3 → ℝ, (ξ a : ℂ) * ∏ i, e i (ξ i) = (I * s a) * ∫ ξ : Fin 3 → ℝ, ∏ i, e i (ξ i)
  rw [lhs, rhs]
  simp_rw [hi, Finset.prod_mul_distrib]
  rw [Finset.prod_ite_eq' Finset.univ a (fun _ => I * (s a : ℂ))]
  simp

/-! ### C12-37: two-pole retarded kernel -/

/-- χ^R(t) = −χ₀ (γΩ/(Ω − γ))(e^{−γt} − e^{−Ωt}) for t > 0 and 0 for t ≤ 0. -/
def chiR (χ0 γ Ω t : ℝ) : ℝ :=
  if 0 < t then -χ0 * (γ * Ω / (Ω - γ)) * (Real.exp (-γ * t) - Real.exp (-Ω * t)) else 0

/-- C12-37 (causality): χ^R(t) = 0 for t < 0. -/
theorem chiR_causal (χ0 γ Ω t : ℝ) (ht : t < 0) : chiR χ0 γ Ω t = 0 := by
  simp [chiR, not_lt.mpr ht.le]

theorem laplace_exp (γ ω : ℝ) (hγ : 0 < γ) :
    ∫ t in Set.Ioi (0:ℝ), cexp ((-γ + ω * I) * t) = 1 / (γ - ω * I) := by
  rw [integral_exp_mul_complex_Ioi (by simp [hγ]) 0]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show (-(γ:ℂ) + ω * I) = -((γ:ℂ) - ω * I) by ring, div_neg, neg_div, neg_neg]

/-- C12-37 (forward transform): ∫₀^∞ χ^R(t) e^{iωt} dt = −χ₀γΩ/((γ − iω)(Ω − iω)) for 0 < γ < Ω, i.e.
the time kernel transforms to the two-pole susceptibility of C12-36. -/
theorem chiR_transform (χ0 γ Ω ω : ℝ) (hγ : 0 < γ) (hγΩ : γ < Ω) :
    ∫ t in Set.Ioi (0:ℝ), (chiR χ0 γ Ω t : ℂ) * cexp (ω * I * t) =
      -(χ0 : ℂ) * γ * Ω / ((γ - ω * I) * (Ω - ω * I)) := by
  have hΩ : 0 < Ω := hγ.trans hγΩ
  have hne : (Ω : ℂ) - γ ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have e : ∀ t ∈ Set.Ioi (0:ℝ), (chiR χ0 γ Ω t : ℂ) * cexp (ω * I * t) =
      (-(χ0 : ℂ) * (γ * Ω / (Ω - γ))) * (cexp ((-γ + ω * I) * t) - cexp ((-Ω + ω * I) * t)) := by
    intro t ht
    simp only [chiR, if_pos (show (0:ℝ) < t from ht)]
    push_cast
    rw [mul_sub, sub_mul]
    simp only [mul_assoc, ← Complex.exp_add]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
    integral_sub (integrableOn_exp_mul_complex_Ioi (by simp [hγ]) 0)
      (integrableOn_exp_mul_complex_Ioi (by simp [hΩ]) 0),
    laplace_exp γ ω hγ, laplace_exp Ω ω hΩ]
  have h1 : (γ : ℂ) - ω * I ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : (Ω : ℂ) - ω * I ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  field_simp; ring

/-- C12-37 (coincident limit): γΩ(e^{−γt} − e^{−Ωt})/(Ω − γ) → γ² t e^{−γt} as Ω → γ. -/
theorem chiR_coincident (γ t : ℝ) :
    Tendsto (fun Ω : ℝ => γ * Ω * (Real.exp (-γ * t) - Real.exp (-Ω * t)) / (Ω - γ)) (𝓝[≠] γ)
      (𝓝 (γ ^ 2 * t * Real.exp (-γ * t))) := by
  have hd : HasDerivAt (fun Ω : ℝ => Real.exp (-Ω * t)) (Real.exp (-γ * t) * (-1 * t)) γ :=
    ((hasDerivAt_neg γ).mul_const t).exp
  have hs := hd.tendsto_slope
  have hs' : Tendsto (fun Ω : ℝ => (Real.exp (-γ * t) - Real.exp (-Ω * t)) / (Ω - γ)) (𝓝[≠] γ)
      (𝓝 (t * Real.exp (-γ * t))) := by
    have h2 := hs.neg
    rw [show -(Real.exp (-γ * t) * (-1 * t)) = t * Real.exp (-γ * t) by ring] at h2
    refine h2.congr' (Eventually.of_forall fun Ω => ?_)
    simp only [slope_def_field]; ring
  have hg : Tendsto (fun Ω : ℝ => γ * Ω) (𝓝[≠] γ) (𝓝 (γ * γ)) :=
    ((continuous_const.mul continuous_id).tendsto γ).mono_left nhdsWithin_le_nhds
  have := hg.mul hs'
  rw [show γ ^ 2 * t * Real.exp (-γ * t) = γ * γ * (t * Real.exp (-γ * t)) by ring]
  refine this.congr' (Eventually.of_forall fun Ω => ?_)
  simp only; ring

/-- C12-37 (poles): (γ − iω)(Ω − iω) = 0 iff ω = −iγ or ω = −iΩ; both lie in the lower half-plane. -/
theorem chiR_poles (γ Ω : ℝ) (ω : ℂ) :
    ((γ : ℂ) - I * ω) * ((Ω : ℂ) - I * ω) = 0 ↔ ω = -I * γ ∨ ω = -I * Ω := by
  have k : ∀ c : ℂ, c - I * ω = 0 ↔ ω = -I * c := by
    intro c; constructor
    · intro h; have : ω = c / I := by field_simp; linear_combination -h
      rw [this, div_I]; ring
    · intro h; rw [h]; ring_nf; rw [I_sq]; ring
  rw [mul_eq_zero, k, k]

/-! ### C12-39: static sum rule -/

theorem integral_partial (γ Ω : ℝ) (hγ : 0 < γ) (hΩ : 0 < Ω) (hne : γ ≠ Ω) :
    ∫ ω : ℝ, 1 / ((γ ^ 2 + ω ^ 2) * (Ω ^ 2 + ω ^ 2)) = π / (γ * Ω * (γ + Ω)) := by
  have hpf : (fun ω : ℝ => 1 / ((γ ^ 2 + ω ^ 2) * (Ω ^ 2 + ω ^ 2))) =
      fun ω => (1 / (Ω ^ 2 - γ ^ 2)) * (1 / (γ ^ 2 + ω ^ 2)) - (1 / (Ω ^ 2 - γ ^ 2)) * (1 / (Ω ^ 2 + ω ^ 2)) := by
    ext ω
    have h1 : Ω ^ 2 - γ ^ 2 ≠ 0 := by
      intro h; have : (Ω - γ) * (Ω + γ) = 0 := by ring_nf; linarith
      rcases mul_eq_zero.mp this with h | h
      · exact hne (by linarith)
      · linarith
    field_simp; ring
  have i1 : Integrable (fun ω : ℝ => 1 / (γ ^ 2 + ω ^ 2)) := by
    by_contra hc; have := Entropic.GalacticLaw.integral_inv_sq_add_sq hγ
    rw [integral_undef hc] at this; exact (by positivity : (0:ℝ) < π / γ).ne this
  have i2 : Integrable (fun ω : ℝ => 1 / (Ω ^ 2 + ω ^ 2)) := by
    by_contra hc; have := Entropic.GalacticLaw.integral_inv_sq_add_sq hΩ
    rw [integral_undef hc] at this; exact (by positivity : (0:ℝ) < π / Ω).ne this
  rw [hpf, integral_sub (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
    Entropic.GalacticLaw.integral_inv_sq_add_sq hγ, Entropic.GalacticLaw.integral_inv_sq_add_sq hΩ]
  have h1 : Ω - γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have h2 : Ω ^ 2 - γ ^ 2 = (Ω - γ) * (Ω + γ) := by ring
  rw [h2]; field_simp; ring

theorem tendsto_rat_zero (a : ℝ) (l : Filter ℝ) (hl : Tendsto (fun x : ℝ => |x|) l atTop) :
    Tendsto (fun x : ℝ => x / (a ^ 2 + x ^ 2)) l (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => |x|⁻¹) l (𝓝 0) := tendsto_inv_atTop_zero.comp hl
  have h2 : ∀ᶠ x in l, ‖x / (a ^ 2 + x ^ 2)‖ ≤ |x|⁻¹ := by
    filter_upwards [hl.eventually_gt_atTop 0] with x hx
    have hp : 0 < a ^ 2 + x ^ 2 := by
      have : 0 < |x| ^ 2 := pow_pos hx 2
      rw [sq_abs] at this; nlinarith [sq_nonneg a]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hp]
    rw [div_le_iff₀ hp, ← sq_abs x]
    have : |x| ^ 2 ≤ a ^ 2 + |x| ^ 2 := by nlinarith [sq_nonneg a]
    calc |x| = |x|⁻¹ * |x| ^ 2 := by field_simp
      _ ≤ |x|⁻¹ * (a ^ 2 + |x| ^ 2) := by gcongr
  exact squeeze_zero_norm' h2 h1

/-- ∫_ℝ (a² + x²)⁻² dx = π/(2a³) for a > 0. -/
theorem integral_inv_sq_sq {a : ℝ} (ha : 0 < a) : ∫ x : ℝ, 1 / (a ^ 2 + x ^ 2) ^ 2 = π / (2 * a ^ 3) := by
  set F : ℝ → ℝ := fun x => x / (2 * a ^ 2 * (a ^ 2 + x ^ 2)) + Real.arctan (x / a) / (2 * a ^ 3)
  have hd : ∀ x, HasDerivAt F (1 / (a ^ 2 + x ^ 2) ^ 2) x := by
    intro x
    have hpos : 0 < a ^ 2 + x ^ 2 := by positivity
    have h1 : HasDerivAt (fun x : ℝ => x / (2 * a ^ 2 * (a ^ 2 + x ^ 2)))
        ((1 * (2 * a ^ 2 * (a ^ 2 + x ^ 2)) - x * (2 * a ^ 2 * (2 * x))) / (2 * a ^ 2 * (a ^ 2 + x ^ 2)) ^ 2) x := by
      apply (hasDerivAt_id x).div
      · have := ((hasDerivAt_id x).pow 2).const_add (a ^ 2) |>.const_mul (2 * a ^ 2)
        convert this using 1 <;> simp [id] <;> ring
      · positivity
    have h2 : HasDerivAt (fun x : ℝ => Real.arctan (x / a) / (2 * a ^ 3))
        (1 / (1 + (x / a) ^ 2) * (1 / a) / (2 * a ^ 3)) x := by
      have := ((hasDerivAt_id x).div_const a).arctan
      convert this.div_const (2 * a ^ 3) using 1 <;> simp [id]
    convert h1.add h2 using 1
    field_simp; ring
  have hint : Integrable (fun x : ℝ => 1 / (a ^ 2 + x ^ 2) ^ 2) := by
    have i1 : Integrable (fun x : ℝ => (a ^ 2)⁻¹ * (1 / (a ^ 2 + x ^ 2))) := by
      have : Integrable (fun x : ℝ => 1 / (a ^ 2 + x ^ 2)) := by
        by_contra hc; have := Entropic.GalacticLaw.integral_inv_sq_add_sq ha
        rw [integral_undef hc] at this; exact (by positivity : (0:ℝ) < π / a).ne this
      exact this.const_mul _
    refine i1.mono' (continuous_const.div (by fun_prop) (fun x => by positivity)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have hpos : 0 < a ^ 2 + x ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [sq_nonneg x]
  have hbot : Tendsto F atBot (𝓝 (0 + (-(π / 2)) / (2 * a ^ 3))) := by
    apply Tendsto.add
    · have := tendsto_rat_zero a atBot (tendsto_abs_atBot_atTop)
      have h := this.div_const (2 * a ^ 2)
      simp only [zero_div] at h
      refine h.congr (fun x => ?_); field_simp
    · apply Tendsto.div_const
      exact Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds |>.comp
        (tendsto_id.atBot_div_const ha)
  have htop : Tendsto F atTop (𝓝 (0 + (π / 2) / (2 * a ^ 3))) := by
    apply Tendsto.add
    · have := tendsto_rat_zero a atTop (tendsto_abs_atTop_atTop)
      have h := this.div_const (2 * a ^ 2)
      simp only [zero_div] at h
      refine h.congr (fun x => ?_); field_simp
    · apply Tendsto.div_const
      exact Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds |>.comp
        (tendsto_id.atTop_div_const ha)
  rw [integral_of_hasDerivAt_of_tendsto hd hint hbot htop]
  field_simp; ring

/-- ∫_ℝ dω/((γ² + ω²)(Ω² + ω²)) = π/(γΩ(γ + Ω)) for all γ, Ω > 0. -/
theorem integral_two_pole (γ Ω : ℝ) (hγ : 0 < γ) (hΩ : 0 < Ω) :
    ∫ ω : ℝ, 1 / ((γ ^ 2 + ω ^ 2) * (Ω ^ 2 + ω ^ 2)) = π / (γ * Ω * (γ + Ω)) := by
  rcases eq_or_ne γ Ω with h | h
  · subst h
    have : (fun ω : ℝ => 1 / ((γ ^ 2 + ω ^ 2) * (γ ^ 2 + ω ^ 2))) = fun ω => 1 / (γ ^ 2 + ω ^ 2) ^ 2 := by
      ext ω; ring
    rw [this, integral_inv_sq_sq hγ]; field_simp; ring
  · exact integral_partial γ Ω hγ hΩ h

/-- C12-38/39: D(ω)/ω = χ₀γΩ(γ+Ω)/((γ²+ω²)(Ω²+ω²)) and (2/π)∫₀^∞ D(ω)/ω dω = χ₀ for all γ, Ω > 0
(including the coincident case γ = Ω). -/
theorem static_sum_rule (χ0 γ Ω : ℝ) (hγ : 0 < γ) (hΩ : 0 < Ω) :
    2 / π * ∫ ω in Set.Ioi (0:ℝ), χ0 * γ * Ω * (γ + Ω) / ((γ ^ 2 + ω ^ 2) * (Ω ^ 2 + ω ^ 2)) = χ0 := by
  have hev := integral_comp_abs (f := fun ω : ℝ => χ0 * γ * Ω * (γ + Ω) / ((γ ^ 2 + ω ^ 2) * (Ω ^ 2 + ω ^ 2)))
  simp only [sq_abs] at hev
  have hfull : ∫ ω : ℝ, χ0 * γ * Ω * (γ + Ω) / ((γ ^ 2 + ω ^ 2) * (Ω ^ 2 + ω ^ 2)) = χ0 * π := by
    have : (fun ω : ℝ => χ0 * γ * Ω * (γ + Ω) / ((γ ^ 2 + ω ^ 2) * (Ω ^ 2 + ω ^ 2))) =
        fun ω => (χ0 * γ * Ω * (γ + Ω)) * (1 / ((γ ^ 2 + ω ^ 2) * (Ω ^ 2 + ω ^ 2))) := by ext; ring
    rw [this, integral_const_mul, integral_two_pole γ Ω hγ hΩ]
    have : γ * Ω * (γ + Ω) ≠ 0 := by positivity
    field_simp
  rw [hfull] at hev
  have : ∫ ω in Set.Ioi (0:ℝ), χ0 * γ * Ω * (γ + Ω) / ((γ ^ 2 + ω ^ 2) * (Ω ^ 2 + ω ^ 2)) = χ0 * π / 2 := by
    linarith
  rw [this]; field_simp

/-! ### C08-67: Euclidean TT covariance, temporal transform -/

/-- C08-67 (forward transform): for a > 0, ∫_ℝ e^{−a|τ|} e^{−iωτ} dτ = 2a/(a² + ω²); with a = c|k| and
prefactor c/(2Z_G|k|) this is (c²/Z_G)/(ω² + c²|k|²). -/
theorem two_sided_transform (a ω : ℝ) (ha : 0 < a) :
    ∫ τ : ℝ, (Real.exp (-a * |τ|) : ℂ) * cexp (-(ω * I * τ)) = 2 * a / (a ^ 2 + ω ^ 2) := by
  have hR : ∫ τ in Set.Ioi (0:ℝ), (Real.exp (-a * |τ|) : ℂ) * cexp (-(ω * I * τ)) = 1 / (a + ω * I) := by
    have e : ∀ τ ∈ Set.Ioi (0:ℝ), (Real.exp (-a * |τ|) : ℂ) * cexp (-(ω * I * τ)) = cexp ((-a + -ω * I) * τ) := by
      intro τ hτ; rw [abs_of_pos hτ]; push_cast; rw [← Complex.exp_add]; ring_nf
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_exp_mul_complex_Ioi (by simp [ha]) 0]
    simp only [ofReal_zero, mul_zero, Complex.exp_zero]
    rw [show (-(a:ℂ) + -ω * I) = -((a:ℂ) + ω * I) by ring, div_neg, neg_div, neg_neg]
  have eL : ∀ τ ∈ Set.Iic (0:ℝ), (Real.exp (-a * |τ|) : ℂ) * cexp (-(ω * I * τ)) = cexp (((a:ℂ) + -ω * I) * τ) := by
    intro τ hτ; rw [abs_of_nonpos hτ]; push_cast; rw [← Complex.exp_add]; ring_nf
  have hL : ∫ τ in Set.Iic (0:ℝ), (Real.exp (-a * |τ|) : ℂ) * cexp (-(ω * I * τ)) = 1 / (a - ω * I) := by
    rw [setIntegral_congr_fun measurableSet_Iic eL, integral_exp_mul_complex_Iic (by simp [ha]) 0]
    simp only [ofReal_zero, mul_zero, Complex.exp_zero]; congr 1; ring
  have intR : IntegrableOn (fun τ : ℝ => (Real.exp (-a * |τ|) : ℂ) * cexp (-(ω * I * τ))) (Set.Ioi 0) := by
    refine (integrableOn_exp_mul_complex_Ioi (a := -a + -ω * I) (by simp [ha]) 0).congr_fun (fun τ hτ => ?_)
      measurableSet_Ioi
    rw [abs_of_pos hτ]; push_cast; rw [← Complex.exp_add]; ring_nf
  have intL : IntegrableOn (fun τ : ℝ => (Real.exp (-a * |τ|) : ℂ) * cexp (-(ω * I * τ))) (Set.Iic 0) :=
    (integrableOn_exp_mul_complex_Iic (a := a + -ω * I) (by simp [ha]) 0).congr_fun
      (fun τ hτ => (eL τ hτ).symm) measurableSet_Iic
  rw [← intervalIntegral.integral_Iic_add_Ioi intL intR, hL, hR]
  have h1 : (a : ℂ) - ω * I ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : (a : ℂ) + ω * I ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have h3 : (a : ℂ) ^ 2 + ω ^ 2 ≠ 0 := by
    have : (0:ℝ) < a ^ 2 + ω ^ 2 := by positivity
    exact_mod_cast this.ne'
  field_simp
  ring_nf; rw [I_sq]; ring

/-! ### C08-89: h_fg ∈ C₀ -/

/-- C08-89: for Schwartz f, g on ℝ, h_fg(λ) = conj(f̂(−λ)) ĝ(−λ) is continuous and vanishes at infinity. -/
theorem hfg_C0 (f g : SchwartzMap ℝ ℂ) :
    ∃ h : ZeroAtInftyContinuousMap ℝ ℂ, ∀ l : ℝ, h l = starRingEnd ℂ (𝓕 f (-l)) * 𝓕 g (-l) := by
  let F : ZeroAtInftyContinuousMap ℝ ℂ := (𝓕 f).toZeroAtInfty
  let G : ZeroAtInftyContinuousMap ℝ ℂ := (𝓕 g).toZeroAtInfty
  refine ⟨(star F * G).comp (Homeomorph.neg ℝ).toCocompactMap, fun l => ?_⟩
  rfl

end Entropic.Sweep.Ana
