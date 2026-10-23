import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-! Spherical galactic law (main manuscript Sec. 15):
    g_obs = g_bar / (1 - exp(-√(g_bar/a₀))) = g_bar [1 + n_B(√(g_bar/a₀))].
The law applies to admissible carriers (nonnegative retained stock below the
cap, App. O.3); that admissibility is a premise of its physical use and is not
re-derived here. Everything below is exact mathematics of the stated law. -/

noncomputable section
namespace Entropic.GalacticLaw
open Real Filter Topology Set

def gObs (a₀ g : ℝ) : ℝ := g / (1 - exp (-Real.sqrt (g / a₀)))

/-! ### Elementary exponential inequalities in x = √(g/a₀) -/

theorem one_sub_exp_neg_pos {x : ℝ} (hx : 0 < x) : 0 < 1 - exp (-x) := by
  have : exp (-x) < exp 0 := exp_lt_exp.mpr (by linarith)
  rw [exp_zero] at this; linarith

/-- (1+x)e^{-x} ≤ 1. -/
theorem upper_core (x : ℝ) : (1 + x) * exp (-x) ≤ 1 := by
  have h := add_one_le_exp x
  have hp := exp_pos x
  rw [exp_neg]; rw [mul_inv_le_iff₀ hp]; linarith

/-- (2-x)eˣ ≤ 2+x for x ≥ 0. -/
theorem lower_core {x : ℝ} (hx : 0 ≤ x) : (2 - x) * exp x ≤ 2 + x := by
  let h : ℝ → ℝ := fun t => (2 + t) - (2 - t) * exp t
  have hd : ∀ t, HasDerivAt h (1 - (1 - t) * exp t) t := by
    intro t
    have := ((hasDerivAt_id t).const_add 2).fun_sub (((hasDerivAt_id t).const_sub 2).fun_mul (hasDerivAt_exp t))
    convert this using 1
    · rfl
    · simp; ring
  have hmono : MonotoneOn h (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
    · intro t _
      rw [(hd t).deriv]
      have := upper_core (-t)
      rw [neg_neg] at this
      nlinarith [exp_pos t]
  have := hmono (self_mem_Ici) (mem_Ici.mpr hx) hx
  simp only [h, exp_zero] at this
  linarith

/-- Scaled form: x/(1-e^{-x}) lies between 1 + x/2 and 1 + x, for x > 0. -/
theorem ratio_bounds {x : ℝ} (hx : 0 < x) :
    1 + x/2 ≤ x / (1 - exp (-x)) ∧ x / (1 - exp (-x)) ≤ 1 + x := by
  have hd := one_sub_exp_neg_pos hx
  constructor
  · rw [le_div_iff₀ hd]
    have h := lower_core hx.le
    have he : exp (-x) * exp x = 1 := by rw [← exp_add]; simp
    have hpos := exp_pos (-x)
    nlinarith [mul_le_mul_of_nonneg_left h hpos.le]
  · rw [div_le_iff₀ hd]
    have := upper_core x
    nlinarith

/-! ### Exact sandwich for the observed acceleration -/

theorem sqrt_facts {a₀ g : ℝ} (ha : 0 < a₀) (hg : 0 < g) :
    0 < Real.sqrt (g / a₀) ∧ a₀ * Real.sqrt (g / a₀) ^ 2 = g ∧
      a₀ * Real.sqrt (g / a₀) = Real.sqrt (a₀ * g) := by
  have hq : 0 < g / a₀ := div_pos hg ha
  refine ⟨Real.sqrt_pos.mpr hq, ?_, ?_⟩
  · rw [Real.sq_sqrt hq.le]; field_simp
  · rw [show a₀ * g = a₀ ^ 2 * (g / a₀) by field_simp <;> ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq ha.le]

theorem gObs_eq_x {a₀ g : ℝ} (ha : 0 < a₀) (hg : 0 < g) :
    gObs a₀ g = (a₀ * Real.sqrt (g / a₀)) *
      (Real.sqrt (g / a₀) / (1 - exp (-Real.sqrt (g / a₀)))) := by
  obtain ⟨hx, h2, -⟩ := sqrt_facts ha hg
  unfold gObs
  generalize Real.sqrt (g / a₀) = s at *
  subst h2; ring

/-- The law is sandwiched exactly, for every g_bar > 0:
    max(g_bar, √(a₀ g_bar) + g_bar/2) ≤ g_obs ≤ g_bar + √(a₀ g_bar). -/
theorem gObs_sandwich {a₀ g : ℝ} (ha : 0 < a₀) (hg : 0 < g) :
    g ≤ gObs a₀ g ∧ Real.sqrt (a₀ * g) + g / 2 ≤ gObs a₀ g ∧
      gObs a₀ g ≤ g + Real.sqrt (a₀ * g) := by
  obtain ⟨hx, h2, h3⟩ := sqrt_facts ha hg
  obtain ⟨r1, r2⟩ := ratio_bounds hx
  rw [gObs_eq_x ha hg, ← h3]
  generalize Real.sqrt (g / a₀) = s at *
  subst h2
  have hA : 0 < a₀ * s := mul_pos ha hx
  have hd := one_sub_exp_neg_pos hx
  have r0 : s ≤ s / (1 - exp (-s)) := by
    rw [le_div_iff₀ hd]; nlinarith [exp_pos (-s)]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left r0 hA.le]
  · nlinarith [mul_le_mul_of_nonneg_left r1 hA.le]
  · nlinarith [mul_le_mul_of_nonneg_left r2 hA.le]

/-- The thermal (Bose) form: g_obs = g_bar (1 + n_B(x)), n_B = 1/(eˣ-1). -/
theorem gObs_thermal {a₀ g : ℝ} (ha : 0 < a₀) (hg : 0 < g) :
    gObs a₀ g = g * (1 + 1 / (exp (Real.sqrt (g / a₀)) - 1)) := by
  obtain ⟨hx, -, -⟩ := sqrt_facts ha hg
  unfold gObs
  generalize Real.sqrt (g / a₀) = s at *
  have h1 : exp s - 1 ≠ 0 := by have := add_one_le_exp s; linarith
  have he := exp_pos s
  rw [exp_neg]
  have h2 : 1 - (exp s)⁻¹ = (exp s - 1) / exp s := by field_simp
  rw [h2]; field_simp; ring

/-! ### Strict monotonicity: the radial-acceleration relation is invertible -/

def k (x : ℝ) : ℝ := x ^ 2 / (1 - exp (-x))

theorem k_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt k ((2 * x * (1 - exp (-x)) - x ^ 2 * exp (-x)) / (1 - exp (-x)) ^ 2) x := by
  have hd := one_sub_exp_neg_pos hx
  have h1 : HasDerivAt (fun t => 1 - exp (-t)) (exp (-x)) x := by
    have := ((hasDerivAt_neg x).exp).const_sub 1
    convert this using 1; ring
  have := ((hasDerivAt_pow 2 x)).fun_div h1 hd.ne'
  convert this using 1
  · rfl
  · push_cast; ring

theorem k_strictMonoOn : StrictMonoOn k (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · exact fun x hx => (k_hasDerivAt hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx0 : (0:ℝ) < x := hx
    rw [(k_hasDerivAt hx).deriv]
    have hd := one_sub_exp_neg_pos hx
    apply div_pos _ (by positivity)
    -- (1+x)e^{-x} ≤ 1 gives 1 - e^{-x} ≥ x e^{-x}, so the numerator is ≥ x² e^{-x} > 0
    have hu := upper_core x
    have hp := exp_pos (-x)
    have hxE : x * exp (-x) ≤ 1 - exp (-x) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hxE (by linarith : (0:ℝ) ≤ 2 * x), mul_pos (mul_pos hx0 hx0) hp]

theorem gObs_eq_k {a₀ g : ℝ} (ha : 0 < a₀) (hg : 0 < g) : gObs a₀ g = a₀ * k (Real.sqrt (g / a₀)) := by
  obtain ⟨-, h2, -⟩ := sqrt_facts ha hg
  unfold gObs k
  generalize Real.sqrt (g / a₀) = s at *
  subst h2; ring

theorem gObs_strictMonoOn {a₀ : ℝ} (ha : 0 < a₀) : StrictMonoOn (gObs a₀) (Ioi 0) := by
  intro g₁ h₁ g₂ h₂ hlt
  rw [gObs_eq_k ha h₁, gObs_eq_k ha h₂]
  apply mul_lt_mul_of_pos_left _ ha
  apply k_strictMonoOn (Real.sqrt_pos.mpr (div_pos h₁ ha)) (Real.sqrt_pos.mpr (div_pos h₂ ha))
  exact Real.sqrt_lt_sqrt (div_pos h₁ ha).le (div_lt_div_of_pos_right hlt ha)

/-! ### Limits -/

/-- Deep regime: g_obs / √(a₀ g_bar) → 1 as g_bar → 0⁺. -/
theorem deep_limit {a₀ : ℝ} (ha : 0 < a₀) :
    Tendsto (fun g => gObs a₀ g / Real.sqrt (a₀ * g)) (𝓝[>] 0) (𝓝 1) := by
  have hx : Tendsto (fun g => Real.sqrt (g / a₀)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun g => Real.sqrt (g / a₀)) (𝓝 0) (𝓝 (Real.sqrt (0 / a₀))) :=
      ((continuous_id.div_const a₀).sqrt).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hlo : Tendsto (fun g => 1 + Real.sqrt (g / a₀) / 2) (𝓝[>] 0) (𝓝 1) := by
    simpa using (hx.div_const 2).const_add 1
  have hhi : Tendsto (fun g => 1 + Real.sqrt (g / a₀)) (𝓝[>] 0) (𝓝 1) := by
    simpa using hx.const_add 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_ <;>
  · filter_upwards [self_mem_nhdsWithin] with g hg
    obtain ⟨hxp, h2, h3⟩ := sqrt_facts ha hg
    obtain ⟨r1, r2⟩ := ratio_bounds hxp
    have hs : 0 < Real.sqrt (a₀ * g) := Real.sqrt_pos.mpr (mul_pos ha hg)
    rw [gObs_eq_x ha hg, ← h3, mul_div_cancel_left₀ _ (by rw [h3]; exact hs.ne')]
    first | exact r1 | exact r2

/-- Newtonian regime: the excess g_obs − g_bar → 0 as g_bar → ∞
(it is bounded by 6a₀/√(g_bar/a₀)). -/
theorem excess_bound {a₀ g : ℝ} (ha : 0 < a₀) (hg : 0 < g) :
    0 ≤ gObs a₀ g - g ∧ gObs a₀ g - g ≤ 6 * a₀ / Real.sqrt (g / a₀) := by
  obtain ⟨hx, h2, -⟩ := sqrt_facts ha hg
  rw [gObs_thermal ha hg]
  generalize Real.sqrt (g / a₀) = s at *
  subst h2
  have h4 := Real.sum_le_exp_of_nonneg hx.le 4
  simp [Finset.sum_range_succ, Nat.factorial] at h4
  have hE : s ^ 3 / 6 ≤ exp s - 1 := by nlinarith [pow_pos hx 2]
  have hEp : 0 < exp s - 1 := lt_of_lt_of_le (by positivity) hE
  constructor
  · have : 0 ≤ a₀ * s ^ 2 * (1 / (exp s - 1)) := by positivity
    nlinarith
  · rw [show a₀ * s ^ 2 * (1 + 1 / (exp s - 1)) - a₀ * s ^ 2 = a₀ * s ^ 2 / (exp s - 1) by ring]
    rw [div_le_div_iff₀ hEp hx]
    nlinarith [mul_le_mul_of_nonneg_left hE (by positivity : (0:ℝ) ≤ 6 * a₀)]

theorem newtonian_limit {a₀ : ℝ} (ha : 0 < a₀) :
    Tendsto (fun g => gObs a₀ g - g) atTop (𝓝 0) := by
  have hx : Tendsto (fun g => Real.sqrt (g / a₀)) atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun b => ⟨a₀ * b ^ 2, fun g hg => ?_⟩
    have : b ^ 2 ≤ g / a₀ := by rw [le_div_iff₀ ha]; linarith
    calc b ≤ |b| := le_abs_self b
      _ = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
      _ ≤ _ := Real.sqrt_le_sqrt this
  have hup : Tendsto (fun g => 6 * a₀ / Real.sqrt (g / a₀)) atTop (𝓝 0) :=
    hx.const_div_atTop (6 * a₀)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_ <;>
  · filter_upwards [eventually_gt_atTop 0] with g hg
    first | exact (excess_bound ha hg).1 | exact (excess_bound ha hg).2


/-! ### Rotation curves and the baryonic Tully–Fisher relation -/

/-- Circular speed squared at radius r for enclosed baryonic mass Menc(r). -/
def vsq (a₀ G : ℝ) (Menc : ℝ → ℝ) (r : ℝ) : ℝ := r * gObs a₀ (G * Menc r / r ^ 2)

/-- Exact, uniform bound for every radius: √(G M a₀) ≤ v² ≤ √(G M a₀) + G M / r. -/
theorem vsq_bounds {a₀ G M r : ℝ} (ha : 0 < a₀) (hG : 0 < G) (hM : 0 < M) (hr : 0 < r) :
    Real.sqrt (G * M * a₀) ≤ vsq a₀ G (fun _ => M) r ∧
      vsq a₀ G (fun _ => M) r ≤ Real.sqrt (G * M * a₀) + G * M / r := by
  have hg : 0 < G * M / r ^ 2 := by positivity
  obtain ⟨-, h2, h3⟩ := gObs_sandwich ha hg
  have hs : r * Real.sqrt (a₀ * (G * M / r ^ 2)) = Real.sqrt (G * M * a₀) := by
    rw [show a₀ * (G * M / r ^ 2) = (G * M * a₀) / r ^ 2 by ring, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq hr.le]
    field_simp
  unfold vsq
  constructor
  · have := mul_le_mul_of_nonneg_left h2 hr.le
    have hpos : 0 ≤ r * (G * M / r ^ 2 / 2) := by positivity
    nlinarith
  · have := mul_le_mul_of_nonneg_left h3 hr.le
    have he : r * (G * M / r ^ 2) = G * M / r := by field_simp <;> ring
    nlinarith

/-- Asymptotic flatness with the exact BTFR normalization, for ANY spherical
baryon distribution of finite mass: if Menc(r) → M > 0 then v² → √(G M a₀),
so v⁴ → G M a₀. -/
theorem btfr {a₀ G M : ℝ} (ha : 0 < a₀) (hG : 0 < G) (hM : 0 < M) {Menc : ℝ → ℝ}
    (hlim : Tendsto Menc atTop (𝓝 M)) :
    Tendsto (vsq a₀ G Menc) atTop (𝓝 (Real.sqrt (G * M * a₀))) := by
  have hpos : ∀ᶠ r in atTop, 0 < Menc r := hlim.eventually (lt_mem_nhds hM)
  have hlo : Tendsto (fun r => Real.sqrt (G * Menc r * a₀)) atTop (𝓝 (Real.sqrt (G * M * a₀))) :=
    (((hlim.const_mul G).mul_const a₀)).sqrt
  have hhi : Tendsto (fun r => Real.sqrt (G * Menc r * a₀) + G * Menc r / r) atTop
      (𝓝 (Real.sqrt (G * M * a₀))) := by
    have : Tendsto (fun r => G * Menc r / r) atTop (𝓝 0) :=
      (hlim.const_mul G).div_atTop tendsto_id
    simpa using hlo.add this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_ <;>
  · filter_upwards [hpos, eventually_gt_atTop 0] with r hm hr
    have := vsq_bounds (M := Menc r) ha hG hm hr
    first | exact this.1 | exact this.2

theorem btfr_fourth_power {a₀ G M : ℝ} (ha : 0 < a₀) (hG : 0 < G) (hM : 0 < M) {Menc : ℝ → ℝ}
    (hlim : Tendsto Menc atTop (𝓝 M)) :
    Tendsto (fun r => vsq a₀ G Menc r ^ 2) atTop (𝓝 (G * M * a₀)) := by
  have := (btfr ha hG hM hlim).pow 2
  rwa [Real.sq_sqrt (by positivity)] at this

/-- With the thermal-contact scale a₀ = ε c H₀ the asymptotic speed is fixed with
no galaxy-dependent parameter: v⁴ → G M ε c H₀. -/
theorem btfr_parameter_free {ε c H₀ G M : ℝ} (he : 0 < ε) (hc : 0 < c) (hH : 0 < H₀)
    (hG : 0 < G) (hM : 0 < M) {Menc : ℝ → ℝ} (hlim : Tendsto Menc atTop (𝓝 M)) :
    Tendsto (fun r => vsq (ε * c * H₀) G Menc r ^ 2) atTop (𝓝 (G * M * ε * c * H₀)) := by
  have := btfr_fourth_power (a₀ := ε * c * H₀) (by positivity) hG hM hlim
  simpa [mul_assoc] using this

/-! ### Lensing of the deep-regime point mass (Sec. 16) -/

theorem integral_inv_sq_add_sq {b : ℝ} (hb : 0 < b) :
    ∫ z : ℝ, 1 / (b ^ 2 + z ^ 2) = π / b := by
  have h := integral_univ_inv_one_add_sq
  have hc := MeasureTheory.Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) (b⁻¹)
  simp only [h, smul_eq_mul, abs_inv, abs_of_pos hb, inv_inv] at hc
  have hfun : (fun z : ℝ => 1 / (b ^ 2 + z ^ 2)) = fun z => b⁻¹ ^ 2 * (1 + (b⁻¹ * z) ^ 2)⁻¹ := by
    funext z; field_simp
  rw [hfun, MeasureTheory.integral_const_mul, hc]
  field_simp <;> ring

/-- Deep-regime field g = A/r with A = √(G M a₀): the asymptotic light
deflection (2/c²)∫ g·(b/r) dz equals 2πA/c², independent of impact parameter. -/
theorem deflection_deep {A c b : ℝ} (hc : c ≠ 0) (hb : 0 < b) :
    2 / c ^ 2 * ∫ z : ℝ, A / Real.sqrt (b ^ 2 + z ^ 2) * (b / Real.sqrt (b ^ 2 + z ^ 2)) =
      2 * π * A / c ^ 2 := by
  have hfun : (fun z : ℝ => A / Real.sqrt (b ^ 2 + z ^ 2) * (b / Real.sqrt (b ^ 2 + z ^ 2))) =
      fun z => (A * b) * (1 / (b ^ 2 + z ^ 2)) := by
    funext z
    have hp : 0 < b ^ 2 + z ^ 2 := by positivity
    rw [div_mul_div_comm, ← sq, Real.sq_sqrt hp.le]; ring
  rw [hfun, MeasureTheory.integral_const_mul, integral_inv_sq_add_sq hb]
  field_simp <;> ring

/-- Projected surface density of ρ⊥ = A/(4πG r²): Σ⊥(R) = A/(4 G R). -/
theorem surface_density_deep {A G R : ℝ} (hG : G ≠ 0) (hR : 0 < R) :
    ∫ z : ℝ, A / (4 * π * G * (R ^ 2 + z ^ 2)) = A / (4 * G * R) := by
  have hfun : (fun z : ℝ => A / (4 * π * G * (R ^ 2 + z ^ 2))) =
      fun z => (A / (4 * π * G)) * (1 / (R ^ 2 + z ^ 2)) := by
    funext z; field_simp
  rw [hfun, MeasureTheory.integral_const_mul, integral_inv_sq_add_sq hR]
  field_simp <;> ring

/-! ### Reciprocity: why the response must be evaluated on the joint source -/

/-- Per-carrier responses give excess forces scaling as M_Q√M_P and M_P√M_Q.
They balance only for equal masses, so a per-carrier rule self-accelerates
every unequal pair. -/
theorem percarrier_balance_iff {Mp Mq : ℝ} (hp : 0 < Mp) (hq : 0 < Mq) :
    Mq * Real.sqrt Mp = Mp * Real.sqrt Mq ↔ Mp = Mq := by
  constructor
  · intro h
    have sp := Real.sqrt_pos.mpr hp; have sq := Real.sqrt_pos.mpr hq
    have e1 := Real.sq_sqrt hp.le; have e2 := Real.sq_sqrt hq.le
    -- Mq √Mp = Mp √Mq  ⇒  √Mq = √Mp
    have : Real.sqrt Mq * (Real.sqrt Mp * Real.sqrt Mq) = Real.sqrt Mp * (Real.sqrt Mp * Real.sqrt Mq) := by
      nlinarith
    have h' : Real.sqrt Mq = Real.sqrt Mp := by
      have hpos : 0 < Real.sqrt Mp * Real.sqrt Mq := mul_pos sp sq
      exact mul_right_cancel₀ hpos.ne' this
    rw [← e1, ← e2, h']
  · rintro rfl; rfl

end Entropic.GalacticLaw
