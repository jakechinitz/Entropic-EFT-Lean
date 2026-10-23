import Entropic.Spine
import Entropic.BlackHole
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Appendix F.5–F.7: horizon counting numbers, tortoise coordinate, echo delay, capacity
transport (ledger C06-18, -20, -23 … -26, -30, -31, -33, -34, -35, -36). -/

noncomputable section
namespace Entropic.AppFG
open Real Set Filter Topology

/-! ### ln 2 to 17 digits -/

theorem log_two_tight :
    (0.69314718055994530 : ℝ) < Real.log 2 ∧ Real.log 2 < 0.69314718055994531 := by
  constructor
  · rw [Real.lt_log_iff_exp_lt (by norm_num)]
    refine lt_of_le_of_lt (Real.exp_bound' (x := 0.69314718055994530) (by norm_num) (by norm_num)
      (n := 25) (by norm_num)) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · rw [Real.log_lt_iff_lt_exp (by norm_num)]
    refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (x := 0.69314718055994531) (by norm_num) 25)
    norm_num [Finset.sum_range_succ, Nat.factorial]

/-- C06-23: γ_BI = ln 2/(6π) = 0.036772600025441… (12 significant digits). -/
theorem gammaBI_value :
    0.0367726000254418 < Entropic.Spine.gammaBI ∧ Entropic.Spine.gammaBI < 0.0367726000254421 := by
  obtain ⟨l1, l2⟩ := log_two_tight
  have p1 := Real.pi_gt_d20; have p2 := Real.pi_lt_d20
  unfold Entropic.Spine.gammaBI
  have hp : 0 < 6 * Real.pi := by positivity
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

/-- C06-23 matching: N ln 2 = A_N/(4L²) with A_N = 24πγN L² (N ≥ 1) forces γ = ln 2/(6π). -/
theorem immirzi_from_matching {γ L : ℝ} {N : ℕ} (hN : 1 ≤ N) (hL : L ≠ 0)
    (h : N * Real.log 2 = 24 * Real.pi * γ * N * L ^ 2 / (4 * L ^ 2)) :
    γ = Entropic.Spine.gammaBI := by
  have hN' : (N:ℝ) ≠ 0 := by
    have h1 : (1:ℝ) ≤ (N:ℝ) := (by exact_mod_cast hN)
    linarith
  unfold Entropic.Spine.gammaBI
  have hp : 0 < Real.pi := Real.pi_pos
  have hL2 : 0 < L ^ 2 := by positivity
  rw [mul_div_assoc] at h
  have e : 24 * Real.pi * γ * ↑N * L ^ 2 / (4 * L ^ 2) = 6 * Real.pi * γ * N := by field_simp; ring
  rw [← mul_div_assoc, e] at h
  have h2 : (N:ℝ) * (Real.log 2 - 6 * Real.pi * γ) = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hN'
  · rw [eq_div_iff (by positivity)]; linarith

/-- C06-24: a_ch = 4 ln 2 = 2.7725887222 and ρ_ch = 1/(4 ln 2) = 0.3606737602 (units L_*). -/
theorem channel_numbers :
    2.7725887222 < 4 * Real.log 2 ∧ 4 * Real.log 2 < 2.7725887223 ∧
      0.3606737602 < 1 / (4 * Real.log 2) ∧ 1 / (4 * Real.log 2) < 0.3606737603 := by
  obtain ⟨l1, l2⟩ := log_two_tight
  have hp : 0 < 4 * Real.log 2 := by positivity
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

/-- C06-25: the bare Casimir alternative ln 2 = 4π√3 γ gives γ = ln 2/(4π√3) = 0.0318460058,
smaller than ln 2/(6π). -/
theorem casimir_alternative :
    8 * Real.pi * (Real.log 2 / (4 * Real.pi * Real.sqrt 3)) * Real.sqrt 12 / 4 = Real.log 2 ∧
      0.0318460057 < Real.log 2 / (4 * Real.pi * Real.sqrt 3) ∧
      Real.log 2 / (4 * Real.pi * Real.sqrt 3) < 0.0318460058 ∧
      Real.log 2 / (4 * Real.pi * Real.sqrt 3) < Entropic.Spine.gammaBI := by
  obtain ⟨l1, l2⟩ := log_two_tight
  have p1 := Real.pi_gt_d20; have p2 := Real.pi_lt_d20
  have s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have s3p : 0 < Real.sqrt 3 := by positivity
  have s3l : (1.7320508075 : ℝ) < Real.sqrt 3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s3u : Real.sqrt 3 < 1.7320508076 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h12 : Real.sqrt 12 = 2 * Real.sqrt 3 := by
    rw [show (12:ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hden : 0 < 4 * Real.pi * Real.sqrt 3 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h12]; have := Real.pi_ne_zero; field_simp; ring
  · rw [lt_div_iff₀ hden]; nlinarith [mul_pos (by linarith : (0:ℝ) < Real.pi) s3p]
  · rw [div_lt_iff₀ hden]; nlinarith [mul_pos (by linarith : (0:ℝ) < Real.pi) s3p]
  · unfold Entropic.Spine.gammaBI
    apply div_lt_div_of_pos_left (by positivity) (by positivity)
    nlinarith

/-- C06-20: S/k_B = A/(4L²) = (A/4)/L² (mean projected area per L² for convex horizons). -/
theorem projected_area_form (A L : ℝ) : A / (4 * L ^ 2) = (A / 4) / L ^ 2 := by ring

/-! ### Tortoise coordinate and echo delay (C06-31, -33) -/

/-- Tortoise coordinate r_* = r + r_h ln(r/r_h − 1). -/
def rstar (rh r : ℝ) : ℝ := r + rh * Real.log (r / rh - 1)

/-- C06-31: dr_*/dr = 1/q_geo, r_* − r_h ln q_geo → r_h, and r_* → −∞ as r → r_h⁺. -/
theorem tortoise {rh : ℝ} (hrh : 0 < rh) :
    (∀ r, rh < r → HasDerivAt (rstar rh) (1 / (1 - rh / r)) r) ∧
      (∀ r, rh < r → rstar rh r - rh * Real.log (1 - rh / r) = r + rh * Real.log (r / rh)) ∧
      Tendsto (fun r => rstar rh r - rh * Real.log (1 - rh / r)) (𝓝[>] rh) (𝓝 rh) ∧
      Tendsto (rstar rh) (𝓝[>] rh) atBot := by
  have hid : ∀ r, rh < r → r / rh - 1 = (1 - rh / r) * (r / rh) := by
    intro r hr; have : r ≠ 0 := by linarith
    field_simp
  refine ⟨fun r hr => ?_, fun r hr => ?_, ?_, ?_⟩
  · have hr0 : r ≠ 0 := by linarith
    have hpos : 0 < r / rh - 1 := by rw [sub_pos, one_lt_div hrh]; exact hr
    have h1 := (((hasDerivAt_id' r).div_const rh).sub_const 1).log hpos.ne'
    have h2 := (hasDerivAt_id' r).add (h1.const_mul rh)
    convert h2 using 1
    · funext x; simp only [rstar, Pi.add_apply]
    · have : r - rh ≠ 0 := by linarith
      field_simp; ring
  · rw [rstar, hid r hr, Real.log_mul (by
        have : rh / r < 1 := (div_lt_one (by linarith)).mpr hr
        linarith) (div_pos (by linarith) hrh).ne']
    ring
  · have hc : ContinuousAt (fun r => r + rh * Real.log (r / rh)) rh :=
      (continuous_id.continuousAt).add ((Real.continuousAt_log (by simp [hrh.ne'])).comp
        (continuousAt_id.div_const rh) |>.const_mul rh)
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi rh))
    simp only [div_self hrh.ne', Real.log_one, mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [show rstar rh r - rh * Real.log (1 - rh / r) = r + rh * Real.log (r / rh) by
      rw [rstar, hid r hr, Real.log_mul (by
        have : rh / r < 1 := (div_lt_one (by have : rh < r := hr; linarith)).mpr hr
        linarith) (div_pos (by have : rh < r := hr; linarith) hrh).ne']; ring]
  · -- r/rh − 1 → 0⁺, log → −∞, times rh > 0, plus bounded r
    have h1 : Tendsto (fun r => r / rh - 1) (𝓝[>] rh) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Tendsto (fun r => r / rh - 1) (𝓝 rh) (𝓝 (rh / rh - 1)) :=
          ((continuous_id.div_const rh).sub continuous_const).tendsto rh
        rw [div_self hrh.ne', sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        show 0 < r / rh - 1
        rw [sub_pos, one_lt_div hrh]; exact hr
    have h2 := (Real.tendsto_log_nhdsGT_zero.comp h1).const_mul_atBot hrh
    have h3 : Tendsto (fun r : ℝ => r) (𝓝[>] rh) (𝓝 rh) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    exact (h3.add_atBot h2).congr (fun r => by simp [rstar, Function.comp])

/-- C06-33: a reflecting layer at q_geo = δ sits at r_δ = r_h/(1 − δ); the round-trip
2|r_*(r_δ)|/c equals (2r_h/c)|ln δ| up to a bounded remainder: for 0 < δ ≤ 1/2,
|r_*(r_δ) − r_h ln δ| ≤ 3r_h. -/
theorem echo_delay {rh δ : ℝ} (hrh : 0 < rh) (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) :
    |rstar rh (rh / (1 - δ)) - rh * Real.log δ| ≤ 3 * rh := by
  have h1 : 0 < 1 - δ := by linarith
  have e : rh / (1 - δ) / rh - 1 = δ / (1 - δ) := by field_simp; ring
  unfold rstar; rw [e, Real.log_div hδ.ne' h1.ne']
  have hl : -Real.log 2 ≤ Real.log (1 - δ) ∧ Real.log (1 - δ) ≤ 0 := by
    constructor
    · rw [← Real.log_inv]; apply Real.log_le_log (by norm_num); linarith
    · exact Real.log_nonpos h1.le (by linarith)
  have hl2 : Real.log 2 < 1 := by have := log_two_tight.2; linarith
  have hr1 : rh / (1 - δ) ≤ 2 * rh := by rw [div_le_iff₀ h1]; nlinarith
  have hr0 : 0 < rh / (1 - δ) := by positivity
  rw [abs_le]; constructor <;> nlinarith [hl.1, hl.2]

/-! ### Capacity transport (C06-34, -35, -36) -/

/-- C06-34: eliminating J from ∂ₜq + ∂ₓJ = 0 and τ∂ₜJ + J = −D₀∂ₓq for plane waves
q = Qe^{i(kx−ωt)}, J = J₀e^{i(kx−ωt)} gives τ(−iω)²Q + (−iω)Q + D₀k²Q = 0, the telegrapher
symbol with speed √(D₀/τ); and for D(q) = D₀q(1−q), √(D(q)/τ) ≤ √(D₀/(4τ)). -/
theorem telegrapher_elimination {τ D0 k : ℝ} {ω Q J0 : ℂ}
    (h1 : -Complex.I * ω * Q + Complex.I * k * J0 = 0)
    (h2 : τ * (-Complex.I * ω) * J0 + J0 = -(D0 * (Complex.I * k * Q))) :
    τ * (-Complex.I * ω) ^ 2 * Q + (-Complex.I * ω) * Q + D0 * k ^ 2 * Q = 0 := by
  -- multiply h2 by ik and use ik J0 = iωQ
  have hJ : Complex.I * k * J0 = Complex.I * ω * Q := by linear_combination h1
  have := congrArg (fun z => Complex.I * k * z) h2
  linear_combination (-1 : ℂ) * this + (τ * (-Complex.I * ω) + 1) * hJ + Q * D0 * k ^ 2 * Complex.I_sq

theorem local_speed_bound {D0 τ q : ℝ} (hD : 0 ≤ D0) (hτ : 0 < τ) :
    Real.sqrt (D0 * (q * (1 - q)) / τ) ≤ Real.sqrt (D0 / (4 * τ)) := by
  apply Real.sqrt_le_sqrt
  rw [div_le_div_iff₀ hτ (by positivity)]
  nlinarith [sq_nonneg (q - 1/2), mul_nonneg hD (sq_nonneg (q - 1/2))]

/-- C06-35 (corrected): the hyperbolic capacity system does NOT preserve 0 ≤ q ≤ 1 in general.
Exact global solution of ∂ₜq + ∂ₓJ = −Γ₀qΣ, τ∂ₜJ + J = −D₀q(1−q)∂ₓq with Σ = 0:
q(t,x) = −a₀τ(1 − e^{−t/τ}), J(t,x) = a₀e^{−t/τ}x. It starts at q ≡ 0 and q < 0 for all t > 0
when a₀ > 0. (Memory in J lets q cross the q = 0 level, which the parabolic limit forbids.) -/
theorem capacity_overshoot {τ a0 D0 : ℝ} (hτ : 0 < τ) (ha : 0 < a0) :
    let q : ℝ → ℝ → ℝ := fun t _ => -a0 * τ * (1 - Real.exp (-t / τ))
    let J : ℝ → ℝ → ℝ := fun t x => a0 * Real.exp (-t / τ) * x
    (∀ t x : ℝ, HasDerivAt (fun s => q s x) (-(a0 * Real.exp (-t / τ))) t) ∧
    (∀ t x : ℝ, HasDerivAt (fun y => J t y) (a0 * Real.exp (-t / τ)) x) ∧
    (∀ t x : ℝ, HasDerivAt (fun s => J s x) (-(a0 * Real.exp (-t / τ) * x) / τ) t) ∧
    (∀ t x : ℝ, HasDerivAt (fun y => q t y) 0 x) ∧
    -- continuity equation ∂ₜq + ∂ₓJ = −Γ₀qΣ with Σ = 0, and flux law τ∂ₜJ + J = −D(q)∂ₓq
    (∀ t : ℝ, -(a0 * Real.exp (-t / τ)) + a0 * Real.exp (-t / τ) = 0) ∧
    (∀ t x : ℝ, τ * (-(a0 * Real.exp (-t / τ) * x) / τ) + J t x = -(D0 * (q t x * (1 - q t x)) * 0)) ∧
    (∀ x : ℝ, q 0 x = 0) ∧ (∀ t x : ℝ, 0 < t → q t x < 0) := by
  intro q J
  have hexp : ∀ t, HasDerivAt (fun s => Real.exp (-s / τ)) (-(Real.exp (-t / τ)) / τ) t := by
    intro t
    have := ((hasDerivAt_neg t).div_const τ).exp
    convert this using 1; ring
  refine ⟨fun t x => ?_, fun t x => ?_, fun t x => ?_, fun t x => hasDerivAt_const _ _,
    fun t => by ring, fun t x => by simp only [J]; field_simp; ring, fun x => by simp [q],
    fun t x ht => ?_⟩
  · have := ((hexp t).const_sub 1).const_mul (-a0 * τ)
    convert this using 1; field_simp
  · have := (hasDerivAt_id' x).const_mul (a0 * Real.exp (-t / τ)); simpa using this
  · have := ((hexp t).const_mul a0).mul_const x
    convert this using 1; ring
  · simp only [q]
    have h1 : Real.exp (-t / τ) < 1 := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (div_neg_of_neg_of_pos (by linarith) hτ)
    have : 0 < a0 * τ * (1 - Real.exp (-t / τ)) := by
      apply mul_pos (mul_pos ha hτ); linarith
    linarith

/-- The general mechanism: at any point where q = 0 and ∂ₓJ > 0 (with Γ ≥ 0 so the sink
vanishes at q = 0), ∂ₜq = −∂ₓJ < 0 and q becomes negative at once. -/
theorem crossing_mechanism {q : ℝ → ℝ} {dJ : ℝ} (hq0 : q 0 = 0) (hdJ : 0 < dJ)
    (hd : HasDerivAt q (-dJ - 0) 0) : ∀ᶠ t in 𝓝[>] 0, q t < 0 := by
  have hlt : -dJ - 0 < 0 := by linarith
  have h := (hasDerivWithinAt_iff_tendsto_slope' (s := Ioi (0:ℝ)) (x := 0)
    (by simp)).mp (hd.hasDerivWithinAt)
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), slope q 0 t < 0 := h.eventually (gt_mem_nhds hlt)
  filter_upwards [hev, self_mem_nhdsWithin] with t ht htp
  have htp' : (0:ℝ) < t := htp
  rw [slope_def_field, hq0, sub_zero, sub_zero] at ht
  by_contra hc; push_neg at hc
  have := div_nonneg hc htp'.le; linarith

/-- C06-36: along a front r_f(t) with q(t, r_f(t)) = 0 and ∂ᵣq ≠ 0, the chain rule gives
∂ₜq + ∂ᵣq·ṙ_f = 0, i.e. ṙ_f = −∂ₜq/∂ᵣq. -/
theorem front_velocity {q : ℝ × ℝ → ℝ} {rf : ℝ → ℝ} {t qt qr v : ℝ}
    (hq : HasFDerivAt q ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight qt +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight qr) (t, rf t))
    (hrf : HasDerivAt rf v t) (hlevel : ∀ s, q (s, rf s) = 0) (hqr : qr ≠ 0) :
    v = -qt / qr := by
  have hpath : HasDerivAt (fun s => (s, rf s)) ((1 : ℝ), v) t :=
    (hasDerivAt_id t).prodMk hrf
  have hcomp := hq.comp_hasDerivAt t hpath
  have hzero : HasDerivAt (fun s => q (s, rf s)) 0 t := by
    have : (fun s => q (s, rf s)) = fun _ => (0:ℝ) := funext hlevel
    rw [this]; exact hasDerivAt_const _ _
  have := hcomp.unique hzero
  simp at this
  field_simp; linarith

end Entropic.AppFG
