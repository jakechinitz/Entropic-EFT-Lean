import Entropic.AppO.Flow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! Appendix O, numerical items with certified brackets: uniform-core sign change (C13-24),
a witness for the global lower bound (C13-26), budget ratio (C13-32), present capacity/baryon
ratio (C13-36), density-floor values (C13-41), stream separation and decoherence times (C13-62,
C13-64), early-release bound (C13-65), reionization increments at x_ion = 1 (C13-68), the binary
symmetric channel (C13-82), virial temperatures (C13-88) and the recurrence margin (C13-97). -/

noncomputable section
namespace Entropic.AppO.Num
open Real

/-- Degree-4 Taylor polynomial of exp. -/
def tay (d : ℝ) : ℝ := 1 + d + d ^ 2 / 2 + d ^ 3 / 6 + d ^ 4 / 24

theorem exp_near {d : ℝ} (hd : |d| ≤ 1) : |Real.exp d - tay d| ≤ |d| ^ 5 / 100 := by
  have := Real.exp_bound hd (n := 5) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
  unfold tay; convert this using 2 <;> norm_num <;> ring

theorem exp_lower {a : ℝ} (n : ℕ) (hd : |a - n| ≤ 1) :
    (2.7182818283 : ℝ) ^ n * (tay (a - n) - |a - n| ^ 5 / 100) ≤ Real.exp a := by
  have hsplit : Real.exp a = Real.exp 1 ^ n * Real.exp (a - n) := by
    rw [Real.exp_one_pow, ← Real.exp_add]; ring_nf
  have h1 := (abs_le.mp (exp_near hd)).1
  have hE : (2.7182818283 : ℝ) ^ n ≤ Real.exp 1 ^ n :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le n
  rcases le_or_gt (tay (a - n) - |a - n| ^ 5 / 100) 0 with h | h
  · have : (2.7182818283 : ℝ) ^ n * (tay (a - n) - |a - n| ^ 5 / 100) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith [Real.exp_pos a]
  · rw [hsplit]
    calc (2.7182818283 : ℝ) ^ n * (tay (a - n) - |a - n| ^ 5 / 100)
        ≤ Real.exp 1 ^ n * (tay (a - n) - |a - n| ^ 5 / 100) := mul_le_mul_of_nonneg_right hE h.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem exp_upper {a : ℝ} (n : ℕ) (hd : |a - n| ≤ 1) :
    Real.exp a ≤ (2.7182818286 : ℝ) ^ n * (tay (a - n) + |a - n| ^ 5 / 100) := by
  have hsplit : Real.exp a = Real.exp 1 ^ n * Real.exp (a - n) := by
    rw [Real.exp_one_pow, ← Real.exp_add]; ring_nf
  have h1 := (abs_le.mp (exp_near hd)).2
  have hE : Real.exp 1 ^ n ≤ (2.7182818286 : ℝ) ^ n :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le n
  rw [hsplit]
  exact mul_le_mul hE (by linarith) (Real.exp_pos _).le (by positivity)

/-! ### C13-24: the uniform-core root -/

/-- f(x) = x − 6 + 6e^{−x}; its positive zero is the root of x = 6(1 − e^{−x}). -/
def fcore (x : ℝ) : ℝ := x - 6 + 6 * Real.exp (-x)

theorem fcore_lo : fcore 5.98490122635 < 0 := by
  have h := exp_lower (a := 5.98490122635) 6 (by norm_num [abs_le])
  norm_num [tay] at h
  unfold fcore
  rw [Real.exp_neg]
  have hp := Real.exp_pos (5.98490122635 : ℝ)
  rw [← sub_neg, show (5.98490122635 : ℝ) - 6 + 6 * (Real.exp 5.98490122635)⁻¹ - 0 =
    ((5.98490122635 - 6) * Real.exp 5.98490122635 + 6) / Real.exp 5.98490122635 by field_simp; try ring]
  apply div_neg_of_neg_of_pos _ hp
  nlinarith

theorem fcore_hi : 0 < fcore 5.98490122645 := by
  have h := exp_upper (a := 5.98490122645) 6 (by norm_num [abs_le])
  norm_num [tay] at h
  unfold fcore
  rw [Real.exp_neg]
  have hp := Real.exp_pos (5.98490122645 : ℝ)
  rw [show (5.98490122645 : ℝ) - 6 + 6 * (Real.exp 5.98490122645)⁻¹ =
    ((5.98490122645 - 6) * Real.exp 5.98490122645 + 6) / Real.exp 5.98490122645 by field_simp; try ring]
  apply div_pos _ hp
  nlinarith

/-- Two positive zeros of f are equal (strict convexity of exp with f(0) = 0). -/
theorem fcore_unique {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hfa : fcore a = 0) (hfb : fcore b = 0) :
    a = b := by
  have key : ∀ a b : ℝ, 0 < a → a < b → fcore b = 0 → fcore a < 0 := by
    intro a b ha hab hfb
    have hb : 0 < b := lt_trans ha hab
    set t := a / b
    have ht0 : 0 < t := div_pos ha hb
    have ht1 : t < 1 := (div_lt_one hb).mpr hab
    have hc := strictConvexOn_exp.2 (Set.mem_univ (-b)) (Set.mem_univ 0) (by linarith) ht0
      (by linarith : 0 < 1 - t) (by ring)
    simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hc
    have hta : t * -b = -a := by simp only [t]; field_simp
    rw [hta] at hc
    unfold fcore at hfb ⊢
    have : a = t * b := by simp only [t]; field_simp
    nlinarith
  rcases lt_trichotomy a b with h | h | h
  · linarith [key a b ha h hfb]
  · exact h
  · linarith [key b a hb h hfa]

/-- C13-24: the s = 3 contact ratio vanishes at a unique positive x₀ with x₀ = 6(1 − e^{−x₀}),
5.98490122635 < x₀ < 5.98490122645 (so x₀ = 5.98490123 to 8 decimals) and
35.819042685 < x₀² < 35.819042695 (g_b/a₀ = 35.81904269). -/
theorem uniform_core_root :
    ∃ x : ℝ, (0 < x ∧ x = 6 * (1 - Real.exp (-x))) ∧
      (∀ y, 0 < y → y = 6 * (1 - Real.exp (-y)) → y = x) ∧
      5.98490122635 < x ∧ x < 5.98490122645 ∧ 35.819042685 < x ^ 2 ∧ x ^ 2 < 35.819042695 ∧
      Entropic.AppO.ratio 3 x = 0 := by
  have hcont : ContinuousOn fcore (Set.Icc 5.98490122635 5.98490122645) := by
    unfold fcore; fun_prop
  obtain ⟨x, ⟨hx1, hx2⟩, hfx⟩ := intermediate_value_Ioo (by norm_num) hcont ⟨fcore_lo, fcore_hi⟩
  have hx0 : 0 < x := by linarith
  have hroot : x = 6 * (1 - Real.exp (-x)) := by unfold fcore at hfx; linarith
  refine ⟨x, ⟨hx0, hroot⟩, fun y hy hyr => fcore_unique hy hx0 (by unfold fcore; linarith) hfx,
    hx1, hx2, by nlinarith, by nlinarith, ?_⟩
  unfold Entropic.AppO.ratio
  have hne : 1 - Real.exp (-x) ≠ 0 := by
    intro h; rw [h] at hroot; linarith
  have : x / (1 - Real.exp (-x)) = 6 := by rw [div_eq_iff hne]; linarith
  rw [this]; norm_num

/-- C13-26 (witness): R₃(6.98708) < −1.531035·10⁻⁴, so ζ₋ ≥ 1.531035·10⁻⁴. -/
theorem lower_bound_witness : Entropic.AppO.ratio 3 6.98708 < -1.531035e-4 := by
  have hU := exp_upper (a := 6.98708) 7 (by norm_num [abs_le])
  have hL := exp_lower (a := 6.98708) 7 (by norm_num [abs_le])
  have hy1 : 1000 < Real.exp 6.98708 := lt_of_lt_of_le (by norm_num [tay]) hL
  have hyU : Real.exp 6.98708 ≤ 1082.556 := le_trans hU (by norm_num [tay])
  unfold Entropic.AppO.ratio
  rw [Real.exp_neg]
  set y := Real.exp 6.98708
  have hy0 : y - 1 ≠ 0 := by linarith
  have e : 1 / (y - 1) * (1 - (3 - 2) / (2 * 3) * (6.98708 / (1 - y⁻¹))) =
      (6 * (y - 1) - 6.98708 * y) / (6 * (y - 1) ^ 2) := by
    have : y ≠ 0 := by linarith
    field_simp; ring
  rw [e, div_lt_iff₀ (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hyU) (by nlinarith : (0:ℝ) ≤ 6 * 1.531035e-4 * (y + 1082.556 - 2) - 0.98708)]

/-! ### C13-32, C13-36, C13-41: closure-root release numbers (η* = 0.0298668443935, F_rel(1) = 0.6633922061) -/

/-- C13-32: e^{−η}/(1 − η) − 1 = 0.0455% (0.000455 < · < 0.000456). -/
theorem budget_ratio :
    0.000455 < Real.exp (-0.0298668443935) / (1 - 0.0298668443935) - 1 ∧
      Real.exp (-0.0298668443935) / (1 - 0.0298668443935) - 1 < 0.000456 := by
  have hU := exp_upper (a := -0.0298668443935) 0 (by norm_num [abs_le])
  have hL := exp_lower (a := -0.0298668443935) 0 (by norm_num [abs_le])
  norm_num [tay] at hU hL
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ (by norm_num)]; nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ (by norm_num)]; nlinarith

/-- C13-32 (budget): with f_b = 0.157, M_h = 10¹² and M_b = 6·10¹⁰, e^{−η}(1 − f_b)M_h/M_b ∈ (13.6, 13.7),
i.e. about 14 M_b; and (e^{−η}/ε)f_bM_h = e^{−η}(1 − f_b)M_h iff f_b/ε = 1 − f_b. -/
theorem budget_value :
    13.6 < Real.exp (-0.0298668443935) * (1 - 0.157) * 1e12 / 6e10 ∧
      Real.exp (-0.0298668443935) * (1 - 0.157) * 1e12 / 6e10 < 13.7 := by
  have hU := exp_upper (a := -0.0298668443935) 0 (by norm_num [abs_le])
  have hL := exp_lower (a := -0.0298668443935) 0 (by norm_num [abs_le])
  norm_num [tay] at hU hL
  constructor <;> nlinarith

theorem budget_equality_iff {e ε fb Mh : ℝ} (he : 0 < e) (hε : 0 < ε) (hM : 0 < Mh) :
    e / ε * fb * Mh = e * (1 - fb) * Mh ↔ fb / ε = 1 - fb := by
  constructor
  · intro h
    have := mul_right_cancel₀ hM.ne' h
    have : e * (fb / ε) = e * (1 - fb) := by rw [← this]; ring
    exact mul_left_cancel₀ he.ne' this
  · intro h; rw [show e / ε * fb * Mh = e * (fb / ε) * Mh by ring, h]

/-- C13-36: 5.333 e^{−η*F_rel(1)} = 5.2284 (5.22835 < · < 5.22845). -/
theorem capacity_baryon_ratio :
    5.22835 < 5.333 * Real.exp (-(0.0298668443935 * 0.6633922061)) ∧
      5.333 * Real.exp (-(0.0298668443935 * 0.6633922061)) < 5.22845 := by
  have hU := exp_upper (a := -(0.0298668443935 * 0.6633922061)) 0 (by norm_num [abs_le])
  have hL := exp_lower (a := -(0.0298668443935 * 0.6633922061)) 0 (by norm_num [abs_le])
  norm_num [tay] at hU hL ⊢
  constructor <;> nlinarith

/-- C13-41: 1 − e^{−η*F_rel(1)} = 0.01961844 (0.019618435 < · < 0.019618437); with d = 0.1 the bound is
< 19.62%, with d = 0.2 it is < 9.81%, and any d > 0.01961844 gives B < 1. -/
theorem density_floor_values :
    0.019618435 < 1 - Real.exp (-(0.0298668443935 * 0.6633922061)) ∧
      1 - Real.exp (-(0.0298668443935 * 0.6633922061)) < 0.019618437 ∧
      (1 - Real.exp (-(0.0298668443935 * 0.6633922061))) / 0.1 < 0.1962 ∧
      (1 - Real.exp (-(0.0298668443935 * 0.6633922061))) / 0.2 < 0.0981 ∧
      ∀ d : ℝ, 0.01961844 < d → (1 - Real.exp (-(0.0298668443935 * 0.6633922061))) / d < 1 := by
  have hU := exp_upper (a := -(0.0298668443935 * 0.6633922061)) 0 (by norm_num [abs_le])
  have hL := exp_lower (a := -(0.0298668443935 * 0.6633922061)) 0 (by norm_num [abs_le])
  norm_num [tay] at hU hL ⊢
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, fun d hd => ?_⟩
  rw [div_lt_one (by linarith)]; nlinarith

/-! ### Arithmetic items (C13-62, C13-64, C13-65, C13-68, C13-88) -/

/-- C13-62: t_sep = L*/Δv with L* = 1.616255·10⁻³⁵ m and Δv = 10 km/s is 1.62·10⁻³⁹ s to 3 figures. -/
theorem stream_separation : 1.615e-39 < (1.616255e-35 : ℝ) / 1e4 ∧ (1.616255e-35 : ℝ) / 1e4 < 1.625e-39 := by
  norm_num

/-- C13-64: 10/D_pin = 66.71 ticks for D_pin = 0.1499, n > 10/D_pin gives e^{−nD/2} < e^{−5}, and
(10/D_pin)·t_P with t_P = 5.391247·10⁻⁴⁴ s is 3.6·10⁻⁴² s. -/
theorem decoherence_time :
    66.71 < (10 : ℝ) / 0.1499 ∧ (10 : ℝ) / 0.1499 < 66.72 ∧
      (∀ n : ℝ, 10 / 0.1499 < n → Real.exp (-(n * 0.1499 / 2)) < Real.exp (-5)) ∧
      3.55e-42 < (10 : ℝ) / 0.1499 * 5.391247e-44 ∧ (10 : ℝ) / 0.1499 * 5.391247e-44 < 3.65e-42 := by
  refine ⟨by norm_num, by norm_num, fun n hn => ?_, by norm_num, by norm_num⟩
  apply Real.exp_lt_exp.mpr
  rw [div_lt_iff₀ (by norm_num)] at hn; linarith

/-- C13-65: 0.01/(0.00783·16³) = 3.1·10⁻⁴ and 5.5·10⁻³ exceeds it by a factor 17.6–17.7 (about 18). -/
theorem early_release :
    3.1e-4 < (0.01 : ℝ) / (0.00783 * 16 ^ 3) ∧ (0.01 : ℝ) / (0.00783 * 16 ^ 3) < 3.15e-4 ∧
      17.6 < (5.5e-3 : ℝ) / (0.01 / (0.00783 * 16 ^ 3)) ∧ (5.5e-3 : ℝ) / (0.01 / (0.00783 * 16 ^ 3)) < 17.7 := by
  norm_num

/-- C13-68: at x_ion = 1 the increments 0.00783(1 + z)³ are 2.686, 5.156, 7.83 for z = 6, 7.7, 9
(the stated 2.2, 4.4, 6.6 need x_ion ≈ 0.82, 0.85, 0.84). -/
theorem reionization_increments :
    (0.00783 : ℝ) * (1 + 6) ^ 3 = 2.68569 ∧ 5.15 < (0.00783 : ℝ) * (1 + 7.7) ^ 3 ∧
      (0.00783 : ℝ) * (1 + 7.7) ^ 3 < 5.16 ∧ (0.00783 : ℝ) * (1 + 9) ^ 3 = 7.83 ∧
      0.81 < (2.2 : ℝ) / 2.68569 ∧ (2.2 : ℝ) / 2.68569 < 0.83 := by
  norm_num

/-- C13-88: T = μm_pV²/(2k_B) at V = 14 km/s is 1.4·10⁴ K for μ = 1.22 and 7·10³ K for μ = 0.59
(m_p = 1.67262192·10⁻²⁷ kg, k_B = 1.380649·10⁻²³ J/K). -/
theorem virial_temperature :
    1.4e4 < (1.22 : ℝ) * 1.67262192e-27 * (1.4e4) ^ 2 / (2 * 1.380649e-23) ∧
      (1.22 : ℝ) * 1.67262192e-27 * (1.4e4) ^ 2 / (2 * 1.380649e-23) < 1.5e4 ∧
      6.9e3 < (0.59 : ℝ) * 1.67262192e-27 * (1.4e4) ^ 2 / (2 * 1.380649e-23) ∧
      (0.59 : ℝ) * 1.67262192e-27 * (1.4e4) ^ 2 / (2 * 1.380649e-23) < 7.1e3 := by
  norm_num

/-! ### C13-82: binary symmetric channel -/

section BSC
open Entropic.AppFG.Info

/-- Joint law of (A, Y) for a uniform bit through a BSC with flip probability 0.1. -/
def bsc : Fin 2 → Fin 2 → ℝ := fun a y => if a = y then 0.45 else 0.05

theorem log_045 : Real.log 0.45 = 2 * Real.log 3 - 2 * Real.log 2 - Real.log 5 := by
  rw [show (0.45 : ℝ) = 3 ^ 2 / (2 ^ 2 * 5) by norm_num, Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring

theorem log_005 : Real.log 0.05 = -(2 * Real.log 2 + Real.log 5) := by
  rw [show (0.05 : ℝ) = 1 / (2 ^ 2 * 5) by norm_num, Real.log_div (by norm_num) (by norm_num),
    Real.log_one, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring

theorem log_05 : Real.log 0.5 = -Real.log 2 := by
  rw [show (0.5 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]

/-- H(A|Y) = log 2 + log 5 − 1.8 log 3 (= −0.9 ln 0.9 − 0.1 ln 0.1) and H(A) = log 2. -/
theorem bsc_entropies :
    Hjoint bsc - H (pY bsc) = Real.log 2 + Real.log 5 - 1.8 * Real.log 3 ∧ H (pX bsc) = Real.log 2 := by
  have hpY : ∀ y, pY bsc y = 0.5 := by
    intro y; fin_cases y <;> norm_num [pY, bsc, Fin.sum_univ_two]
  have hpX : ∀ x, pX bsc x = 0.5 := by
    intro x; fin_cases x <;> norm_num [pX, bsc, Fin.sum_univ_two]
  constructor
  · simp only [Hjoint, H, hpY, Fin.sum_univ_two, bsc]
    norm_num [negMulLog]
    rw [show (9:ℝ)/20 = 0.45 by norm_num, show (1:ℝ)/20 = 0.05 by norm_num,
      show (1:ℝ)/2 = 0.5 by norm_num, log_045, log_005, log_05]
    ring
  · simp only [H, hpX, Fin.sum_univ_two]
    norm_num [negMulLog]
    rw [show (1:ℝ)/2 = 0.5 by norm_num, log_05]; ring

/-- C13-82: K_mix = H(A|Y)/H(A) = h₂(0.1) = 0.468996 (0.4689955 < · < 0.4689965), the reset
coefficient is e = min(0.9, 0.1) + min(0.1, 0.9) = 0.2, and e < K_mix. -/
theorem bsc_values :
    0.4689955 < (Hjoint bsc - H (pY bsc)) / H (pX bsc) ∧
      (Hjoint bsc - H (pY bsc)) / H (pX bsc) < 0.4689965 ∧
      min (0.9:ℝ) 0.1 + min (0.1:ℝ) 0.9 = 0.2 ∧ min (0.9:ℝ) 0.1 + min (0.1:ℝ) 0.9 < (Hjoint bsc - H (pY bsc)) / H (pX bsc) := by
  obtain ⟨h1, h2⟩ := bsc_entropies
  rw [h1, h2]
  have a1 := Real.log_two_gt_d9; have a2 := Real.log_two_lt_d9
  have b1 := Real.log_three_gt_d9; have b2 := Real.log_three_lt_d9
  have c1 := Real.log_five_gt_d9; have c2 := Real.log_five_lt_d9
  have hp : 0 < Real.log 2 := by linarith
  refine ⟨?_, ?_, by norm_num, ?_⟩
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith
  · rw [show min (0.9:ℝ) 0.1 + min (0.1:ℝ) 0.9 = 0.2 by norm_num, lt_div_iff₀ hp]; nlinarith
end BSC

/-! ### C13-97: recurrence margin -/

/-- C13-97: at the closure root, e^{(16.1 − 7) g} = e^{9.1 g} lies in (2.0·10²⁹, 2.2·10²⁹), so the stated
3·10²⁹ overstates the margin (about 2.1·10²⁹); and 1.0024/ε ∈ (5.33, 5.335) contains 5.333. -/
theorem recurrence_margin {η : ℝ} (h : Entropic.FiniteModel.ClosureStationary η) :
    2.0e29 < Real.exp ((16.1 - 7) * Entropic.ClosureRoot.gshare η) ∧
      Real.exp ((16.1 - 7) * Entropic.ClosureRoot.gshare η) < 2.2e29 ∧
      5.33 < 1.0024 / (Entropic.ClosureRoot.gshare η / (4 * π ^ 2)) ∧
      1.0024 / (Entropic.ClosureRoot.gshare η / (4 * π ^ 2)) < 5.335 := by
  obtain ⟨g1, g2⟩ := Entropic.ClosureRoot.gshare_bracket h
  unfold Entropic.ClosureRoot.gLo at g1; unfold Entropic.ClosureRoot.gHi at g2
  obtain ⟨e1, e2⟩ := Entropic.Spine.epsilon_bracket h
  set g := Entropic.ClosureRoot.gshare η
  have hlo := exp_lower (a := (16.1 - 7) * (74198000220 / 10 ^ 10)) 67 (by norm_num [abs_le])
  have hhi := exp_upper (a := (16.1 - 7) * (74198000250 / 10 ^ 10)) 67 (by norm_num [abs_le])
  have n1 : (2.0e29 : ℝ) < Real.exp ((16.1 - 7) * (74198000220 / 10 ^ 10)) :=
    lt_of_lt_of_le (by norm_num [tay]) hlo
  have n2 : Real.exp ((16.1 - 7) * (74198000250 / 10 ^ 10)) < (2.2e29 : ℝ) :=
    lt_of_le_of_lt hhi (by norm_num [tay])
  have m1 : Real.exp ((16.1 - 7) * (74198000220 / 10 ^ 10)) < Real.exp ((16.1 - 7) * g) :=
    Real.exp_lt_exp.mpr (by nlinarith)
  have m2 : Real.exp ((16.1 - 7) * g) < Real.exp ((16.1 - 7) * (74198000250 / 10 ^ 10)) :=
    Real.exp_lt_exp.mpr (by nlinarith)
  have hp : 0 < g / (4 * π ^ 2) := by linarith
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

/-- C13-56 (remainder): at the closure root ⟨K²⟩ = 3/(2η*), so (ε_ξ/ε_K)(3/2)/⟨K²⟩ = (ε_ξ/ε_K)η*;
with ε_ξ = ε_K this is η*. -/
theorem drain_ratio {η : ℝ} (h : Entropic.FiniteModel.ClosureStationary η) (eξ eK : ℝ) :
    eξ / eK * (3 / 2) / Entropic.FiniteModel.meanK2 η = eξ / eK * η := by
  obtain ⟨hη, hm⟩ := h
  rw [hm]; field_simp

/-- C13-85: the χ² rows sum to 2227.910 and 2228.429, with difference −0.519. -/
theorem chi2_rows :
    (589.185 : ℝ) + 11.707 + 1627.018 = 2227.910 ∧ (590.329 : ℝ) + 11.191 + 1626.909 = 2228.429 ∧
      (2227.910 : ℝ) - 2228.429 = -0.519 := by norm_num

end Entropic.AppO.Num
