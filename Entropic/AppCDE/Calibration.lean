import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Appendix C.6 event-volume calibration (ledger C05-38, -39, -40, -44, -45).
Units L_* = 1. v_ev = (π/24)m₄⁴, a_reg = (3√2 v_ev)^{1/3} (= (6√2 V_site)^{1/3} with
V_site = v_ev/2), A_ch = (√3/4)a_reg², G₀/G_* = A_ch/(4 ln 2). -/

noncomputable section
namespace Entropic.AppCDE.Calibration
open Real

def vev (m : ℝ) : ℝ := Real.pi / 24 * m ^ 4
def areg (m : ℝ) : ℝ := (3 * Real.sqrt 2 * vev m) ^ (1/3 : ℝ)
def Ach (m : ℝ) : ℝ := Real.sqrt 3 / 4 * areg m ^ 2
def G0 (m : ℝ) : ℝ := Ach m / (4 * Real.log 2)

theorem vev_pos {m : ℝ} (hm : 0 < m) : 0 < vev m := by unfold vev; positivity

theorem areg_pos {m : ℝ} (hm : 0 < m) : 0 < areg m := by
  unfold areg; have := vev_pos hm; positivity

theorem areg_cube {m : ℝ} (hm : 0 < m) : areg m ^ 3 = 3 * Real.sqrt 2 * vev m := by
  unfold areg
  have hx : 0 ≤ 3 * Real.sqrt 2 * vev m := by have := vev_pos hm; positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

/-- C05-38: G₀/G_* = (√3/(16 ln 2))(3√2 v_ev)^{2/3}. -/
theorem G0_formula {m : ℝ} (hm : 0 < m) :
    G0 m = Real.sqrt 3 / (16 * Real.log 2) * (3 * Real.sqrt 2 * vev m) ^ (2/3 : ℝ) := by
  unfold G0 Ach areg
  have hx : 0 ≤ 3 * Real.sqrt 2 * vev m := by have := vev_pos hm; positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  norm_num; field_simp; ring

/-- Cube form: (G₀/G_*)³ = C m⁸ with C = (√3/4)³(3√2π/24)²/(4 ln 2)³; so G₀/G_* = C^{1/3} m^{8/3}. -/
def C3 : ℝ := (Real.sqrt 3 / 4) ^ 3 * (3 * Real.sqrt 2 * Real.pi / 24) ^ 2 / (4 * Real.log 2) ^ 3

theorem G0_cube {m : ℝ} (hm : 0 < m) : G0 m ^ 3 = C3 * m ^ 8 := by
  unfold G0 Ach C3
  rw [div_pow, mul_pow, show areg m ^ 2 = areg m ^ 2 from rfl,
    show (areg m ^ 2) ^ 3 = (areg m ^ 3) ^ 2 by ring, areg_cube hm]
  unfold vev; ring

theorem sqrt2_bounds : (1.41421356237 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.41421356238 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem sqrt3_bounds : (1.73205080756 : ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < 1.73205080757 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- C ∈ (0.0011748840, 0.0011748855). -/
theorem C3_bounds : (0.0011748840 : ℝ) < C3 ∧ C3 < 0.0011748855 := by
  obtain ⟨s2l, s2h⟩ := sqrt2_bounds
  obtain ⟨s3l, s3h⟩ := sqrt3_bounds
  have pl := Real.pi_gt_d6; have ph := Real.pi_lt_d6
  have ll := Real.log_two_gt_d9; have lh := Real.log_two_lt_d9
  unfold C3
  have hden : 0 < (4 * Real.log 2) ^ 3 := by positivity
  have n1 : (1.73205080756 / 4 : ℝ) ^ 3 * (3 * 1.41421356237 * 3.141592 / 24) ^ 2 <
      (Real.sqrt 3 / 4) ^ 3 * (3 * Real.sqrt 2 * Real.pi / 24) ^ 2 := by
    gcongr
  have n2 : (Real.sqrt 3 / 4) ^ 3 * (3 * Real.sqrt 2 * Real.pi / 24) ^ 2 <
      (1.73205080757 / 4 : ℝ) ^ 3 * (3 * 1.41421356238 * 3.141593 / 24) ^ 2 := by
    gcongr
  have d1 : (4 * 0.6931471803 : ℝ) ^ 3 < (4 * Real.log 2) ^ 3 := by gcongr
  have d2 : (4 * Real.log 2) ^ 3 < (4 * 0.6931471808 : ℝ) ^ 3 := by gcongr
  constructor
  · rw [lt_div_iff₀ hden]; nlinarith
  · rw [div_lt_iff₀ hden]; nlinarith

/-- C05-38: G₀/G_* = K m₄^{8/3} with K = C^{1/3} ∈ (0.1055192, 0.1055193)
(paper: 0.1055… m₄^{8/3}; K = (√3/(16 ln 2))(3√2π/24)^{2/3} = 0.10551927). -/
theorem K_bounds : (0.1055192 : ℝ) < C3 ^ (1/3 : ℝ) ∧ C3 ^ (1/3 : ℝ) < 0.1055193 := by
  obtain ⟨c1, c2⟩ := C3_bounds
  have hC : 0 < C3 := lt_trans (by norm_num) c1
  have hK : (C3 ^ (1/3 : ℝ)) ^ 3 = C3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hC.le]; norm_num
  have hK0 : 0 < C3 ^ (1/3 : ℝ) := Real.rpow_pos_of_pos hC _
  constructor
  · by_contra h; push_neg at h
    have := pow_le_pow_left₀ hK0.le h 3; rw [hK] at this; nlinarith
  · by_contra h; push_neg at h
    have := pow_le_pow_left₀ (by norm_num) h 3; rw [hK] at this; nlinarith

theorem G0_pos {m : ℝ} (hm : 0 < m) : 0 < G0 m := by
  unfold G0 Ach; have := areg_pos hm
  have : 0 < Real.log 2 := Real.log_pos (by norm_num); positivity

theorem G0_eq_K {m : ℝ} (hm : 0 < m) : G0 m = C3 ^ (1/3 : ℝ) * m ^ (8/3 : ℝ) := by
  have hC : 0 < C3 := lt_trans (by norm_num) C3_bounds.1
  have h3 := G0_cube hm
  have hG := G0_pos hm
  have : G0 m = (C3 * m ^ 8) ^ (1/3 : ℝ) := by
    rw [← h3, ← Real.rpow_natCast, ← Real.rpow_mul hG.le]; norm_num
  rw [this, Real.mul_rpow hC.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hm.le]
  norm_num

/-- G₀/G_* is strictly increasing in m₄. -/
theorem G0_strictMono : StrictMonoOn G0 (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0:ℝ) < a := ha; have hb' : (0:ℝ) < b := hb
  have hC : 0 < C3 := lt_trans (by norm_num) C3_bounds.1
  have h8 : a ^ 8 < b ^ 8 := pow_lt_pow_left₀ hab ha'.le (by norm_num)
  have h3 : G0 a ^ 3 < G0 b ^ 3 := by rw [G0_cube ha', G0_cube hb']; nlinarith
  exact (pow_lt_pow_iff_left₀ (G0_pos ha').le (G0_pos hb').le (by norm_num)).mp h3

/-- C05-40: the calibration root G₀ = G_* lies in m₄ ∈ (2.3240, 2.3242) and is unique;
over m₄ ∈ [2.25, 2.45], G₀/G_* runs from 0.917 to 1.151. -/
theorem calibration_root :
    G0 2.3240 < 1 ∧ 1 < G0 2.3242 ∧ (∃! m, 0 < m ∧ G0 m = 1) ∧
      0.917 < G0 2.25 ∧ G0 2.25 < 0.918 ∧ 1.151 < G0 2.45 ∧ G0 2.45 < 1.152 := by
  obtain ⟨c1, c2⟩ := C3_bounds
  have cube_lt : ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y → x ^ 3 < y ^ 3 → x < y := fun hx hy h =>
    (pow_lt_pow_iff_left₀ hx hy (by norm_num)).mp h
  have r1 : G0 2.3240 < 1 := cube_lt (G0_pos (by norm_num)).le (by norm_num)
    (by rw [G0_cube (by norm_num)]; nlinarith)
  have r2 : 1 < G0 2.3242 := cube_lt (by norm_num) (G0_pos (by norm_num)).le
    (by rw [G0_cube (by norm_num)]; nlinarith)
  refine ⟨r1, r2, ?_, ?_, ?_, ?_, ?_⟩
  · -- existence by IVT on [2.3240, 2.3242], uniqueness by strict monotonicity
    have hcont : ContinuousOn G0 (Set.Icc 2.3240 2.3242) := by
      unfold G0 Ach areg vev
      apply ContinuousOn.div_const
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.pow
      apply ContinuousOn.rpow_const (by fun_prop)
      intro x _; right; norm_num
    obtain ⟨m, hm, hm1⟩ := intermediate_value_Icc (by norm_num) hcont ⟨r1.le, r2.le⟩
    refine ⟨m, ⟨lt_of_lt_of_le (by norm_num) hm.1, hm1⟩, fun y ⟨hy, hy1⟩ => ?_⟩
    have hm0 : (0:ℝ) < m := lt_of_lt_of_le (by norm_num) hm.1
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := G0_strictMono hy hm0 h; linarith
    · have := G0_strictMono hm0 hy h; linarith
  all_goals first
    | exact cube_lt (by norm_num) (G0_pos (by norm_num)).le (by rw [G0_cube (by norm_num)]; nlinarith)
    | exact cube_lt (G0_pos (by norm_num)).le (by norm_num) (by rw [G0_cube (by norm_num)]; nlinarith)

/-- C05-39: at m₄ = 2.35: v_ev = 3.99217968, a_reg = 2.56812078, A_ch = 2.85582456,
G₀/G_* = 1.03002098. -/
theorem calibration_235 :
    3.992179682 < vev 2.35 ∧ vev 2.35 < 3.992179683 ∧
      2.5681207753 < areg 2.35 ∧ areg 2.35 < 2.5681207757 ∧
      2.855824559 < Ach 2.35 ∧ Ach 2.35 < 2.855824563 ∧
      1.0300209815 < G0 2.35 ∧ G0 2.35 < 1.0300209850 := by
  have pl := Real.pi_gt_d20; have ph := Real.pi_lt_d20
  obtain ⟨s2l, s2h⟩ := sqrt2_bounds
  obtain ⟨s3l, s3h⟩ := sqrt3_bounds
  have v1 : 3.992179682 < vev 2.35 := by unfold vev; nlinarith
  have v2 : vev 2.35 < 3.992179683 := by unfold vev; nlinarith
  have ha := areg_cube (m := 2.35) (by norm_num)
  have hap := areg_pos (m := 2.35) (by norm_num)
  have a1 : 2.5681207753 < areg 2.35 := by
    by_contra h; push_neg at h
    have : areg 2.35 ^ 3 ≤ 2.5681207753 ^ 3 := pow_le_pow_left₀ hap.le h 3
    nlinarith
  have a2 : areg 2.35 < 2.5681207757 := by
    by_contra h; push_neg at h
    have : (2.5681207757:ℝ) ^ 3 ≤ areg 2.35 ^ 3 := pow_le_pow_left₀ (by norm_num) h 3
    nlinarith
  have A1 : 2.855824559 < Ach 2.35 := by unfold Ach; nlinarith
  have A2 : Ach 2.35 < 2.855824563 := by unfold Ach; nlinarith
  have ll := Real.log_two_gt_d9; have lh := Real.log_two_lt_d9
  have hl : 0 < 4 * Real.log 2 := by positivity
  refine ⟨v1, v2, a1, a2, A1, A2, ?_, ?_⟩
  · unfold G0; rw [lt_div_iff₀ hl]; nlinarith
  · unfold G0; rw [div_lt_iff₀ hl]; nlinarith

/-- C05-44 (arithmetic part): √(3.99218/1.03002) ∈ (1.968, 1.969), the displacement in units of
L_* that would restore the cut normalization under the (v_ev/L_*⁴)(L_*/d)² scaling. -/
theorem displacement_ratio : 1.968 < Real.sqrt (3.99218 / 1.03002) ∧ Real.sqrt (3.99218 / 1.03002) < 1.969 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- C05-45: tick-unit Einstein-continuation coefficients κ = 1/(2S_∞), γ = 1/(16πG₀S_∞²) at
S_∞ = 0.04614825156, G₀ = 1.03002098: κ = 10.83465, γ = 9.06930, and κ/(γS_∞) = 8πG₀. -/
theorem einstein_coefficients :
    let S : ℝ := 0.04614825156
    let G : ℝ := 1.03002098
    10.834645 < 1 / (2 * S) ∧ 1 / (2 * S) < 10.834650 ∧
      9.069295 < 1 / (16 * Real.pi * G * S ^ 2) ∧ 1 / (16 * Real.pi * G * S ^ 2) < 9.069297 ∧
      (1 / (2 * S)) / ((1 / (16 * Real.pi * G * S ^ 2)) * S) = 8 * Real.pi * G := by
  intro S G
  have pl := Real.pi_gt_d20; have ph := Real.pi_lt_d20
  have hp : 0 < 16 * Real.pi * G * S ^ 2 := by simp only [G, S]; positivity
  refine ⟨by norm_num [S], by norm_num [S], ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hp]; simp only [G, S]; nlinarith
  · rw [div_lt_iff₀ hp]; simp only [G, S]; nlinarith
  · simp only [G, S]; field_simp; ring

end Entropic.AppCDE.Calibration
