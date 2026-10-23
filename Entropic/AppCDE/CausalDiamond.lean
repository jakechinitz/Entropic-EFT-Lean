import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

/-! Volume of a four-dimensional causal diamond (ledger C05-34). In ℝ × ℝ³ the Alexandrov
interval of half-height a = cT/2 is {(t, x) : ‖x‖ < a − |t|}; its Lebesgue volume is
(2π/3)a⁴ = π(cT)⁴/24. -/

noncomputable section
namespace Entropic.AppCDE.CausalDiamond
open MeasureTheory Real

abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem gamma_five_halves : Real.Gamma (5/2) = 3/4 * Real.sqrt Real.pi := by
  rw [show (5:ℝ)/2 = 3/2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    show (3:ℝ)/2 = 1/2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  ring

/-- Volume of a 3-ball: (4π/3) r³. -/
theorem ball_volume (r : ℝ) :
    volume (Metric.ball (0 : E3) r) = ENNReal.ofReal r ^ 3 * ENNReal.ofReal (4 * Real.pi / 3) := by
  rw [EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin]
  congr 2
  rw [show ((3:ℕ):ℝ) / 2 + 1 = 5/2 by norm_num, gamma_five_halves]
  have hs : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hs0 : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  rw [show Real.sqrt Real.pi ^ 3 = Real.pi * Real.sqrt Real.pi by rw [pow_succ, hs]]
  field_simp

def diamond (a : ℝ) : Set (ℝ × E3) := {p | ‖p.2‖ < a - |p.1|}

theorem diamond_open (a : ℝ) : IsOpen (diamond a) :=
  isOpen_lt (by fun_prop) (by fun_prop)

theorem slice (a t : ℝ) : Prod.mk t ⁻¹' diamond a = Metric.ball (0 : E3) (a - |t|) := by
  ext x; simp [diamond]

def g (a t : ℝ) : ℝ := max (a - |t|) 0

theorem g_cont (a : ℝ) : Continuous (g a) := by unfold g; fun_prop

theorem g_support {a t : ℝ} (ha : 0 < a) (ht : t ∉ Set.Icc (-a) a) : g a t ^ 3 = 0 := by
  have : a ≤ |t| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at ht
    rcases ht with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  unfold g; rw [max_eq_right (by linarith)]; norm_num

theorem integral_g (a : ℝ) (ha : 0 < a) : ∫ t, g a t ^ 3 = a ^ 4 / 2 := by
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc (-a) a)
    (fun t ht => g_support ha ht), MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  have hc : Continuous fun t => g a t ^ 3 := (g_cont a).pow 3
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : ∫ t in (-a)..0, g a t ^ 3 = ∫ t in (-a)..0, (a + t) ^ 3 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    simp only [g]; rw [abs_of_nonpos ht.2, max_eq_left (by linarith [ht.1])]; ring
  have h2 : ∫ t in (0:ℝ)..a, g a t ^ 3 = ∫ t in (0:ℝ)..a, (a - t) ^ 3 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le ha.le] at ht
    simp only [g]; rw [abs_of_nonneg ht.1, max_eq_left (by linarith [ht.2])]
  rw [h1, h2, intervalIntegral.integral_comp_add_left (fun x => x ^ 3),
    intervalIntegral.integral_comp_sub_left (fun x => x ^ 3)]
  simp only [add_neg_cancel, add_zero, sub_zero, sub_self, integral_pow]
  ring

/-- C05-34: vol{(t,x) ∈ ℝ × ℝ³ : ‖x‖ < a − |t|} = (2π/3)a⁴; with a = cT/2 this is π(cT)⁴/24. -/
theorem diamond_volume (a : ℝ) (ha : 0 < a) :
    volume (diamond a) = ENNReal.ofReal (2 * Real.pi / 3 * a ^ 4) := by
  rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_apply (diamond_open a).measurableSet]
  simp_rw [slice, ball_volume]
  have hofr : ∀ t, ENNReal.ofReal (a - |t|) ^ 3 = ENNReal.ofReal (g a t ^ 3) := by
    intro t
    have hg : 0 ≤ g a t := le_max_right _ _
    rw [ENNReal.ofReal_pow hg]
    congr 1
    unfold g
    by_cases h : 0 ≤ a - |t|
    · rw [max_eq_left h]
    · push_neg at h
      rw [max_eq_right h.le, ENNReal.ofReal_of_nonpos h.le, ENNReal.ofReal_zero]
  simp_rw [hofr]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  have hint : Integrable (fun t => g a t ^ 3) := by
    apply Continuous.integrable_of_hasCompactSupport ((g_cont a).pow 3)
    exact HasCompactSupport.intro isCompact_Icc (fun t ht => g_support ha ht)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun t => pow_nonneg (le_max_right _ _) 3)), integral_g a ha,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1; ring

theorem diamond_volume_cT (cT : ℝ) (h : 0 < cT) :
    volume (diamond (cT / 2)) = ENNReal.ofReal (Real.pi * cT ^ 4 / 24) := by
  rw [diamond_volume _ (by positivity)]; congr 1; ring

end Entropic.AppCDE.CausalDiamond
