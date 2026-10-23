import Entropic.Completion.GlobalRelease

/-! An algebraic floor inequality for the global spatial witness.
Caveat: the floor here eventually lies below V. It does not satisfy the
manuscript depletion-action domain K>V. This module is retained to make that
incomplete implication explicit; it is not a depletion compatibility certificate. -/
noncomputable section
namespace Entropic.Completion.GlobalFloor
open MeasureTheory GlobalBackground GlobalSpatial

def volumeBound (eta eps delta : ℝ) := (1+delta*I eta eps 1)^2/E 1
def donorBound (eta eps delta : ℝ) := Real.exp (-eta)/(2*volumeBound eta eps delta)
def floor (eta eps delta : ℝ) := min (donorBound eta eps delta/6) (V eta 1/2)

theorem integral_upper (eta eps s : ℝ) (he : 0 < eta) (hp : 0 < eps) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    I eta eps s ≤ I eta eps 1 := by
  apply intervalIntegral.integral_mono_interval (le_refl 0) hs hs1
  · apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [] with z hz
    exact div_nonneg (Real.exp_pos _).le (H_positive eta eps z he hp hz.1.le).le
  · exact weight_integrable eta eps 1 he hp (by norm_num)

theorem early_volume_bound (eta eps delta a d s : ℝ) (he : 0 < eta) (hp : 0 < eps)
    (hdelta : 0 < delta) (ha : 0 ≤ a) (hd : 0 ≤ d) (ha1 : a ≤ delta) (hd1 : d ≤ delta)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < volumeBound eta eps delta ∧ J eta eps a d s ≤ volumeBound eta eps delta := by
  have hi0 := I_nonnegative eta eps s he hp hs
  have hi1 := I_nonnegative eta eps 1 he hp (by norm_num)
  have hi := integral_upper eta eps s he hp hs hs1
  have hP := P_positive eta eps a s he hp ha hs
  have hD := P_positive eta eps d s he hp hd hs
  have hpa : P eta eps a s ≤ 1+delta*I eta eps 1 := by
    have hm := mul_le_mul ha1 hi hi0 hdelta.le
    dsimp [P]; linarith
  have hpd : P eta eps d s ≤ 1+delta*I eta eps 1 := by
    have hm := mul_le_mul hd1 hi hi0 hdelta.le
    dsimp [P]; linarith
  have htop : 0 < 1+delta*I eta eps 1 := by positivity
  have he1 : 0 < E 1 := Real.exp_pos _
  have hes : E 1 ≤ E s := Real.exp_le_exp.mpr (by linarith)
  have hprod : P eta eps a s*P eta eps d s ≤ (1+delta*I eta eps 1)^2 := by
    have hm := mul_le_mul hpa hpd hD.le htop.le
    nlinarith
  refine ⟨by dsimp [volumeBound]; positivity,?_⟩
  exact div_le_div₀ (sq_nonneg _) hprod he1 hes

theorem early_donor_bound (eta eps delta a d s : ℝ) (he : 0 < eta) (hp : 0 < eps)
    (hsmall : small eta eps delta) (ha : 0 ≤ a) (hd : 0 ≤ d) (ha1 : a ≤ delta) (hd1 : d ≤ delta)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) : donorBound eta eps delta < donor eta eps a d s := by
  obtain ⟨hv,hj⟩ := early_volume_bound eta eps delta a d s he hp hsmall.1 ha hd ha1 hd1 hs hs1
  have hc := donor_positive eta eps delta a d s he hp hsmall ha hd ha1 hd1 hs
  have hm := comoving_donor_positive eta eps delta a d s he hp hsmall ha hd ha1 hd1 hs
  apply (div_lt_iff₀ (show 0 < 2*volumeBound eta eps delta by positivity)).mpr
  have hb := mul_le_mul_of_nonneg_right hj hc.le
  nlinarith

theorem algebraic_floor_inequality (eta eps delta : ℝ) (he : 0 < eta) (hp : 0 < eps)
    (hsmall : small eta eps delta) :
    0 < floor eta eps delta ∧ ∀ a d s : ℝ,
      0 ≤ a → 0 ≤ d → a ≤ delta → d ≤ delta → 0 ≤ s →
      3*(floor eta eps delta-V eta s) < donor eta eps a d s := by
  have hi := I_nonnegative eta eps 1 he hp (by norm_num)
  have hdelta := hsmall.1
  have hvb : 0 < volumeBound eta eps delta := by dsimp [volumeBound,E]; positivity
  have hdb : 0 < donorBound eta eps delta := by dsimp [donorBound]; positivity
  have hv : 0 < V eta 1 := by
    have hh := vacuum_strictMono eta he (show (0:ℝ) < 1 by norm_num)
    simpa [V] using hh
  refine ⟨lt_min (by positivity) (by positivity),?_⟩
  intro a d s ha hd ha1 hd1 hs
  have hf1 : floor eta eps delta ≤ donorBound eta eps delta/6 := min_le_left _ _
  have hf2 : floor eta eps delta ≤ V eta 1/2 := min_le_right _ _
  by_cases hs1 : s ≤ 1
  · have hc := early_donor_bound eta eps delta a d s he hp hsmall ha hd ha1 hd1 hs hs1
    have hv0 := vacuum_nonnegative eta s he hs
    linarith
  · have hv1 := (vacuum_strictMono eta he).monotone (le_of_not_ge hs1)
    have hc := donor_positive eta eps delta a d s he hp hsmall ha hd ha1 hd1 hs
    linarith


theorem selected_action_local_domain (eta eps delta : ℝ) (he : 0 < eta) (hp : 0 < eps)
    (hsmall : small eta eps delta) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ s : ℝ, 0 ≤ s → s < radius →
      0 < floor eta eps delta-V eta s ∧ ∀ a d : ℝ,
        0 ≤ a → 0 ≤ d → a ≤ delta → d ≤ delta →
        3*(floor eta eps delta-V eta s) < donor eta eps a d s := by
  obtain ⟨hk,hbound⟩ := algebraic_floor_inequality eta eps delta he hp hsmall
  have hv : V eta 0 < floor eta eps delta := by simpa [V] using hk
  have ev := (V_deriv eta 0).continuousAt.eventually (gt_mem_nhds hv)
  obtain ⟨rd,hrd,hball⟩ := Metric.mem_nhds_iff.mp ev
  refine ⟨rd,hrd,?_⟩
  intro s hs hsr
  have hh := hball (show s ∈ Metric.ball (0:ℝ) rd by simpa [Metric.mem_ball,Real.dist_eq,abs_of_nonneg hs] using hsr)
  change V eta s < floor eta eps delta at hh
  exact ⟨sub_pos.mpr hh,fun a d ha hd ha1 hd1 => hbound a d s ha hd ha1 hd1 hs⟩

theorem current_floor_fails_global_domain (eta eps delta : ℝ) (he : 0 < eta) :
    floor eta eps delta < V eta 1 := by
  have hv : 0 < V eta 1 := by
    have hh := vacuum_strictMono eta he (show (0:ℝ) < 1 by norm_num)
    simpa [V] using hh
  have hf : floor eta eps delta ≤ V eta 1/2 := min_le_right _ _
  linarith

end Entropic.Completion.GlobalFloor
