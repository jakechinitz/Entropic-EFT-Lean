import Mathlib

/-! Global positive background in e-fold coordinate s>=0 with lapse 1/H(s).
ds_metric^2=-H(s)^(-2) ds^2+exp(2s) dx^2, c=8*pi*G=1.
The chosen hazard is Gamma=H, so F=1-exp(-s). This is an existence witness,
not an independently measured assembly law. All component equations use this
same lapse, H, stock and vacuum. No inhomogeneous global continuation is claimed. -/
noncomputable section
set_option linter.unnecessarySeqFocus false
namespace Entropic.Completion.GlobalBackground
open MeasureTheory

def F (s : ℝ) := 1-Real.exp (-s)
def b (eps s : ℝ) := eps*Real.exp (-3*s)
def C (eta s : ℝ) := Real.exp (-3*s-eta*F s)
def sourceS (eta s : ℝ) := eta*C eta s*Real.exp (-s)
def V (eta s : ℝ) := ∫ z in (0:ℝ)..s, sourceS eta z
def total (eta eps s : ℝ) := b eps s+C eta s+V eta s
def H (eta eps s : ℝ) := Real.sqrt (total eta eps s/3)
def u (eta s : ℝ) := (1-F s)*C eta s
def R (eta s : ℝ) := F s*C eta s
def Q (eta eps s : ℝ) := H eta eps s*sourceS eta s
def properTime (eta eps s : ℝ) := ∫ z in (0:ℝ)..s, 1/H eta eps z

theorem F_deriv (s : ℝ) : HasDerivAt F (Real.exp (-s)) s := by
  convert (((hasDerivAt_id s).neg).exp).const_sub 1 using 1 <;> (try funext x) <;> (try dsimp [F]) <;> ring

theorem b_deriv (eps s : ℝ) : HasDerivAt (b eps) (-3*b eps s) s := by
  convert ((((hasDerivAt_id s).const_mul (-3)).exp).const_mul eps) using 1 <;> (try funext x) <;> (try dsimp [b]) <;> ring

theorem C_deriv (eta s : ℝ) : HasDerivAt (C eta) (-3*C eta s-sourceS eta s) s := by
  convert (((hasDerivAt_id s).const_mul (-3)).sub ((F_deriv s).const_mul eta)).exp using 1 <;> (try funext x) <;>
    (try dsimp [C,sourceS]) <;> ring

theorem source_continuous (eta : ℝ) : Continuous (sourceS eta) := by
  unfold sourceS C F; fun_prop

theorem V_deriv (eta s : ℝ) : HasDerivAt (V eta) (sourceS eta s) s :=
  intervalIntegral.integral_hasDerivAt_right ((source_continuous eta).intervalIntegrable _ _)
    ((source_continuous eta).stronglyMeasurableAtFilter _ _) (source_continuous eta).continuousAt

theorem total_deriv (eta eps s : ℝ) : HasDerivAt (total eta eps) (-3*(b eps s+C eta s)) s := by
  convert ((b_deriv eps s).add (C_deriv eta s)).add (V_deriv eta s) using 1 <;> (try funext x) <;> (try dsimp [total]) <;> ring

theorem fraction_bounds (s : ℝ) (hs : 0 ≤ s) : 0 ≤ F s ∧ F s<1 := by
  have hp := Real.exp_pos (-s)
  have h1 := Real.exp_le_one_iff.mpr (show -s ≤ 0 by linarith)
  dsimp [F]; constructor <;> linarith

theorem source_positive (eta s : ℝ) (he : 0<eta) : 0<sourceS eta s := by
  dsimp [sourceS,C]; positivity

theorem vacuum_nonnegative (eta s : ℝ) (he : 0<eta) (hs : 0 ≤ s) : 0 ≤ V eta s :=
  intervalIntegral.integral_nonneg_of_forall hs (fun z => (source_positive eta z he).le)

theorem fields_positive (eta eps s : ℝ) (he : 0<eta) (hp : 0<eps) (hs : 0 ≤ s) :
    0<b eps s ∧ 0<C eta s ∧ 0<u eta s ∧ 0 ≤ R eta s ∧ 0 ≤ V eta s := by
  have hb : 0<b eps s := mul_pos hp (Real.exp_pos _)
  have hc : 0<C eta s := Real.exp_pos _
  obtain ⟨hf,hf1⟩ := fraction_bounds s hs
  exact ⟨hb,hc,mul_pos (sub_pos.mpr hf1) hc,mul_nonneg hf hc.le,vacuum_nonnegative eta s he hs⟩

theorem H_positive (eta eps s : ℝ) (he : 0<eta) (hp : 0<eps) (hs : 0 ≤ s) : 0<H eta eps s := by
  obtain ⟨hb,hc,_,_,hv⟩ := fields_positive eta eps s he hp hs
  apply Real.sqrt_pos.mpr
  dsimp [total]; positivity

theorem friedmann (eta eps s : ℝ) (he : 0<eta) (hp : 0<eps) (hs : 0 ≤ s) :
    3*(H eta eps s)^2=b eps s+C eta s+V eta s := by
  obtain ⟨hb,hc,_,_,hv⟩ := fields_positive eta eps s he hp hs
  have hz : 0 ≤ total eta eps s/3 := by dsimp [total]; positivity
  rw [H,Real.sq_sqrt hz]; dsimp [total]; ring

theorem H_deriv (eta eps s : ℝ) (he : 0<eta) (hp : 0<eps) (hs : 0 ≤ s) :
    HasDerivAt (H eta eps) (-(b eps s+C eta s)/(2*H eta eps s)) s := by
  have hpos := H_positive eta eps s he hp hs
  have hx : total eta eps s/3≠0 := by
    intro hz; have : H eta eps s=0 := by simp [H,hz]
    linarith
  convert ((total_deriv eta eps s).div_const 3).sqrt hx using 1 <;> (try funext x) <;>
    (try dsimp [H]) <;> ring

theorem raychaudhuri (eta eps s : ℝ) (he : 0<eta) (hp : 0<eps) (hs : 0 ≤ s) :
    H eta eps s*deriv (H eta eps) s=-(b eps s+C eta s)/2 := by
  rw [(H_deriv eta eps s he hp hs).deriv]
  have hz := (H_positive eta eps s he hp hs).ne'
  field_simp <;> ring

theorem release_equations (eta eps s : ℝ) :
    u eta s+R eta s=C eta s ∧
    H eta eps s*deriv F s=H eta eps s*(1-F s) ∧
    Q eta eps s=eta*H eta eps s*u eta s ∧
    H eta eps s*deriv (C eta) s+3*H eta eps s*C eta s= -Q eta eps s ∧
    H eta eps s*deriv (V eta) s=Q eta eps s := by
  rw [(F_deriv s).deriv,(C_deriv eta s).deriv,(V_deriv eta s).deriv]
  dsimp [u,R,F,Q,sourceS]
  exact ⟨by ring,by ring,by ring,by ring,by ring⟩

theorem formation_allocation (eta eps s : ℝ) (hp : eps≠0) :
    C eta s=(b eps s/eps)*Real.exp (-eta*F s) := by
  dsimp [C,b]
  rw [show -3*s-eta*F s=(-3*s)+(-eta*F s) by ring,Real.exp_add]
  field_simp

theorem vacuum_strictMono (eta : ℝ) (he : 0<eta) : StrictMono (V eta) := by
  apply strictMono_of_deriv_pos
  intro s; rw [(V_deriv eta s).deriv]; exact source_positive eta s he

theorem capacity_strictAnti (eta : ℝ) (he : 0<eta) : StrictAnti (C eta) := by
  apply strictAnti_of_deriv_neg
  intro s; rw [(C_deriv eta s).deriv]
  have hc : 0<C eta s := Real.exp_pos _
  have hq := source_positive eta s he
  linarith

def floor (eta : ℝ) := min (C eta 1/6) (V eta 1/2)

-- This inequality alone does NOT include the additional selected-action condition K>V.
theorem algebraic_floor_inequality (eta : ℝ) (he : 0<eta) :
    0<floor eta ∧ ∀ s : ℝ, 0 ≤ s → 3*(floor eta-V eta s)<C eta s := by
  have hc : 0<C eta 1 := Real.exp_pos _
  have hv : 0<V eta 1 := by
    have hh := vacuum_strictMono eta he (show (0:ℝ)<1 by norm_num)
    simpa [V] using hh
  refine ⟨lt_min (by positivity) (by positivity),?_⟩
  intro s hs
  have hf1 : floor eta ≤ C eta 1/6 := min_le_left _ _
  have hf2 : floor eta ≤ V eta 1/2 := min_le_right _ _
  by_cases hle : s ≤ 1
  · have hc1 := (capacity_strictAnti eta he).antitone hle
    have hv0 := vacuum_nonnegative eta s he hs
    linarith
  · have hv1 := (vacuum_strictMono eta he).monotone (le_of_not_ge hle)
    have hcs : 0<C eta s := Real.exp_pos _
    linarith

theorem total_nonincreasing (eta eps : ℝ) (hp : 0<eps) : Antitone (total eta eps) := by
  apply antitone_of_deriv_nonpos
  · intro s; exact (total_deriv eta eps s).differentiableAt
  · intro s; rw [(total_deriv eta eps s).deriv]
    have hb : 0<b eps s := mul_pos hp (Real.exp_pos _)
    have hc : 0<C eta s := Real.exp_pos _
    linarith

theorem H_continuous (eta eps : ℝ) : Continuous (H eta eps) := by
  have hc : Continuous (total eta eps) := continuous_iff_continuousAt.mpr (fun s => (total_deriv eta eps s).continuousAt)
  exact (hc.div_const 3).sqrt

theorem H_upper (eta eps s : ℝ) (hp : 0<eps) (hs : 0 ≤ s) : H eta eps s ≤ H eta eps 0 := by
  apply Real.sqrt_le_sqrt
  exact div_le_div_of_nonneg_right (total_nonincreasing eta eps hp hs) (by norm_num)

theorem lapse_integrable (eta eps s : ℝ) (he : 0<eta) (hp : 0<eps) (hs : 0 ≤ s) :
    IntervalIntegrable (fun z => 1/H eta eps z) volume 0 s := by
  have hc : ContinuousOn (fun z => 1/H eta eps z) (Set.Icc 0 s) :=
    continuousOn_const.div (H_continuous eta eps).continuousOn (fun z hz => (H_positive eta eps z he hp hz.1).ne')
  exact hc.intervalIntegrable_of_Icc hs

theorem proper_time_lower (eta eps s : ℝ) (he : 0<eta) (hp : 0<eps) (hs : 0 ≤ s) :
    s/H eta eps 0 ≤ properTime eta eps s := by
  have h0 := H_positive eta eps 0 he hp (by norm_num)
  have hh := intervalIntegral.integral_mono_on hs (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 1/H eta eps 0) volume 0 s)
    (lapse_integrable eta eps s he hp hs) (fun z hz => one_div_le_one_div_of_le (H_positive eta eps z he hp hz.1) (H_upper eta eps z hp hz.1))
  simpa [properTime,div_eq_mul_inv] using hh

theorem unbounded_future_proper_time (eta eps T : ℝ) (he : 0<eta) (hp : 0<eps) :
    ∃ s : ℝ, 0<s ∧ T<properTime eta eps s := by
  have h0 := H_positive eta eps 0 he hp (by norm_num)
  let s := (max T 0+1)*H eta eps 0
  have hs : 0<s := mul_pos (by linarith [le_max_right T 0]) h0
  refine ⟨s,hs,?_⟩
  have hl := proper_time_lower eta eps s he hp hs.le
  have heq : s/H eta eps 0=max T 0+1 := by dsimp [s]; field_simp
  rw [heq] at hl
  linarith [le_max_left T 0]

end Entropic.Completion.GlobalBackground
