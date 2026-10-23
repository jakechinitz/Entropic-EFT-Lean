import Entropic.Completion.Spatial

/-! The same inhomogeneous metric and dust density carry positive baryons,
donor, retained stock, active release and the exponential formation ledger.
This is local existence on the dust branch, not global depletion or a fitted
assembly kernel. The release rate is explicitly constructed from the solution. -/
noncomputable section
set_option linter.unnecessarySeqFocus false
namespace Entropic.Completion.SpatialRelease
open Entropic.Completion.Spatial

def baryon (eps r t : ℝ) := eps/(1+eps)*rho r 0/J r t
def donor (eps r t : ℝ) := rho r t-baryon eps r t
def comoving (eps r t : ℝ) := J r t*donor eps r t
def fraction (eta eps r t : ℝ) := -Real.log (comoving eps r t/donor eps r 0)/eta
def unreleased (eta eps r t : ℝ) := (1-fraction eta eps r t)*donor eps r t
def retained (eta eps r t : ℝ) := fraction eta eps r t*donor eps r t
def rate (eta eps r t : ℝ) := Q t/(eta*donor eps r t*(1-fraction eta eps r t))
def floor (eps : ℝ) := 1/(12*(1+eps))

theorem initial_density_lower (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) : 1/2 < rho r 0 := by
  have hs : r^2 ≤ 1 := by nlinarith
  have hh : 9/10 ≤ h r := by dsimp [h]; nlinarith
  have hj : 23/30 ≤ j r := by dsimp [j]; nlinarith
  have hp : 0 ≤ (h r-9/10)*(j r-23/30) := mul_nonneg (by linarith) (by linarith)
  rw [(initial_geometry r).2.2.2.1]
  nlinarith

theorem initial_conditions (eps r : ℝ) (he : 0<eps) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    0<baryon eps r 0 ∧ 0<donor eps r 0 ∧ donor eps r 0=baryon eps r 0/eps := by
  have hp : 0<rho r 0 := by linarith [initial_density_lower r hr hr1]
  have hz : 1+eps≠0 := by positivity
  have hc : donor eps r 0=rho r 0/(1+eps) := by
    rw [donor,baryon,(initial_geometry r).2.2.1]; field_simp <;> ring
  refine ⟨?_,by rw [hc]; positivity,?_⟩
  · rw [baryon,(initial_geometry r).2.2.1]; positivity
  · rw [hc,baryon,(initial_geometry r).2.2.1]; field_simp <;> ring

theorem baryon_deriv (eps r t : ℝ) (ha : A r t≠0) (hb : B r t≠0) :
    HasDerivAt (baryon eps r) (-theta r t*baryon eps r t) t := by
  have hz : J r t≠0 := mul_ne_zero ha hb
  by_cases he0 : 1+eps=0
  · have hfun : baryon eps r=fun _ => 0 := by funext x; simp [baryon,he0]
    rw [hfun]; simpa using (hasDerivAt_const t (0:ℝ))
  convert (hasDerivAt_const t (eps/(1+eps)*rho r 0)).div (volume_deriv r t ha hb) hz using 1 <;>
    first | rfl | (funext x; rfl) | (simp only [baryon]; field_simp [hz,he0,ha,hb] <;> ring)

theorem donor_deriv (eps r t : ℝ) (ha : A r t≠0) (hb : B r t≠0) :
    HasDerivAt (donor eps r) (-theta r t*donor eps r t-Q t) t := by
  convert (density_deriv r t ha hb).sub (baryon_deriv eps r t ha hb) using 1 <;> (try funext x) <;> (try dsimp [donor]) <;> ring

theorem comoving_deriv (eps r t : ℝ) (ha : A r t≠0) (hb : B r t≠0) :
    HasDerivAt (comoving eps r) (-J r t*Q t) t := by
  convert (volume_deriv r t ha hb).mul (donor_deriv eps r t ha hb) using 1 <;> (try funext x) <;>
    (try dsimp [comoving]) <;> ring

theorem fraction_zero (eta eps r : ℝ) (he : 0<eps) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    fraction eta eps r 0=0 := by
  have hp := (initial_conditions eps r he hr hr1).2.1
  simp [fraction,comoving,(initial_geometry r).2.2.1,hp.ne']

theorem fraction_deriv (eta eps r t : ℝ) (hEta : eta≠0) (he : 0<eps) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (ha : A r t≠0) (hb : B r t≠0) (hc : donor eps r t≠0) :
    HasDerivAt (fraction eta eps r) (Q t/(eta*donor eps r t)) t := by
  have h0 := (initial_conditions eps r he hr hr1).2.1.ne'
  have hJ : J r t≠0 := mul_ne_zero ha hb
  have hx : comoving eps r t/donor eps r 0≠0 := div_ne_zero (mul_ne_zero hJ hc) h0
  convert ((((comoving_deriv eps r t ha hb).div_const (donor eps r 0)).log hx).neg).div_const eta using 1
  all_goals try (first | rfl | (funext x; rfl))
  dsimp [comoving]; field_simp [hEta,hJ,h0,hc,ha,hb] <;> ring

theorem physical_allocation (eta eps r t : ℝ) (hEta : eta≠0) (he : 0<eps)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ht : 0 ≤ t) (hc : 0<donor eps r t) :
    donor eps r t=(baryon eps r t/eps)*Real.exp (-eta*fraction eta eps r t) := by
  obtain ⟨ha,hb⟩ := AB_positive r t hr hr1 ht
  have hJ : 0<J r t := mul_pos ha hb
  have h0 := (initial_conditions eps r he hr hr1).2.1
  have hx : 0<comoving eps r t/donor eps r 0 := div_pos (mul_pos hJ hc) h0
  have heq : -eta*fraction eta eps r t=Real.log (comoving eps r t/donor eps r 0) := by
    dsimp [fraction]; field_simp
  rw [heq,Real.exp_log hx]
  have hform := (initial_conditions eps r he hr hr1).2.2
  rw [hform]
  dsimp [baryon,comoving]
  rw [(initial_geometry r).2.2.1]
  have hrho : rho r 0≠0 := by linarith [initial_density_lower r hr hr1]
  field_simp <;> ring

theorem comoving_strictly_decreases (eps r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    StrictAntiOn (comoving eps r) (Set.Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · intro t ht
    obtain ⟨ha,hb⟩ := AB_positive r t hr hr1 ht
    exact (comoving_deriv eps r t ha.ne' hb.ne').continuousAt.continuousWithinAt
  · intro t ht
    have ht' : 0 ≤ t := (show 0<t by simpa using ht).le
    obtain ⟨ha,hb⟩ := AB_positive r t hr hr1 ht'
    rw [(comoving_deriv eps r t ha.ne' hb.ne').deriv]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos ha hb)) (source_positive t ht')

theorem fraction_positive (eta eps r t : ℝ) (hEta : 0<eta) (he : 0<eps)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ht : 0<t) (hc : 0<donor eps r t) :
    0<fraction eta eps r t := by
  have h0 := (initial_conditions eps r he hr hr1).2.1
  have hm := comoving_strictly_decreases eps r hr hr1 (by simp) ht.le ht
  have hu : comoving eps r t/donor eps r 0<1 := by
    apply (div_lt_one h0).mpr
    simpa [comoving,(initial_geometry r).2.2.1] using hm
  obtain ⟨ha,hb⟩ := AB_positive r t hr hr1 ht.le
  have hp : 0<comoving eps r t/donor eps r 0 := div_pos (mul_pos (mul_pos ha hb) hc) h0
  exact div_pos (neg_pos.mpr (Real.log_neg hp hu)) hEta

theorem positive_interval (eta eps r : ℝ) (hEta : 0<eta) (he : 0<eps)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ∃ radius : ℝ, 0<radius ∧ ∀ t, 0<t → t<radius →
      0<donor eps r t ∧ 0<fraction eta eps r t ∧ fraction eta eps r t<1 ∧
      0<floor eps-V t ∧ 3*(floor eps-V t)<donor eps r t := by
  have ha : A r 0≠0 := by rw [(initial_geometry r).1]; norm_num
  have hb : B r 0≠0 := by rw [(initial_geometry r).2.1]; norm_num
  have h0 := (initial_conditions eps r he hr hr1).2.1
  have cc := (donor_deriv eps r 0 ha hb).continuousAt
  have cf := (fraction_deriv eta eps r 0 hEta.ne' he hr hr1 ha hb h0.ne').continuousAt
  have hfloor : 0<floor eps := by dsimp [floor]; positivity
  have hmargin : 3*floor eps<donor eps r 0 := by
    have hd := initial_density_lower r hr hr1
    have hz : 0<1+eps := by positivity
    have hc : donor eps r 0=rho r 0/(1+eps) := by
      rw [donor,baryon,(initial_geometry r).2.2.1]; field_simp <;> ring
    rw [hc]; dsimp [floor]; apply (lt_div_iff₀ hz).mpr
    have hh : 3*(1/(12*(1+eps)))*(1+eps)=1/4 := by field_simp <;> ring
    rw [hh]; linarith
  have e1 := cc.eventually (lt_mem_nhds h0)
  have e2 := cf.eventually (gt_mem_nhds (show fraction eta eps r 0<1 by rw [fraction_zero eta eps r he hr hr1]; norm_num))
  have e3 := (vacuum_deriv 0).continuousAt.eventually (gt_mem_nhds (show V 0<floor eps by simpa [V] using hfloor))
  have cm : ContinuousAt (fun t => donor eps r t-3*(floor eps-V t)) 0 :=
    cc.sub (continuousAt_const.mul (continuousAt_const.sub (vacuum_deriv 0).continuousAt))
  have e4 := cm.eventually (lt_mem_nhds (show 0<donor eps r 0-3*(floor eps-V 0) by simp only [V]; nlinarith))
  have ev : ∀ᶠ t in nhds (0:ℝ), 0<donor eps r t ∧ fraction eta eps r t<1 ∧
      0<floor eps-V t ∧ 3*(floor eps-V t)<donor eps r t := by
    filter_upwards [e1,e2,e3,e4] with t h1 h2 h3 h4
    exact ⟨h1,h2,by linarith,by linarith⟩
  obtain ⟨s,hs,hball⟩ := Metric.mem_nhds_iff.mp ev
  refine ⟨s,hs,?_⟩
  intro t ht hts
  have hg := hball (show t∈Metric.ball (0:ℝ) s by simpa [Metric.mem_ball,Real.dist_eq,abs_of_pos ht] using hts)
  exact ⟨hg.1,fraction_positive eta eps r t hEta he hr hr1 ht hg.1,hg.2⟩

theorem same_field_equations (eta eps r t : ℝ) (hEta : 0<eta) (he : 0<eps)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ht : 0 ≤ t) (hc : 0<donor eps r t)
    (hf : fraction eta eps r t<1) :
    unreleased eta eps r t+retained eta eps r t=donor eps r t ∧
    rate eta eps r t*unreleased eta eps r t=Q t/eta ∧
    HasDerivAt (unreleased eta eps r)
      (-theta r t*unreleased eta eps r t-Q t/eta-unreleased eta eps r t/donor eps r t*Q t) t ∧
    HasDerivAt (retained eta eps r)
      (-theta r t*retained eta eps r t+Q t/eta-retained eta eps r t/donor eps r t*Q t) t := by
  obtain ⟨ha,hb⟩ := AB_positive r t hr hr1 ht
  have hd := donor_deriv eps r t ha.ne' hb.ne'
  have hfd := fraction_deriv eta eps r t hEta.ne' he hr hr1 ha.ne' hb.ne' hc.ne'
  have hf0 : 1-fraction eta eps r t≠0 := by linarith
  refine ⟨by dsimp [unreleased,retained]; ring,?_,?_,?_⟩
  · dsimp [rate,unreleased]; field_simp <;> ring
  · convert (hfd.const_sub 1).mul hd using 1 <;> (try funext x) <;> (try dsimp [unreleased]) <;> field_simp <;> ring
  · convert hfd.mul hd using 1 <;> (try funext x) <;> (try dsimp [retained]) <;> field_simp <;> ring

theorem same_field_gravity (eps r t : ℝ) :
    (Htrans r t)^2+2*Htrans r t*Hrad r t=baryon eps r t+donor eps r t+V t := by
  rw [hamiltonian]; dsimp [donor]; ring

end Entropic.Completion.SpatialRelease
