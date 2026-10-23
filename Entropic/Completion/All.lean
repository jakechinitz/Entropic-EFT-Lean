import Entropic.Completion.Entropy
import Entropic.Completion.Metric
import Entropic.Completion.SpatialRelease
import Entropic.Completion.Motion
import Entropic.Completion.Obstructions
import Entropic.Completion.CausalBounds
import Entropic.Completion.GlobalModel
import Entropic.Compatibility.SharedModel

/-! A common inhomogeneous classical clock/stock/history subsystem.
This is NOT a witness of the complete microscopic theory: no native interacting
continuum limit, galaxy target selection, full field-to-operator map, or empirical
likelihood is included. The root is an explicit initial-state choice. -/
noncomputable section
namespace Entropic.Completion
open Entropic.Compatibility Entropic.Completion.Spatial

def admissible (eta eps r t : ℝ) : Prop :=
  0<SpatialRelease.donor eps r t ∧
  0<SpatialRelease.fraction eta eps r t ∧ SpatialRelease.fraction eta eps r t<1 ∧
  0<SpatialRelease.floor eps-V t ∧
  3*(SpatialRelease.floor eps-V t)<SpatialRelease.donor eps r t

theorem initial_contrast : rho (3/4) 0<rho (1/4) 0 := by
  rw [(initial_geometry (3/4)).2.2.2.1,(initial_geometry (1/4)).2.2.2.1]
  norm_num [h,j]

theorem common_epoch (eta eps : ℝ) (hEta : 0<eta) (he : 0<eps) :
    ∃ t : ℝ, 0<t ∧ admissible eta eps (1/4) t ∧ admissible eta eps (3/4) t ∧
      rho (3/4) t<rho (1/4) t := by
  obtain ⟨r1,hr1,h1⟩ := SpatialRelease.positive_interval eta eps (1/4) hEta he (by norm_num) (by norm_num)
  obtain ⟨r2,hr2,h2⟩ := SpatialRelease.positive_interval eta eps (3/4) hEta he (by norm_num) (by norm_num)
  have hd1 := density_deriv (1/4) 0 (by norm_num [A,U,Y,I]) (by norm_num [B,U,Y,I])
  have hd2 := density_deriv (3/4) 0 (by norm_num [A,U,Y,I]) (by norm_num [B,U,Y,I])
  have hc := hd1.continuousAt.sub hd2.continuousAt
  have ev := hc.eventually (lt_mem_nhds (show 0<rho (1/4) 0-rho (3/4) 0 by linarith [initial_contrast]))
  obtain ⟨rd,hrd,hball⟩ := Metric.mem_nhds_iff.mp ev
  let t := min r1 (min r2 rd)/2
  have hp : 0 < min r1 (min r2 rd) := lt_min hr1 (lt_min hr2 hrd)
  have ht : 0<t := by dsimp [t]; linarith
  have htmin : t < min r1 (min r2 rd) := by dsimp [t]; linarith
  have ht1 := lt_of_lt_of_le htmin (min_le_left _ _)
  have ht2 := lt_of_lt_of_le htmin (le_trans (min_le_right _ _) (min_le_left _ _))
  have htd := lt_of_lt_of_le htmin (le_trans (min_le_right _ _) (min_le_right _ _))
  have hh := hball (show t∈Metric.ball (0:ℝ) rd by simpa [Metric.mem_ball,Real.dist_eq,abs_of_pos ht] using htd)
  change 0 < rho (1/4) t-rho (3/4) t at hh
  exact ⟨t,ht,h1 t ht ht1,h2 t ht ht2,by linarith⟩

structure SpatialHistoryModel where
  eta : ℝ
  stationary : Entropic.FiniteModel.ClosureStationary eta
  histories : MeasureTheory.Measure InfiniteHistory.History
  history_choice : histories=InfiniteHistory.rootedLaw eta
  baryons : ℝ → ℝ → ℝ
  stock : ℝ → ℝ → ℝ
  unreleased : ℝ → ℝ → ℝ
  baryons_eq : baryons=SpatialRelease.baryon (epsilon eta)
  stock_eq : stock=SpatialRelease.retained eta (epsilon eta)
  unreleased_eq : unreleased=SpatialRelease.unreleased eta (epsilon eta)
  time : ℝ
  time_pos : 0<time
  first_region : admissible eta (epsilon eta) (1/4) time
  second_region : admissible eta (epsilon eta) (3/4) time
  contrast : rho (3/4) time<rho (1/4) time

theorem spatial_history_assumptions_compatible : Nonempty SpatialHistoryModel := by
  obtain ⟨eta,hs,_,_⟩ := Entropic.ClosureRoot.stationary_exists
  have he : 0<epsilon eta := by
    have hh := (Entropic.Spine.epsilon_bracket hs).1
    change 0.1879<epsilon eta at hh
    linarith
  obtain ⟨t,ht,h1,h2,hc⟩ := common_epoch eta (epsilon eta) hs.1 he
  exact ⟨{
    eta:=eta,stationary:=hs,histories:=InfiniteHistory.rootedLaw eta,history_choice:=rfl,
    baryons:=SpatialRelease.baryon (epsilon eta),
    stock:=SpatialRelease.retained eta (epsilon eta),
    unreleased:=SpatialRelease.unreleased eta (epsilon eta),
    baryons_eq:=rfl,stock_eq:=rfl,unreleased_eq:=rfl,
    time:=t,time_pos:=ht,first_region:=h1,second_region:=h2,contrast:=hc }⟩

namespace SpatialHistoryModel

theorem epsilon_positive (m : SpatialHistoryModel) : 0<epsilon m.eta := by
  have hh := (Entropic.Spine.epsilon_bracket m.stationary).1
  change 0.1879<epsilon m.eta at hh
  linarith

theorem fields_positive (m : SpatialHistoryModel) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (ha : admissible m.eta (epsilon m.eta) r m.time) :
    0 < m.baryons r m.time ∧ 0 < m.stock r m.time ∧ 0 < m.unreleased r m.time := by
  obtain ⟨hc,hf,hf1,_,_⟩ := ha
  obtain ⟨hA,hB⟩ := AB_positive r m.time hr hr1 m.time_pos.le
  have hd : 0<rho r 0 := by linarith [SpatialRelease.initial_density_lower r hr hr1]
  have he := m.epsilon_positive
  rw [m.baryons_eq,m.stock_eq,m.unreleased_eq]
  dsimp [SpatialRelease.baryon,SpatialRelease.retained,SpatialRelease.unreleased,J]
  exact ⟨by positivity,mul_pos hf hc,mul_pos (sub_pos.mpr hf1) hc⟩

theorem same_positive_stock_sources_metric (m : SpatialHistoryModel) (r t : ℝ) :
    (Htrans r t)^2+2*Htrans r t*Hrad r t=
      m.baryons r t+m.unreleased r t+m.stock r t+V t := by
  rw [m.baryons_eq,m.stock_eq,m.unreleased_eq,SpatialRelease.same_field_gravity]
  dsimp [SpatialRelease.unreleased,SpatialRelease.retained]; ring

theorem active_release (m : SpatialHistoryModel) : 0<Q m.time :=
  source_positive m.time m.time_pos.le

theorem common_native_parameter (m n : SpatialHistoryModel) : m.eta=n.eta :=
  Entropic.ClosureRoot.stationary_unique m.stationary n.stationary

end SpatialHistoryModel
end Entropic.Completion
