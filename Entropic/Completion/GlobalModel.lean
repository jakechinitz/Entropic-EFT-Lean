import Entropic.Completion.GlobalFloor
import Entropic.Completion.Entropy
import Entropic.Compatibility.SharedModel

/-! Nonempty common global classical clock/stock/history model.
The measure and fields share the unique native eta. There is NO claimed map
from individual microscopic histories to this metric or to its field equations.
The selected depletion action is certified only on a positive initial interval.
The metric is on r>0; no smooth central extension or bound galaxy is asserted. -/
noncomputable section
namespace Entropic.Completion
open Entropic.Compatibility

structure GlobalModel where
  eta : ℝ
  stationary : Entropic.FiniteModel.ClosureStationary eta
  amplitude : ℝ
  small : GlobalSpatial.small eta (epsilon eta) amplitude
  histories : MeasureTheory.Measure InfiniteHistory.History
  histories_eq : histories=InfiniteHistory.rootedLaw eta

theorem global_effective_assumptions_compatible : Nonempty GlobalModel := by
  obtain ⟨eta,hs,_,_⟩ := Entropic.ClosureRoot.stationary_exists
  have he : 0 < epsilon eta := by
    have hh := (Entropic.Spine.epsilon_bracket hs).1
    change 0.1879 < epsilon eta at hh
    linarith
  obtain ⟨delta,hd⟩ := GlobalSpatial.small_exists eta (epsilon eta) hs.1 he
  exact ⟨{
    eta := eta
    stationary := hs
    amplitude := delta
    small := hd
    histories := InfiniteHistory.rootedLaw eta
    histories_eq := rfl }⟩

namespace GlobalModel

theorem epsilon_positive (m : GlobalModel) : 0 < epsilon m.eta := by
  have hh := (Entropic.Spine.epsilon_bracket m.stationary).1
  change 0.1879 < epsilon m.eta at hh
  linarith

def baryons (m : GlobalModel) (r s : ℝ) := GlobalSpatial.baryon m.eta (epsilon m.eta)
  (GlobalSpatial.h m.amplitude r) (GlobalSpatial.j m.amplitude r) s
def stock (m : GlobalModel) (r s : ℝ) := GlobalRelease.retained m.eta (epsilon m.eta)
  (GlobalSpatial.h m.amplitude r) (GlobalSpatial.j m.amplitude r) s
def unreleased (m : GlobalModel) (r s : ℝ) := GlobalRelease.unreleased m.eta (epsilon m.eta)
  (GlobalSpatial.h m.amplitude r) (GlobalSpatial.j m.amplitude r) s
-- Spherical metric: -lapse(s)^2 ds^2 + (d_r arealRadius)^2 dr^2 + arealRadius^2 dOmega^2.
def lapse (m : GlobalModel) (s : ℝ) := 1/GlobalBackground.H m.eta (epsilon m.eta) s
def arealRadius (m : GlobalModel) (r s : ℝ) := r*Real.exp s*
  (GlobalSpatial.P m.eta (epsilon m.eta) (GlobalSpatial.h m.amplitude r) s)^(2/3:ℝ)

theorem positive_fields (m : GlobalModel) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 < s) :
    0 < m.baryons r s ∧ 0 < m.unreleased r s ∧ 0 < m.stock r s := by
  obtain ⟨ha,ha1,hd,hd1⟩ := GlobalSpatial.profile_bounds m.amplitude r m.small.1 hr
  obtain ⟨hb,hu,_⟩ := GlobalRelease.positive_components m.eta (epsilon m.eta) m.amplitude
    (GlobalSpatial.h m.amplitude r) (GlobalSpatial.j m.amplitude r) s m.stationary.1 m.epsilon_positive
    m.small ha.le hd.le ha1 hd1 hs.le
  exact ⟨hb,hu,GlobalRelease.positive_retained m.eta (epsilon m.eta) m.amplitude
    (GlobalSpatial.h m.amplitude r) (GlobalSpatial.j m.amplitude r) s m.stationary.1 m.epsilon_positive
    m.small ha.le hd.le ha1 hd1 hs⟩

theorem future_proper_time (m : GlobalModel) (T : ℝ) :
    ∃ s : ℝ, 0 < s ∧ T < GlobalBackground.properTime m.eta (epsilon m.eta) s :=
  GlobalBackground.unbounded_future_proper_time m.eta (epsilon m.eta) T m.stationary.1 m.epsilon_positive

theorem inhomogeneous_every_epoch (m : GlobalModel) (s : ℝ) (hs : 0 ≤ s) :
    GlobalSpatial.rho m.eta (epsilon m.eta) (GlobalSpatial.h m.amplitude 2) (GlobalSpatial.j m.amplitude 2) s <
    GlobalSpatial.rho m.eta (epsilon m.eta) (GlobalSpatial.h m.amplitude 1) (GlobalSpatial.j m.amplitude 1) s :=
  GlobalRelease.global_radial_contrast m.eta (epsilon m.eta) m.amplitude s
    m.stationary.1 m.epsilon_positive m.small.1 hs

theorem selected_depletion_initial_interval (m : GlobalModel) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ s : ℝ, 0 ≤ s → s < radius →
      0 < GlobalFloor.floor m.eta (epsilon m.eta) m.amplitude-GlobalBackground.V m.eta s ∧
      ∀ r : ℝ, 0 ≤ r →
        3*(GlobalFloor.floor m.eta (epsilon m.eta) m.amplitude-GlobalBackground.V m.eta s) <
          GlobalSpatial.donor m.eta (epsilon m.eta) (GlobalSpatial.h m.amplitude r) (GlobalSpatial.j m.amplitude r) s := by
  obtain ⟨rd,hrd,hall⟩ := GlobalFloor.selected_action_local_domain m.eta (epsilon m.eta) m.amplitude
    m.stationary.1 m.epsilon_positive m.small
  refine ⟨rd,hrd,?_⟩
  intro s hs hsr
  obtain ⟨hv,hallr⟩ := hall s hs hsr
  refine ⟨hv,?_⟩
  intro r hr
  obtain ⟨ha,ha1,hd,hd1⟩ := GlobalSpatial.profile_bounds m.amplitude r m.small.1 hr
  exact hallr _ _ ha.le hd.le ha1 hd1

theorem common_parameter (m n : GlobalModel) : m.eta=n.eta :=
  Entropic.ClosureRoot.stationary_unique m.stationary n.stationary

end GlobalModel
end Entropic.Completion
