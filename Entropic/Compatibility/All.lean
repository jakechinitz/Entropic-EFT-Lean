import Entropic.Compatibility.SharedModel
import Entropic.Compatibility.GibbsHistory
import Entropic.Compatibility.Expanding
import Entropic.Compatibility.Projection
import Entropic.Extensions20261023.ConnectedClosure
import Entropic.Extensions20261023.EffectiveContact

/-! Main result: compatibility of the explicit effective subsystem below.
This is not Nonempty for all physical assumptions of the four publications.
The finite stock is shared across reconstruction, relaxation, and forces;
the native eta/epsilon is shared with the exact homogeneous solution and
the native Gibbs history. No embedding of the finite two-body system into
that FLRW spacetime or the native quantum geometry is asserted.
-/
noncomputable section
open scoped BigOperators
namespace Entropic.Compatibility

def shared_from_cosmology (eta : ℝ) (hs : Entropic.FiniteModel.ClosureStationary eta)
    (t : ℝ) (ht : 0 < t) (hC : 0 < Expanding.donor (epsilon eta) t)
    (hF1 : Expanding.releasedFraction eta (epsilon eta) t < 1) : SharedModel := by
  have he : 0 < epsilon eta := by
    have hh := (Entropic.Spine.epsilon_bracket hs).1
    change 0.1879 < epsilon eta at hh
    linarith
  let b := Expanding.baryon (epsilon eta) t
  let C := Expanding.donor (epsilon eta) t
  let F := Expanding.releasedFraction eta (epsilon eta) t
  let R := F*C
  let u := (1-F)*C
  have hb : 0 < b := mul_pos (div_pos he (by linarith)) (Real.exp_pos _)
  have hF : 0 < F := Expanding.fraction_positive eta (epsilon eta) t hs.1 he ht hC
  have hR : 0 < R := mul_pos hF hC
  have hu : 0 < u := mul_pos (sub_pos.mpr hF1) hC
  refine {
    eta := eta
    stationary := hs
    baryon := fun _ => b/2
    baryon_pos := by intro i; positivity
    stock := fun _ => R/2
    stock_pos := by intro i; positivity
    unreleased := u
    unreleased_pos := hu
    fraction := F
    fraction_pos := hF
    fraction_lt_one := hF1
    capacity_link := ?_
    release_link := ?_
    position := ![0,1]
    separated := by norm_num
    target := ![1,0]
    target_nonneg := by intro i; fin_cases i <;> norm_num
    target_normalized := by norm_num [Fin.sum_univ_two]
    disequilibrium := ?_ }
  · simp only [Fin.sum_univ_two]
    calc
      u+(R/2+R/2)=C := by dsimp [u,R]; ring
      _ = ((b/2+b/2)/epsilon eta)*Real.exp (-eta*F) := by
        convert Expanding.physical_allocation eta (epsilon eta) t hs.1.ne' he hC using 1 <;>
          dsimp [C,b,F] <;> ring
  · simp only [Fin.sum_univ_two]
    dsimp [R,u]; ring
  · simp only [Fin.sum_univ_two,Matrix.cons_val_zero,one_mul]
    linarith

structure EffectiveModel extends SharedModel where
  radius : ℝ
  radius_pos : 0 < radius
  floor : ℝ
  floor_pos : 0 < floor
  observationTime : ℝ
  observationTime_pos : 0 < observationTime
  observationTime_lt : observationTime < radius
  baryons_at_time : (∑ i, baryon i)=Expanding.baryon (epsilon eta) observationTime
  stock_at_time : (∑ i, stock i)=Expanding.retained eta (epsilon eta) observationTime
  unreleased_at_time : unreleased=Expanding.unreleased eta (epsilon eta) observationTime
  fraction_at_time : fraction=Expanding.releasedFraction eta (epsilon eta) observationTime
  homogeneous_admissible : ∀ t, 0 ≤ t → t < radius →
    0 < Expanding.donor (epsilon eta) t ∧
    0 ≤ Expanding.releasedFraction eta (epsilon eta) t ∧
    Expanding.releasedFraction eta (epsilon eta) t < 1
  completion_admissible : ∀ t, 0 ≤ t → t < radius →
    0 < floor-Expanding.V t ∧ 3*(floor-Expanding.V t) < Expanding.donor (epsilon eta) t
  histories_normalized : ∀ n,
    (∑ h : Fin n → GibbsHistory.Microstate,
      History.historyWeight (GibbsHistory.probability eta) n h)=1
  histories_full_support : ∀ n (h : Fin n → GibbsHistory.Microstate),
    0 < History.historyWeight (GibbsHistory.probability eta) n h
  shell_return : ∀ s, History.shellAt s 720=s
  shell_first_return : ∀ s n, 0<n → n<720 → History.shellAt s n ≠ s

theorem effective_assumptions_compatible : Nonempty EffectiveModel := by
  obtain ⟨eta,hstat,_,_⟩ := Entropic.ClosureRoot.stationary_exists
  have he : 0 < epsilon eta := by
    have hh := (Entropic.Spine.epsilon_bracket hstat).1
    change 0.1879 < epsilon eta at hh
    linarith
  obtain ⟨r,hr,hGood⟩ := Expanding.admissible_interval eta (epsilon eta) hstat.1 he
  obtain ⟨K,s,hK,hs,hDust⟩ := Expanding.depletion_compatible_interval (epsilon eta) he
  let t := min r s/2
  have hmin : 0 < min r s := lt_min hr hs
  have ht : 0 < t := by dsimp [t]; linarith
  have htmin : t < min r s := by dsimp [t]; linarith
  have htr : t < r := lt_of_lt_of_le htmin (min_le_left _ _)
  have hc := hGood t ht.le htr
  let m := shared_from_cosmology eta hstat t ht hc.1 hc.2.2
  refine ⟨{
    toSharedModel := m
    radius := min r s
    radius_pos := lt_min hr hs
    floor := K
    floor_pos := hK
    observationTime := t
    observationTime_pos := ht
    observationTime_lt := htmin
    baryons_at_time := by dsimp [m,shared_from_cosmology]; simp only [Fin.sum_univ_two]; ring
    stock_at_time := by dsimp [m,shared_from_cosmology,Expanding.retained]; simp only [Fin.sum_univ_two]; ring
    unreleased_at_time := rfl
    fraction_at_time := rfl
    homogeneous_admissible := ?_
    completion_admissible := ?_
    histories_normalized := GibbsHistory.native_history_normalized m.eta
    histories_full_support := GibbsHistory.native_history_full_support m.eta
    shell_return := History.shell_returns
    shell_first_return := fun z n hn hn' => History.shell_no_early_return z hn hn' }⟩
  · intro t ht hb
    exact hGood t ht (lt_of_lt_of_le hb (min_le_left _ _))
  · intro t ht hb
    apply hDust
    rw [abs_of_nonneg ht]
    exact lt_of_lt_of_le hb (min_le_right _ _)

namespace EffectiveModel

theorem native_parameter_unique (m n : EffectiveModel) : m.eta=n.eta :=
  Entropic.ClosureRoot.stationary_unique m.stationary n.stationary

theorem expanding_nonzero_source (m : EffectiveModel) :
    ∃ t : ℝ, 0 < t ∧ t < m.radius ∧ 0 < Expanding.H t ∧ 0 < Expanding.Q t ∧
      0<Expanding.baryon (epsilon m.eta) t ∧ 0<Expanding.donor (epsilon m.eta) t := by
  let t := m.radius/2
  have ht : 0 < t := by dsimp [t]; linarith [m.radius_pos]
  have hr : t < m.radius := by dsimp [t]; linarith [m.radius_pos]
  refine ⟨t,ht,hr,(Expanding.expansion_positive t).1,Expanding.source_positive ht.le,?_,
    (m.homogeneous_admissible t ht.le hr).1⟩
  unfold Expanding.baryon
  exact mul_pos (div_pos m.toSharedModel.epsilon_pos (by linarith [m.toSharedModel.epsilon_pos]))
    (Real.exp_pos _)

theorem same_stock_projection (m : EffectiveModel) :
    (∀ i, 0 ≤ Projection.projected m.toSharedModel.retained Projection.signedExample i) ∧
    (∑ i, Projection.projected m.toSharedModel.retained Projection.signedExample i)=m.toSharedModel.retained := by
  have h := Projection.nontrivial_repair m.toSharedModel.retained m.toSharedModel.retained_pos
  exact ⟨h.2.1,h.2.2.1⟩

-- A real intermediate depletion state, away from the dust and rest endpoints.
theorem intermediate_depletion_exists (m : EffectiveModel) :
    ∃ L V K lam X : ℝ, 0<L ∧ L=3*(K-V) ∧ L/2<lam ∧ lam<L ∧
      X=ConnectedClosure.kineticX (lam/L) ∧ 0<X ∧ X<1/2 ∧
      K ≤ L*ConnectedClosure.energyShape (lam/L)+V := by
  let K := m.floor
  let V := K/2
  let L := 3*(K-V)
  have hL : 0<L := by dsimp [L,V,K]; linarith [m.floor_pos]
  have hratio : (3*L/4)/L=3/4 := by field_simp
  refine ⟨L,V,K,3*L/4,3/8,hL,rfl,by linarith,by linarith,?_,by norm_num,by norm_num,?_⟩
  · rw [hratio]; norm_num [ConnectedClosure.kineticX]
  · exact ConnectedClosure.adaptive_floor L V K _ hL.le rfl (by rw [hratio]; norm_num)

-- Nonzero target-weight change, heat, and work with two admissible endpoints.
theorem finite_work_contact_exists (m : EffectiveModel) :
    ∃ E Enew U bath Q W : ℝ,
      0<Q ∧ 0<W ∧ m.floor<U ∧ m.floor<U-W ∧
      Q=m.floor*Real.log (Real.exp 1/1) ∧ W=Enew-E+Q ∧
      Enew+(U-W)+(bath+Q)=E+U+bath := by
  let K := m.floor
  refine ⟨2*K,9*K/4,4*K,0,K,5*K/4,m.floor_pos,?_,?_,?_,?_,by ring,by ring⟩
  · dsimp [K]; linarith [m.floor_pos]
  · dsimp [K]; linarith [m.floor_pos]
  · dsimp [K]; linarith [m.floor_pos]
  · simp [K]

end EffectiveModel

end Entropic.Compatibility
