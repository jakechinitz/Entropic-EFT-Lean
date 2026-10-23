import Entropic.Compatibility.History
import Entropic.Compatibility.SharedModel
import Mathlib

/-! Precisely scoped incompatibilities and missing implications. These do not
conjoin alternative manuscript branches or claim that the whole theory is inconsistent. -/
namespace Entropic.Completion.Obstructions

theorem finite_faithful_archive_impossible : IsEmpty Entropic.Compatibility.History.FiniteArchive :=
  Entropic.Compatibility.History.finiteArchive_isEmpty

-- A single nonzero exchange vector cannot be parallel to two distinct unit-time flows.
theorem two_stream_clock_obstruction (v1 v2 a b : ℝ) (hv : v1≠v2)
    (ht : a=b) (hx : a*v1=b*v2) : a=0 ∧ b=0 := by
  have hz : a*(v1-v2)=0 := by rw [← ht] at hx; nlinarith
  have ha := (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hv)
  exact ⟨ha,by rwa [← ht]⟩

-- Only applies when one additionally imposes a pointwise Q=eta*gamma*u.
-- O.3 imposes Q=eta*E_bg[q], so this is not an objection to that background law.
theorem uniform_local_hazard_obstruction (eta gamma Q u1 u2 : ℝ)
    (he : eta≠0) (hg : gamma≠0) (h1 : Q=eta*gamma*u1) (h2 : Q=eta*gamma*u2) :
    u1=u2 := by
  exact mul_left_cancel₀ (mul_ne_zero he hg) (h1.symm.trans h2)

theorem bare_matched_normalizations_conflict (G G0 c : ℝ) (hG : 0<G) (hc : 1<c)
    (hbare : G0=c*G) (hmatched : G0=G) : False := by nlinarith

theorem renormalization_can_match (G c : ℝ) (hc : 0<c) :
    ∃ Z : ℝ, 0<Z ∧ Z*(c*G)=G := by
  exact ⟨1/c,one_div_pos.mpr hc,by field_simp⟩

-- A monotone positive-mass profile cannot approximate a decreasing raw target
-- more accurately than half the drop at both endpoints.
theorem positive_profile_error_floor (raw1 raw2 mass1 mass2 delta : ℝ)
    (hm : mass1 ≤ mass2) (h1 : |mass1-raw1| ≤ delta) (h2 : |mass2-raw2| ≤ delta) :
    (raw1-raw2)/2 ≤ delta := by
  obtain ⟨h1l,h1u⟩ := abs_le.mp h1
  obtain ⟨h2l,h2u⟩ := abs_le.mp h2
  linarith

theorem exact_decreasing_target_impossible (raw1 raw2 mass1 mass2 : ℝ)
    (hd : raw2<raw1) (hm : mass1 ≤ mass2) (h1 : mass1=raw1) (h2 : mass2=raw2) : False := by
  linarith

-- A conserved comoving donor cannot finance an integrated drain larger than itself.
theorem integrated_drain_budget (initial remaining spent : ℝ)
    (hbalance : remaining=initial-spent) (hpositive : 0 ≤ remaining) : spent ≤ initial := by
  linarith

theorem overdraw_is_negative (initial remaining spent : ℝ)
    (hbalance : remaining=initial-spent) (hover : initial<spent) : remaining<0 := by
  linarith

-- An explicit nonempty choice of positive matching and common speeds exists,
-- but neither common speed nor the matching multiplier is derived by this identity.
theorem matching_parameters_coexist (G c speed : ℝ) (hG : 0<G) (hc : 0<c) (hs : 0<speed) :
    ∃ G0 Z cm cg : ℝ, 0<G0 ∧ 0<Z ∧ Z*G0=G ∧ 0<cm ∧ cm=cg := by
  refine ⟨c*G,1/c,speed,speed,mul_pos hc hG,one_div_pos.mpr hc,?_,hs,rfl⟩
  field_simp


-- Holding the arithmetic G_* and bare multiplier fixed does not fix physical G
-- if the low-energy matching factor is still unconstrained. This does NOT apply
-- after imposing the paper's selected Einstein/horizon matching premise.
theorem arithmetic_does_not_select_matching (Gstar bareFactor target : ℝ)
    (hs : 0 < Gstar) (hc : 0 < bareFactor) (ht : 0 < target) :
    ∃ Z : ℝ, 0 < Z ∧ Z*(bareFactor*Gstar)=target := by
  refine ⟨target/(bareFactor*Gstar),div_pos ht (mul_pos hc hs),?_⟩
  field_simp

theorem two_distinct_matchings (Gstar bareFactor : ℝ) (hs : 0 < Gstar) (hc : 0 < bareFactor) :
    ∃ Z1 Z2 : ℝ, 0 < Z1 ∧ 0 < Z2 ∧ Z1≠Z2 ∧
      Z1*(bareFactor*Gstar)=Gstar ∧ Z2*(bareFactor*Gstar)=2*Gstar := by
  obtain ⟨z1,h1,e1⟩ := arithmetic_does_not_select_matching Gstar bareFactor Gstar hs hc hs
  obtain ⟨z2,h2,e2⟩ := arithmetic_does_not_select_matching Gstar bareFactor (2*Gstar) hs hc (by positivity)
  exact ⟨z1,z2,h1,h2,by intro hh; rw [hh] at e1; nlinarith,e1,e2⟩

-- A positive relaxation rate fixes a timescale, but allows every constant target.
-- Additional physics must choose which target the dynamics relaxes toward.
theorem relaxation_rate_does_not_select_target (rate target : ℝ) :
    ∃ stock : ℝ → ℝ, (∀ t,stock t=target) ∧
      ∀ t,deriv stock t=rate*(target-stock t) := by
  exact ⟨fun _ => target,fun _ => rfl,by intro t; simp⟩

end Entropic.Completion.Obstructions
