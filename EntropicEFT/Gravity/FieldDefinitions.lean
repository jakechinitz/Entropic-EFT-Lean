import EntropicEFT.Gravity.Static

/-!
# EntropicEFT.Gravity.FieldDefinitions

LOCAL CONTRACT
* Manuscript: Sections 2--4, 11.
* Pure definitions of S_ent, deltaS, q at the continuum bookkeeping level.
* No claim that a particular microscopic observable has this continuum limit is proved here.
-/

namespace EntropicEFT.Gravity

structure CapacityFieldPoint where
  SEnt : ℝ
  SInf : ℝ
  SInf_pos : 0 < SInf

namespace CapacityFieldPoint

noncomputable def deficit (x : CapacityFieldPoint) : ℝ := x.SInf - x.SEnt

noncomputable def q (x : CapacityFieldPoint) : ℝ := x.SEnt / x.SInf

theorem q_eq_one_minus_deficit (x : CapacityFieldPoint) :
    x.q = 1 - x.deficit/x.SInf := by
  simp [q, deficit]
  field_simp [ne_of_gt x.SInf_pos]
  ring

end CapacityFieldPoint

/-- Strong-field boundedness is a constitutive/domain condition, not implied by this definition. -/
structure BoundedCapacityPoint extends CapacityFieldPoint where
  q_nonneg : 0 ≤ toCapacityFieldPoint.q
  q_le_one : toCapacityFieldPoint.q ≤ 1

end EntropicEFT.Gravity
