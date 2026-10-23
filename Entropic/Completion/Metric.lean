import Entropic.Completion.Spatial

/-! Link the reduced variables to actual radial and temporal metric derivatives.
Spherical chart away from its coordinate singularities. No claim here of a
formalized manifold-level curvature calculation; see metric_check.py. -/
noncomputable section
set_option linter.unnecessarySeqFocus false
namespace Entropic.Completion.Metric
open Entropic.Completion.Spatial

def radius (r t : ℝ) := r*(A r t)^(2/3:ℝ)
def radialScale (r t : ℝ) := B r t*(A r t)^(-1/3:ℝ)

theorem radius_time_deriv (r t : ℝ) (ha : 0<A r t) :
    HasDerivAt (radius r) (Htrans r t*radius r t) t := by
  convert ((A_deriv r t).rpow_const (Or.inl ha.ne')).const_mul r using 1
  all_goals try (first | rfl | (funext x; rfl))
  dsimp [radius,Htrans,alpha]
  rw [Real.rpow_sub ha,Real.rpow_one]
  field_simp <;> ring

theorem radius_spatial_deriv (r t : ℝ) (ha : 0<A r t) :
    HasDerivAt (fun s => radius s t) (radialScale r t) r := by
  have hd : HasDerivAt (fun s => A s t) ((-r/5)*Y t) r := by
    convert (((((hasDerivAt_id r).pow 2).div_const 10).const_sub 1).mul_const (Y t)).const_add (U t) using 1 <;> (try funext x) <;>
      (try dsimp [A,h]) <;> ring
  have hex : (2/3:ℝ)-1=(-1/3:ℝ) := by norm_num
  have hpow : (A r t)^(2/3:ℝ)=A r t*(A r t)^(-1/3:ℝ) := by
    calc
      (A r t)^(2/3:ℝ)=(A r t)^((1:ℝ)+(-1/3:ℝ)) := by norm_num
      _=(A r t)^(1:ℝ)*(A r t)^(-1/3:ℝ) := Real.rpow_add ha _ _
      _=A r t*(A r t)^(-1/3:ℝ) := by rw [Real.rpow_one]
  convert (hasDerivAt_id r).mul (hd.rpow_const (Or.inl ha.ne')) using 1
  all_goals try (first | rfl | (funext x; rfl))
  dsimp [radius,radialScale]
  rw [hex,hpow]
  dsimp [A,B,h,j]; ring

theorem metric_positive (r t : ℝ) (hr : 0<r) (hr1 : r ≤ 1) (ht : 0 ≤ t) :
    0<radius r t ∧ 0<radialScale r t := by
  obtain ⟨ha,hb⟩ := AB_positive r t hr.le hr1 ht
  exact ⟨mul_pos hr (Real.rpow_pos_of_pos ha _),mul_pos hb (Real.rpow_pos_of_pos ha _)⟩

theorem physical_volume (r t : ℝ) (ha : 0<A r t) :
    (radius r t)^2*radialScale r t=r^2*J r t := by
  dsimp [radius,radialScale,J]
  rw [mul_pow,← Real.rpow_mul_natCast ha.le]
  rw [mul_assoc, mul_left_comm _ (B r t),← Real.rpow_add ha]
  norm_num
  ring <;> simp

theorem homogeneous_companion (t : ℝ) :
    Hrad 0 t=Htrans 0 t ∧ 3*(Htrans 0 t)^2=rho 0 t+V t := by
  have hab : beta 0 t=alpha 0 t := by simp [beta,alpha,A,B,Ap,Bp,h,j]
  have hi : Hrad 0 t=Htrans 0 t := by dsimp [Hrad,Htrans]; rw [hab]; ring
  refine ⟨hi,?_⟩
  have hh := hamiltonian 0 t
  rw [hi] at hh
  nlinarith [hh]

end Entropic.Completion.Metric
