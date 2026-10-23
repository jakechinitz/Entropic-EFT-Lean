import Mathlib

/-! Exact local identities for the selected merger discretization.
These do not certify a PDE solution, an initial distribution or an observed map. -/
noncomputable section
namespace MergerContact

theorem reciprocal_pair_momentum (m n v w d : ℝ) :
    m*(v+n/(m+n)*d)+n*(w-m/(m+n)*d)=m*v+n*w := by ring

theorem relative_velocity_update (m n v w d : ℝ) (h : m+n ≠ 0) :
    (v+n/(m+n)*d)-(w-m/(m+n)*d)=v-w+d := by
  field_simp
  ring

theorem reduced_mass_work (m n v w d : ℝ) (h : m+n ≠ 0) :
    m/2*((v+n/(m+n)*d)^2-v^2)+n/2*((w-m/(m+n)*d)^2-w^2)
      =m*n/(m+n)*((v-w)*d+d^2/2) := by
  field_simp
  ring

theorem central_pair_torque (x y X Y a : ℝ) :
    x*(a*(y-Y))-y*(a*(x-X))+
      X*(-a*(y-Y))-Y*(-a*(x-X))=0 := by ring

theorem sph_pair_power (m n v w A B viscosity grad : ℝ) :
    m*v*(-n*(A+B+viscosity)*grad)+n*w*(m*(A+B+viscosity)*grad)+
      m*n*(A+viscosity/2)*(v-w)*grad+
      n*m*(B+viscosity/2)*(v-w)*grad=0 := by ring

theorem viscous_heat_nonnegative (m n viscosity vg : ℝ)
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hp : 0 ≤ viscosity) (hv : 0 ≤ vg) :
    0 ≤ m*n*viscosity*vg := by positivity

theorem negative_work_recharges (U work : ℝ) (h : work < 0) : U < U-work := by linarith

theorem floor_gate_absorbing (nu vfinal : ℝ) : nu*(0:ℝ)*vfinal=0 := by ring

end MergerContact
