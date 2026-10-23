import Mathlib

/-! Independent empirical-program certificates. Numerical inputs are explicit.
These statements neither certify data likelihoods nor select physical premises. -/
noncomputable section
namespace EmpiricalProgram

def expansion (z : ℝ) : ℝ := Real.sqrt ((315/1000:ℝ)*(1+z)^3 + 685/1000)

theorem expansion_today : expansion 0 = 1 := by
  norm_num [expansion]

theorem expansion_z23 : (3.4648:ℝ) < expansion (23/10) ∧ expansion (23/10) < 3.4649 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 315/1000*(1+23/10)^3+685/1000 by norm_num)
  have hn := Real.sqrt_nonneg (315/1000*(1+(23:ℝ)/10)^3+685/1000)
  dsimp [expansion]
  constructor <;> nlinarith

theorem a0_z23_from_stated_today :
    (4.2642:ℝ) < 1.2307292376441814 * expansion (23/10) ∧
    1.2307292376441814 * expansion (23/10) < 4.2644 := by
  obtain ⟨h1,h2⟩ := expansion_z23
  constructor <;> nlinarith

theorem effective_vacuum_w_le (V rate : ℝ) (hV : 0 < V) (hr : 0 ≤ rate) :
    -1 - rate / (3*V) ≤ -1 := by
  have := div_nonneg hr (by positivity : 0 ≤ 3*V)
  linarith

theorem bare_cross_relation (e c H : ℝ) (he : e ≠ 0) :
    (e*c*H)*(1/e)=c*H := by field_simp [he] <;> ring

theorem corrected_cross_relation (e c H massFactor survival : ℝ) (he : e ≠ 0) :
    (e*c*H)*(massFactor*survival/e)=massFactor*survival*c*H := by
  field_simp
  <;> ring

theorem lensing_potential_under_no_slip (phi psi : ℝ) (h : phi=psi) :
    (phi+psi)/2=psi := by rw [h]; ring

#print axioms expansion_today
#print axioms expansion_z23
#print axioms a0_z23_from_stated_today
#print axioms effective_vacuum_w_le
#print axioms bare_cross_relation
#print axioms corrected_cross_relation
#print axioms lensing_potential_under_no_slip
end EmpiricalProgram
