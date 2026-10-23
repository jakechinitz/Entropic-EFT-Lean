import Mathlib.Tactic

/-! Source terms survive exact elimination. Work in an orthogonal eigenbasis
of a positive interior Hessian; the source b may depend on all retained fields.
Gaussian integration and its determinant factor are not formalized here. -/
noncomputable section
namespace Entropic.GaussianSource
open Finset
variable {ι : Type*} [Fintype ι]

theorem complete_square (a b y : ℝ) (ha : a ≠ 0) :
    a*y^2/2 - b*y = a/2*(y-b/a)^2 - b^2/(2*a) := by
  field_simp <;> ring

theorem eliminate_finite (a b y : ι → ℝ) (ha : ∀ i, a i ≠ 0) :
    (∑ i, (a i*(y i)^2/2 - b i*y i)) =
      (∑ i, a i/2*(y i-b i/a i)^2) - ∑ i, (b i)^2/(2*a i) := by
  rw [← sum_sub_distrib]
  exact sum_congr rfl (fun i _ => complete_square (a i) (b i) (y i) (ha i))

theorem minimum_bound (a b y : ι → ℝ) (ha : ∀ i, 0 < a i) :
    -(∑ i, (b i)^2/(2*a i)) ≤ ∑ i, (a i*(y i)^2/2-b i*y i) := by
  rw [eliminate_finite a b y (fun i => ne_of_gt (ha i))]
  have h : 0 ≤ ∑ i, a i/2*(y i-b i/a i)^2 :=
    sum_nonneg (fun i _ => mul_nonneg (div_nonneg (le_of_lt (ha i)) (by norm_num)) (sq_nonneg _))
  linarith

theorem minimum_attained (a b : ι → ℝ) (ha : ∀ i, a i ≠ 0) :
    (∑ i, (a i*(b i/a i)^2/2-b i*(b i/a i))) =
      -(∑ i, (b i)^2/(2*a i)) := by
  rw [eliminate_finite a b (fun i => b i/a i) ha]
  simp

end Entropic.GaussianSource
