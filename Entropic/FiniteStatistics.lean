import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Finite statistical inequalities used by the closure program. The Gibbs
derivative identity is a separate analytic obligation; it is not an axiom here.
The KL sign theorem applies to the specified affine family with fixed weights. -/
noncomputable section
namespace Entropic.FiniteStatistics
open Finset
variable {ι : Type*} [Fintype ι]

theorem bounded_second_moment (p x : ι → ℝ) (a b : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hn : ∑ i, p i = 1)
    (ha : ∀ i, a ≤ x i) (hb : ∀ i, x i ≤ b) :
    (∑ i, p i * (x i)^2) ≤ (a+b) * (∑ i, p i*x i) - a*b := by
  have h : ∀ i, p i * (x i)^2 ≤ (a+b)*(p i*x i) - a*b*p i := by
    intro i
    have hlocal := mul_nonneg (sub_nonneg.mpr (ha i)) (sub_nonneg.mpr (hb i))
    have hweighted := mul_nonneg (hp i) hlocal
    nlinarith
  have hh := sum_le_sum (fun i (_ : i ∈ univ) => h i)
  simpa only [sum_sub_distrib, ← mul_sum, hn, mul_one] using hh

theorem variance_bound (p x : ι → ℝ) (a b : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hn : ∑ i, p i = 1)
    (ha : ∀ i, a ≤ x i) (hb : ∀ i, x i ≤ b) :
    (∑ i, p i * (x i)^2) - (∑ i, p i*x i)^2 ≤ (b-a)^2/4 := by
  have h := bounded_second_moment p x a b hp hn ha hb
  nlinarith [sq_nonneg ((∑ i, p i*x i) - (a+b)/2)]

theorem capacity_variance_bound (p x : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hn : ∑ i, p i = 1)
    (ha : ∀ i, (122:ℝ)/3 ≤ x i) (hb : ∀ i, x i ≤ (170:ℝ)/3) :
    (∑ i, p i * (x i)^2) - (∑ i, p i*x i)^2 ≤ 64 := by
  have h := variance_bound p x ((122:ℝ)/3) ((170:ℝ)/3) hp hn ha hb
  norm_num at h ⊢
  exact h

theorem stationary_window {eta mean : ℝ}
    (hlo : (122:ℝ)/3 ≤ mean) (hhi : mean ≤ (170:ℝ)/3)
    (hroot : eta*mean = (3:ℝ)/2) :
    (9:ℝ)/340 ≤ eta ∧ eta ≤ (9:ℝ)/244 := by
  have hm : 0 < mean := by linarith
  have he : 0 < eta := by
    by_contra h
    have hneg := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) (le_of_lt hm)
    linarith
  constructor <;> nlinarith

theorem gibbs_product_derivative_lower_bound {eta mean variance : ℝ}
    (he0 : 0 ≤ eta) (he1 : eta ≤ (9:ℝ)/244)
    (hm : (122:ℝ)/3 ≤ mean) (hv : variance ≤ 64) :
    (7010:ℝ)/183 ≤ mean - eta*variance := by
  have h := mul_le_mul_of_nonneg_left hv he0
  nlinarith

theorem affine_kl_summand_nonneg {d e : ℝ}
    (hd : 0 ≤ d) (hs : 0 < 1+d*e) :
    0 ≤ e * Real.log (1+d*e) := by
  by_cases he : 0 ≤ e
  · exact mul_nonneg he (Real.log_nonneg (by nlinarith))
  · have he' : e ≤ 0 := le_of_not_ge he
    exact mul_nonneg_of_nonpos_of_nonpos he'
      (Real.log_nonpos (le_of_lt hs) (by nlinarith))

theorem affine_kl_derivative_nonneg (p e : ι → ℝ) {d : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hd : 0 ≤ d) (hs : ∀ i, 0 < 1+d*e i) :
    0 ≤ ∑ i, p i * (e i * Real.log (1+d*e i)) := by
  exact sum_nonneg (fun i _ => mul_nonneg (hp i)
    (affine_kl_summand_nonneg hd (hs i)))

end Entropic.FiniteStatistics
