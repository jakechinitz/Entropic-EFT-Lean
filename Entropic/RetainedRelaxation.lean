import Mathlib.Tactic

/-! O.3 retained angular-marginal update (ported unchanged from the 2026-10-21 stock-adjustment package).
Finite conditional relaxation. The protected label is an explicit
kinetic premise. These theorems do not identify a physical halo label. -/
noncomputable section
open scoped BigOperators
namespace Entropic.RetainedRelaxation
variable {I A : Type*} [Fintype I]

def marginal (w : I → A → ℝ) (a : A) : ℝ := ∑ i, w i a
def relax (w : I → A → ℝ) (p : I → ℝ) (s : ℝ) (i : I) (a : A) : ℝ :=
  (1-s)*w i a + s*p i*marginal w a

theorem marginal_nonneg (w : I → A → ℝ) (hw : ∀ i a, 0 ≤ w i a) (a : A) :
    0 ≤ marginal w a := Finset.sum_nonneg (fun i _ => hw i a)

theorem relax_nonneg (w : I → A → ℝ) (p : I → ℝ) (s : ℝ)
    (hw : ∀ i a, 0 ≤ w i a) (hp : ∀ i, 0 ≤ p i) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (i : I) (a : A) : 0 ≤ relax w p s i a := by
  unfold relax
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hs1) (hw i a))
    (mul_nonneg (mul_nonneg hs (hp i)) (marginal_nonneg w hw a))

theorem marginal_preserved (w : I → A → ℝ) (p : I → ℝ) (s : ℝ)
    (hp : ∑ i, p i = 1) (a : A) : marginal (relax w p s) a = marginal w a := by
  change (∑ i, ((1-s)*w i a+s*p i*marginal w a)) = marginal w a
  have hsum : (∑ i, p i * marginal w a) = marginal w a := by
    rw [← Finset.sum_mul, hp, one_mul]
  calc
    _ = (1-s)*(∑ i, w i a) + s*(∑ i, p i*marginal w a) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = marginal w a := by rw [hsum]; change (1-s)*marginal w a+s*marginal w a=marginal w a; ring

theorem angular_observable_preserved [Fintype A] (w : I → A → ℝ) (p : I → ℝ)
    (s : ℝ) (hp : ∑ i, p i = 1) (g : A → ℝ) :
    (∑ a, g a * marginal (relax w p s) a) = ∑ a, g a * marginal w a := by
  simp only [marginal_preserved w p s hp]

theorem total_preserved [Fintype A] (w : I → A → ℝ) (p : I → ℝ) (s : ℝ)
    (hp : ∑ i, p i = 1) :
    (∑ a, marginal (relax w p s) a) = ∑ a, marginal w a := by
  simp only [marginal_preserved w p s hp]

theorem fixed_target (p : I → ℝ) (m : A → ℝ) (s : ℝ)
    (hp : ∑ i, p i = 1) (i : I) (a : A) :
    relax (fun j b => p j * m b) p s i a = p i * m a := by
  have hm : marginal (fun j b => p j*m b) a = m a := by
    unfold marginal
    rw [← Finset.sum_mul, hp, one_mul]
  simp only [relax, hm]
  ring

theorem deviation_contracted (w : I → A → ℝ) (p : I → ℝ) (s : ℝ)
    (i : I) (a : A) :
    relax w p s i a - p i * marginal w a =
      (1-s)*(w i a-p i*marginal w a) := by
  unfold relax
  ring

omit [Fintype I] in
theorem detailed_balance (p : I → ℝ) (k : ℝ) (i j : I) :
    (k*p i)*p j = (k*p j)*p i := by ring

end Entropic.RetainedRelaxation

