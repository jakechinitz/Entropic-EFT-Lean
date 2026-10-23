import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! An effective positive ledger. Conservation alone does not select this
allocation: composition preservation under pure drain is the extra premise.
These are finite-step and homogeneous results, not a covariant kinetic theory. -/
noncomputable section
namespace Entropic.PositiveLedger

def stepU (u survival conversion : ℝ) := survival * (1 - conversion) * u
def stepR (u r survival conversion : ℝ) := survival * (r + conversion * u)

theorem step_positive {u r s p : ℝ} (hu : 0 ≤ u) (hr : 0 ≤ r)
    (hs : 0 ≤ s) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ stepU u s p ∧ 0 ≤ stepR u r s p := by
  constructor
  · exact mul_nonneg (mul_nonneg hs (sub_nonneg.mpr hp1)) hu
  · exact mul_nonneg hs (add_nonneg hr (mul_nonneg hp hu))

theorem step_total (u r s p : ℝ) :
    stepU u s p + stepR u r s p = s * (u + r) := by
  unfold stepU stepR
  ring

theorem step_budget {u r s p : ℝ} (hu : 0 ≤ u) (hr : 0 ≤ r) (hs : s ≤ 1) :
    stepU u s p + stepR u r s p ≤ u + r := by
  rw [step_total]
  nlinarith

/-- Composition preservation determines the allocation, including at either
empty component boundary, provided the total donor is nonempty. -/
theorem common_fractional_drain_unique {u r du dr Q : ℝ}
    (hC : u + r ≠ 0) (hsum : du + dr = Q) (hratio : du * r = dr * u) :
    du = u / (u + r) * Q ∧ dr = r / (u + r) * Q := by
  rw [← hsum]
  constructor <;> field_simp <;> nlinarith

theorem common_drain_conserves (u r q Q : ℝ) (hC : u + r ≠ 0) :
    (-q - u / (u + r) * Q) + (q - r / (u + r) * Q) + Q = 0 := by
  field_simp <;> ring

def stock (B eta f : ℝ) := B * Real.exp (-eta * f)
def unreleased (B eta f : ℝ) := (1 - f) * stock B eta f
def reallocated (B eta f : ℝ) := f * stock B eta f

theorem component_sum (B eta f : ℝ) :
    unreleased B eta f + reallocated B eta f = stock B eta f := by
  unfold unreleased reallocated
  ring

theorem component_positive {B eta f : ℝ} (hB : 0 ≤ B)
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    0 ≤ unreleased B eta f ∧ 0 ≤ reallocated B eta f := by
  have hC : 0 ≤ stock B eta f := mul_nonneg hB (le_of_lt (Real.exp_pos _))
  exact ⟨mul_nonneg (sub_nonneg.mpr hf1) hC, mul_nonneg hf0 hC⟩

theorem stock_hasDerivAt {f : ℝ → ℝ} {fd t B eta : ℝ}
    (hf : HasDerivAt f fd t) :
    HasDerivAt (fun x => stock B eta (f x))
      (-eta * stock B eta (f t) * fd) t := by
  convert (((hf.const_mul (-eta)).exp).const_mul B) using 1 <;>
    dsimp [stock] <;> ring

/-- The whole positive donor completion has a smooth closed-form solution;
q=C f' and Q=eta q. The relation q=Gamma u requires f'=Gamma(1-f). -/
theorem unreleased_hasDerivAt {f : ℝ → ℝ} {fd t B eta : ℝ}
    (hf : HasDerivAt f fd t) :
    HasDerivAt (fun x => unreleased B eta (f x))
      (-stock B eta (f t) * fd - eta * unreleased B eta (f t) * fd) t := by
  convert (hf.const_sub 1).fun_mul (stock_hasDerivAt (B := B) (eta := eta) hf) using 1 <;>
    dsimp [unreleased] <;> ring

theorem reallocated_hasDerivAt {f : ℝ → ℝ} {fd t B eta : ℝ}
    (hf : HasDerivAt f fd t) :
    HasDerivAt (fun x => reallocated B eta (f x))
      (stock B eta (f t) * fd - eta * reallocated B eta (f t) * fd) t := by
  convert hf.fun_mul (stock_hasDerivAt (B := B) (eta := eta) hf) using 1 <;>
    dsimp [reallocated] <;> ring

end Entropic.PositiveLedger
