import Mathlib

/-! Underdetermination certificates concern omitted physical selection data,
not the explicitly matched branch of the paper. -/
noncomputable section
open scoped BigOperators
namespace Entropic.FourItems.Selection

theorem arbitrary_physical_matching (Gstar target : ℝ) (hs : 0<Gstar) (ht : 0<target) :
    ∃ beta : ℝ, 0<beta ∧ Gstar/beta=target := by
  refine ⟨Gstar/target, div_pos hs ht, ?_⟩
  field_simp

theorem matched_branch (Gstar : ℝ) : Gstar/(1:ℝ)=Gstar := by ring

-- Convolution is positive and affine in the entry-loss K0, at fixed tail time.
theorem entry_loss_affine (K0 immediate delayed : ℝ) :
    K0*immediate+(1-K0)*delayed=delayed+K0*(immediate-delayed) := by ring

theorem normalization_can_select_entry_loss (target immediate delayed : ℝ)
    (h : immediate≠delayed) :
    delayed+((target-delayed)/(immediate-delayed))*(immediate-delayed)=target := by
  rw [div_mul_cancel₀ _ (sub_ne_zero.mpr h)]
  ring

theorem entry_loss_in_unit_interval (target immediate delayed : ℝ)
    (h : delayed < immediate) (hl : delayed ≤ target) (hu : target ≤ immediate) :
    0 ≤ (target-delayed)/(immediate-delayed) ∧
    (target-delayed)/(immediate-delayed) ≤ 1 := by
  constructor
  · exact div_nonneg (by linarith) (by linarith)
  · exact (div_le_one (by linarith)).mpr (by linarith)

-- An unlimited supply of registers is part of the constructed state space.
-- A reversible swap uses it but does not manufacture that resource.
def swapRegister {α : Type*} (p : α × α) : α × α := (p.2,p.1)

theorem swap_involutive {α : Type*} (p : α × α) :
    swapRegister (swapRegister p)=p := by cases p; rfl

theorem swap_energy {α : Type*} (E : α → ℝ) (p : α × α) :
    E (swapRegister p).1+E (swapRegister p).2=E p.1+E p.2 := by
  simp [swapRegister, add_comm]

theorem history_capacity_growth (d N : ℕ) : d^(N+1)=d^N*d := pow_succ _ _

-- A source-independent discarded partition factor cancels from normalized
-- source ratios. Source dependence invalidates that cancellation.
theorem source_independent_factor (z z0 h : ℝ) (hh : h≠0) :
    (z*h)/(z0*h)=z/z0 := by exact mul_div_mul_right z z0 hh

theorem source_dependent_factor_counterexample :
    ((2:ℝ)*3)/(1*1)≠2/1 := by norm_num

-- A finite compensating battery can make every native code state have the
-- same energy. Fresh zero-Hamiltonian history registers are still an input.
def battery (ceiling energy : ℝ) := ceiling-energy

theorem battery_nonnegative (ceiling energy : ℝ) (h : energy ≤ ceiling) :
    0 ≤ battery ceiling energy := sub_nonneg.mpr h

theorem code_energy (ceiling energy : ℝ) :
    energy+battery ceiling energy=ceiling := by unfold battery; ring

theorem reset_energy (ceiling oldEnergy newEnergy : ℝ) :
    oldEnergy+battery ceiling oldEnergy=newEnergy+battery ceiling newEnergy := by
  unfold battery; ring

theorem native_battery_range (k : ℝ) (hlo : 122 ≤ k) (hhi : k ≤ 170) :
    0 ≤ battery (170/3) (k/3) ∧ battery (170/3) (k/3) ≤ 16 := by
  unfold battery; constructor <;> linarith

theorem battery_balance (ceiling oldEnergy newEnergy : ℝ) :
    battery ceiling newEnergy-battery ceiling oldEnergy=oldEnergy-newEnergy := by
  unfold battery; ring

-- Inner product of W x and W y, for W|r> = sum_s a_s |s;r,s>.
-- This proves the Gram identity for any finite alphabet, including the native
-- one. The battery embedding is orthogonal and does not alter the identity.
theorem reset_inner {ι : Type*} [Fintype ι] (a x y : ι → ℝ)
    (ha : ∑ j, (a j)^2 = 1) :
    (∑ i, ∑ j, (a j*x i)*(a j*y i)) = ∑ i, x i*y i := by
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∑ j, (a j*x i)*(a j*y i)) = ∑ j, (a j)^2*(x i*y i) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ j, (a j)^2)*(x i*y i) := by rw [Finset.sum_mul]
    _ = x i*y i := by rw [ha]; ring

end Entropic.FourItems.Selection
