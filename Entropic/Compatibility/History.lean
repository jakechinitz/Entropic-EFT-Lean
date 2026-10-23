import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Entropic.HistoryCapacity

/-! Two different history branches, with no claim that a periodic orbit is IID.
The growing archive is an exactly consistent family of finite product laws.
An infinite product probability measure and a unitary implementation are not
constructed here. The finite 720-cycle witnesses the arithmetic return branch.
-/
noncomputable section
open scoped BigOperators
namespace Entropic.Compatibility.History

structure FiniteArchive where
  capacity : ℕ
  encode : (n : ℕ) → (Fin n → Bool) → Fin capacity
  faithful : ∀ n, Function.Injective (encode n)

theorem finiteArchive_isEmpty : IsEmpty FiniteArchive := by
  constructor
  intro m
  apply Entropic.HistoryCapacity.no_finite_archive m.capacity
  intro n
  simpa using Entropic.HistoryCapacity.independent_records_bounded n (m.encode n) (m.faithful n)

variable {α : Type*} [Fintype α]

def historyWeight (p : α → ℝ) (n : ℕ) (h : Fin n → α) : ℝ := ∏ i, p (h i)

theorem history_normalized (p : α → ℝ) (hp : ∑ a, p a = 1) (n : ℕ) :
    ∑ h : Fin n → α, historyWeight p n h = 1 := by
  unfold historyWeight
  rw [← Fintype.prod_sum]
  simp [hp]

theorem history_positive (p : α → ℝ) (hp : ∀ a, 0 < p a) (n : ℕ) (h : Fin n → α) :
    0 < historyWeight p n h := Finset.prod_pos (fun i _ => hp (h i))

def extend (h : Fin n → α) (a : α) : Fin (n+1) → α := Fin.snoc h a

theorem extension_weight (p : α → ℝ) (h : Fin n → α) (a : α) :
    historyWeight p (n+1) (extend h a) = historyWeight p n h * p a := by
  simp [historyWeight, extend, Fin.prod_univ_castSucc]

theorem consistent_prefix (p : α → ℝ) (hp : ∑ a, p a = 1) (h : Fin n → α) :
    ∑ a, historyWeight p (n+1) (extend h a) = historyWeight p n h := by
  simp_rw [extension_weight]
  rw [← Finset.mul_sum, hp, mul_one]

theorem extension_recoverable : Function.Injective
    (fun ha : (Fin n → α) × α => extend ha.1 ha.2) := by
  intro x y h
  apply Prod.ext
  · funext i
    have hi := congrFun h i.castSucc
    simpa [extend] using hi
  · have hi := congrFun h (Fin.last n)
    simpa [extend] using hi

theorem archive_size (n : ℕ) : Fintype.card (Fin n → α) = Fintype.card α ^ n := by simp

def shellAt (s : ZMod 720) (n : ℕ) : ZMod 720 := s + n

def shellTick : Equiv.Perm (ZMod 720) where
  toFun s := s + 1
  invFun s := s - 1
  left_inv s := by ring
  right_inv s := by ring

theorem shell_tick (s : ZMod 720) (n : ℕ) :
    shellAt s (n+1) = shellTick (shellAt s n) := by
  simp [shellAt, shellTick, Nat.cast_add, Nat.cast_one, add_assoc]

theorem shell_returns (s : ZMod 720) : shellAt s 720 = s := by
  simp only [shellAt, ZMod.natCast_self, add_zero]

theorem shell_no_early_return (s : ZMod 720) {n : ℕ} (h0 : 0 < n) (h1 : n < 720) :
    shellAt s n ≠ s := by
  intro h
  have hz : (n : ZMod 720) = 0 := add_left_cancel (show s + (n : ZMod 720) = s + 0 by simpa [shellAt] using h)
  have hd := (ZMod.natCast_eq_zero_iff n 720).mp hz
  exact (not_le.mpr h1) (Nat.le_of_dvd h0 hd)

theorem shell_stationary (f : ZMod 720 → ℝ) :
    (∑ s, f (shellTick s) / 720) = ∑ s, f s / 720 := by
  exact Equiv.sum_comp shellTick (fun s => f s / 720)

theorem shell_probability : (∑ _s : ZMod 720, (1:ℝ)/720) = 1 := by
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  norm_num

theorem shell_arithmetic_mean_return :
    (∑ _s : ZMod 720, ((1:ℝ)/720) * 720) = 720 := by
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  norm_num

-- The deterministic successor forbids some two-letter words; it is not a
-- realization of a full-support IID renewal law on the same shell variable.
theorem shell_not_memoryless : ¬ ∀ a b : ZMod 720, ∃ s, s = a ∧ shellTick s = b := by
  letI : Fact (1 < 720) := ⟨by decide⟩
  intro h
  obtain ⟨s, rfl, hs⟩ := h 0 0
  have hh : (1 : ZMod 720) = 0 := by simpa only [shellTick, Equiv.coe_fn_mk, zero_add] using hs
  exact (one_ne_zero : (1 : ZMod 720) ≠ 0) hh

end Entropic.Compatibility.History
