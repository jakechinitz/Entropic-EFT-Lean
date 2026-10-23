import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-! One-pass dressing operator on the seven-factor history space (ledger C05-70).
Functions on configurations `Fin n → α` stand for vectors in ⊗ⁿ ℝ^α. `T K m` applies the
kernel K on factor m and the identity elsewhere. The T_m commute, so the one-pass product
is order independent, and it equals the full tensor power K^{⊗n}. -/

noncomputable section
namespace Entropic.AppCDE.History
open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

abbrev V (α : Type*) (n : ℕ) := (Fin n → α) → ℝ

/-- Kernel K acting on tensor factor m. -/
def T (K : α → α → ℝ) (m : Fin n) : Function.End (V α n) :=
  fun f x => ∑ b, K (x m) b * f (Function.update x m b)

theorem T_apply (K : α → α → ℝ) (m : Fin n) (f : V α n) (x : Fin n → α) :
    (T K m : V α n → V α n) f x = ∑ b, K (x m) b * f (Function.update x m b) := rfl

/-- Operators on distinct factors commute. -/
theorem T_comm (K : α → α → ℝ) {m k : Fin n} (h : m ≠ k) : Commute (T K m) (T K k) := by
  unfold Commute SemiconjBy
  funext f x
  show (T K m) ((T K k) f) x = (T K k) ((T K m) f) x
  simp only [T_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_))
  rw [Function.update_of_ne h.symm, Function.update_of_ne h, Function.update_comm h]
  ring

/-- Tensor power K^{⊗n}. -/
def Kpow (K : α → α → ℝ) : V α n → V α n :=
  fun f x => ∑ y, (∏ i, K (x i) (y i)) * f y

/-- Partial product formula: applying T on the (distinct) coordinates of `l`. -/
theorem partial_prod (K : α → α → ℝ) (l : List (Fin n)) (hl : l.Nodup) (f : V α n)
    (x : Fin n → α) :
    ((l.map (T K)).prod : V α n → V α n) f x =
      ∑ y, (∏ i ∈ l.toFinset, K (x i) (y i)) *
        (∏ i ∈ l.toFinsetᶜ, if y i = x i then 1 else 0) * f y := by
  induction l generalizing x with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.toFinset_nil, Finset.prod_empty, one_mul,
      Finset.compl_empty]
    show f x = _
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      obtain ⟨i, hi⟩ : ∃ i, y i ≠ x i := by
        by_contra h; push_neg at h; exact hy (funext h)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), zero_mul]
    · simp
  | cons m l ih =>
    have hm : m ∉ l := (List.nodup_cons.mp hl).1
    have hl' := (List.nodup_cons.mp hl).2
    simp only [List.map_cons, List.prod_cons]
    show (T K m : V α n → V α n) (((l.map (T K)).prod : V α n → V α n) f) x = _
    rw [T_apply]
    simp_rw [ih hl']
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    have hmL : m ∉ l.toFinset := by simpa using hm
    have e1 : ∀ b, ∏ i ∈ l.toFinset, K (Function.update x m b i) (y i) =
        ∏ i ∈ l.toFinset, K (x i) (y i) := by
      intro b; refine Finset.prod_congr rfl (fun i hi => ?_)
      rw [Function.update_of_ne (fun h => hmL (by rw [← h]; exact hi))]
    have hcompl : l.toFinsetᶜ = insert m ((m :: l).toFinsetᶜ) := by
      ext i; by_cases h : i = m <;> simp [h, hm]
    have hnot : m ∉ (m :: l).toFinsetᶜ := by simp
    have e2 : ∀ b, ∏ i ∈ l.toFinsetᶜ, (if y i = Function.update x m b i then (1:ℝ) else 0) =
        (if y m = b then 1 else 0) *
          ∏ i ∈ (m :: l).toFinsetᶜ, (if y i = x i then (1:ℝ) else 0) := by
      intro b
      rw [hcompl, Finset.prod_insert hnot, Function.update_self]
      congr 1
      refine Finset.prod_congr rfl (fun i hi => ?_)
      have : i ≠ m := fun h => hnot (h ▸ hi)
      rw [Function.update_of_ne this]
    simp_rw [e1, e2]
    have e3 : ∑ b, K (x m) b * ((∏ i ∈ l.toFinset, K (x i) (y i)) *
        ((if y m = b then 1 else 0) * ∏ i ∈ (m :: l).toFinsetᶜ, (if y i = x i then (1:ℝ) else 0)) *
          f y) = K (x m) (y m) * ((∏ i ∈ l.toFinset, K (x i) (y i)) *
            ∏ i ∈ (m :: l).toFinsetᶜ, (if y i = x i then (1:ℝ) else 0)) * f y := by
      rw [Finset.sum_eq_single (y m)]
      · simp; ring
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    rw [e3]
    rw [List.toFinset_cons, Finset.prod_insert hmL]
    ring

/-- C05-70: the one-pass operator T_{m₁}⋯T_{m_n} (each factor once, any order) equals the
tensor power K^{⊗n}. -/
theorem one_pass_eq_tensor_power (K : α → α → ℝ) (l : List (Fin n)) (hl : l.Nodup)
    (hall : ∀ i, i ∈ l) : ((l.map (T K)).prod : V α n → V α n) = Kpow K := by
  funext f x
  rw [partial_prod K l hl f x]
  have : l.toFinset = Finset.univ := by ext i; simp [hall i]
  simp [this, Kpow]

/-- Order independence, stated directly: any two orderings give the same operator. -/
theorem order_independent (K : α → α → ℝ) (l₁ l₂ : List (Fin n)) (h₁ : l₁.Nodup)
    (h₂ : l₂.Nodup) (a₁ : ∀ i, i ∈ l₁) (a₂ : ∀ i, i ∈ l₂) :
    (l₁.map (T K)).prod = (l₂.map (T K)).prod := by
  exact (one_pass_eq_tensor_power K l₁ h₁ a₁).trans (one_pass_eq_tensor_power K l₂ h₂ a₂).symm

end Entropic.AppCDE.History
