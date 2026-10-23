import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! History capacity (App. P.9; response to critique item 7).

Two horns, both kernel checked.

(A) EXACT memoryless renewal with every per-tick draw kept recoverable needs
    2^N ≤ D after N ticks, so no finite capacity suffices (`exact_export_bound`,
    `no_finite_archive`). This is the manuscript's P.9 non-reuse theorem; it is
    what forces the "non-geometric history factor".

(B) A FINITE reversible (bijective) dynamics on D states keeps the initial state
    exactly recoverable after any number of ticks with D fixed
    (`initial_state_recoverable`), and it recurs: some power is the identity
    (`finite_reversible_recurs`). What it cannot do is store more than log₂ D
    independent binary records (`independent_records_bounded`).

So the choice is between an unbounded external archive (A) and finite capacity with
effective (mixing) memorylessness and super-exponential recurrence (B). -/

namespace Entropic.HistoryCapacity

/-- (A) If N ticks each export d_k ≥ 2 alternatives and all joint histories stay
distinguishable inside D states, then 2^N ≤ D. -/
theorem exact_export_bound (N D : ℕ) (d : Fin N → ℕ) (hd : ∀ k, 2 ≤ d k)
    (f : ((k : Fin N) → Fin (d k)) → Fin D) (hf : Function.Injective f) : 2 ^ N ≤ D := by
  have h1 := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_pi, Fintype.card_fin] at h1
  calc 2 ^ N = ∏ _k : Fin N, 2 := by simp
    _ ≤ ∏ k : Fin N, d k := Finset.prod_le_prod' (fun k _ => hd k)
    _ ≤ D := h1

/-- (A) No fixed capacity holds an exactly recoverable memoryless history forever. -/
theorem no_finite_archive (D : ℕ) : ¬ ∀ N : ℕ, 2 ^ N ≤ D :=
  fun h => absurd (h D) (not_le.mpr Nat.lt_two_pow_self)

variable {α : Type*} [Fintype α]

omit [Fintype α] in
/-- (B) Reversible finite dynamics: after any number of ticks the initial state is
exactly recoverable (σ^N is injective), with the state space fixed. -/
theorem initial_state_recoverable (σ : Equiv.Perm α) (N : ℕ) :
    Function.Injective (σ ^ N) := (σ ^ N).injective

/-- (B) Poincaré recurrence for finite reversible dynamics: some positive power of the
one-tick map is the identity. -/
theorem finite_reversible_recurs (σ : Equiv.Perm α) : ∃ k : ℕ, 0 < k ∧ σ ^ k = 1 :=
  ⟨orderOf σ, orderOf_pos σ, pow_orderOf_eq_one σ⟩

/-- (B) Every state returns: for each state a the orbit revisits a. -/
theorem every_state_returns (σ : Equiv.Perm α) (a : α) : ∃ k : ℕ, 0 < k ∧ (σ ^ k) a = a := by
  obtain ⟨k, hk, h⟩ := finite_reversible_recurs σ
  exact ⟨k, hk, by rw [h]; rfl⟩

/-- (B) Capacity limit: r independent binary records can be stored injectively in a
finite state space only if 2^r ≤ |α|. -/
theorem independent_records_bounded (r : ℕ) (f : (Fin r → Bool) → α)
    (hf : Function.Injective f) : 2 ^ r ≤ Fintype.card α := by
  have := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using this

/-- Overflow in exponent form: if N binary draws must be distinguishable inside a space
of at most 2^M states, then N ≤ M. -/
theorem overflow_exponent {N M D : ℕ} (hN : 2 ^ N ≤ D) (hD : D ≤ 2 ^ M) : N ≤ M :=
  (Nat.pow_le_pow_iff_right (by norm_num)).mp (hN.trans hD)

/-- Numerical form of the paper's own comparison: ≥ 10^243 recoverable binary draws do
not fit a space of log₂-capacity 10^123 (S_dS ≈ 3.3·10^122 nats ≈ 4.8·10^122 bits). -/
theorem desitter_overflow {N M D : ℕ} (hN : 10 ^ 243 ≤ N) (hM : M ≤ 10 ^ 123)
    (hND : 2 ^ N ≤ D) (hDM : D ≤ 2 ^ M) : False := by
  have := overflow_exponent hND hDM
  have h : (10:ℕ) ^ 123 < 10 ^ 243 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  omega

end Entropic.HistoryCapacity
