import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! Carrier projector claims (p. 33) versus weighted overlapping supports
(pp. 259–261). The application to the manuscript is conditional: identifying
the smooth weights with a multiplicative factor of an idempotent map needs
justification from its record algebra. -/

namespace Entropic.Projectors

def scalarWeight (w : ℝ) (x : ℝ) : ℝ := w * x

/-- Even in one dimension, a multiplicative weight is a projection exactly
when it is binary. This is not a theorem that all conditional expectations
or all smoothing constructions fail. -/
theorem scalarWeight_idempotent_iff (w : ℝ) :
    (∀ x, scalarWeight w (scalarWeight w x) = scalarWeight w x) ↔
      w = 0 ∨ w = 1 := by
  constructor
  · intro h
    have hh := h 1
    simp only [scalarWeight, mul_one] at hh
    have hfactor : w * (w - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfactor with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) x <;> simp [scalarWeight]

theorem fractional_weight_not_idempotent {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) :
    ¬ (∀ x, scalarWeight w (scalarWeight w x) = scalarWeight w x) := by
  rw [scalarWeight_idempotent_iff]
  rintro (h | h) <;> linarith

section Linear
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def weighted (w : ℝ) (E : V →ₗ[ℝ] V) : V →ₗ[ℝ] V := w • E

theorem weighted_twice (w : ℝ) (E : V →ₗ[ℝ] V)
    (hE : ∀ x, E (E x) = E x) (x : V) :
    weighted w E (weighted w E x) = (w * w) • E x := by
  simp [weighted, hE, smul_smul]

/-- The obstruction survives for a nonzero idempotent linear map. -/
theorem weighted_idempotent_forces_binary (w : ℝ) (E : V →ₗ[ℝ] V)
    (hE : ∀ x, E (E x) = E x) (x : V) (hx : E x ≠ 0)
    (hP : ∀ y, weighted w E (weighted w E y) = weighted w E y) :
    w = 0 ∨ w = 1 := by
  have hh := hP x
  rw [weighted_twice w E hE x] at hh
  change (w * w) • E x = w • E x at hh
  have hz : (w * w - w) • E x = 0 := by rw [sub_smul, hh, sub_self]
  have hs : w * w - w = 0 := (smul_eq_zero.mp hz).resolve_right hx
  have hf : w * (w - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hf with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linarith)

end Linear
end Entropic.Projectors
