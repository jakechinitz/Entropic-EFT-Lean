import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

/-! Appendix B supplements (ledger C04-06, C04-69, C04-82). -/

namespace Entropic.AppB

/-- C04-06: a common positive rescaling of S_ent, S_inf and κ/γ leaves δS/S_inf and
κ/(γ S_inf) unchanged (so G = c²κ/(8πγS_inf) is fixed). -/
theorem rescaling_invariance {l : ℝ} (hl : 0 < l) (dS S k : ℝ) :
    (l * dS) / (l * S) = dS / S ∧ (l * k) / (l * S) = k / S := by
  constructor <;> rw [mul_div_mul_left _ _ hl.ne']

/-- C04-69: complement isometry. If I : Q → V₁⊗V₁ is a partial isometry with initial
projection P (I†I = P, II† = 1) and W is unitary, then L = W I P has L†L = P and LL† = 1.
Stated in any monoid with an involutive anti-multiplicative star (operators on a
finite Hilbert space, matrices, a C*-algebra). -/
theorem complement_isometry {R : Type*} [Monoid R] [StarMul R] (P I W : R)
    (hP : P * P = P) (hPs : star P = P) (hI1 : star I * I = P) (hI2 : I * star I = 1)
    (hW1 : star W * W = 1) (hW2 : W * star W = 1) :
    star (W * I * P) * (W * I * P) = P ∧ (W * I * P) * star (W * I * P) = 1 := by
  have hIP : I * P = I := by rw [← hI1, ← mul_assoc, hI2, one_mul]
  have hs : star (W * I * P) = P * star I * star W := by
    simp only [star_mul, hPs, mul_assoc]
  rw [hs]
  constructor
  · calc P * star I * star W * (W * I * P) = P * (star I * (star W * W) * I) * P := by
          simp only [mul_assoc]
      _ = P := by rw [hW1, mul_one, hI1, hP, hP]
  · calc W * I * P * (P * star I * star W) = W * ((I * P) * star I) * star W := by
          simp only [mul_assoc]
          rw [← mul_assoc P P, hP]
      _ = 1 := by rw [hIP, hI2, mul_one, hW2]

/-- C04-82: the B.5.2 counting conventions at seven letters. -/
theorem counting_conventions :
    2 * Nat.descFactorial 7 4 = 1680 ∧ Nat.descFactorial 7 4 = 840 ∧ 2 * 7 ^ 4 = 4802 ∧
      2 * Nat.choose 7 4 = 70 ∧ Nat.choose 7 4 = 35 := by
  decide

/-- C04-67: dim Q(j) = (2j+1)² − (4j+1) = 4j², and for j, s ≥ 0 the match
4j² = (2s+1)² holds iff 2j = 2s+1. -/
theorem dimension_match {j s : ℝ} (hj : 0 ≤ j) (hs : 0 ≤ s) :
    (2 * j + 1) ^ 2 - (4 * j + 1) = 4 * j ^ 2 ∧
      (4 * j ^ 2 = (2 * s + 1) ^ 2 ↔ 2 * j = 2 * s + 1) := by
  refine ⟨by ring, ⟨fun h => ?_, fun h => by nlinarith⟩⟩
  have h' : (2 * j) ^ 2 = (2 * s + 1) ^ 2 := by nlinarith
  exact (sq_eq_sq₀ (by positivity) (by positivity)).mp h'

end Entropic.AppB
