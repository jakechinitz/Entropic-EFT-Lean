import Mathlib.Tactic

/-!
# Cavity ensemble from the angular rule (Appendix F.5)

For a spherical cavity of `N_B` boundary channels, the capped and uncapped fillings of `S¹ × S²` have
reduced weight `−ln(W_cap/W_gas) = N_B ln 2 · F(τ, x)` with

  `F(τ, x) = τ (1 − √(1 − x)) − x²`,  `x² = N/N_B`,  `τ = β/(π r_B)`,

York's cavity action written in channel counts. The cap wins where `F < 0`.

* `F_critical_nonneg`: at `τ = 32/27`, `F ≥ 0` on `[0, 1]`, with zeros only at `x = 0` and `x = 8/9`;
* `gas_wins` (`τ > 32/27`) and `cap_wins` (`τ < 32/27`): the transition is at `τ_c = 32/27`;
* `coexistence`: `F = 0` and `∂F/∂x = 0` at `(32/27, 8/9)`, so the jump is `N = (64/81) N_B`,
  and `T_c r_B = 27/(32π)`;
* `stationary_bound`: stationary caps exist only for `τ ≤ 8√3/9`;
* `unbiased_boundary`: a boundary weight `e^{−γ}` per channel moves the equilibrium temperature to
  `T_H/(1 − γ/ln 2)`, equal to `T_H` only for `γ = 0`.

The reduced weight itself is derived in the manuscript from the hinge counts of the two fillings
(`02 Research/Black hole transfer audit 2026-11-18`) and is the input here.
-/

noncomputable section
namespace Entropic.Extensions20261119.Cavity
open Real

/-- Reduced weight per `N_B ln 2`. -/
def F (τ x : ℝ) : ℝ := τ * (1 - √(1 - x)) - x ^ 2

/-- In the variable `s = √(1 − x)`. -/
theorem F_in_s (τ x : ℝ) (hx : x ≤ 1) :
    F τ x = τ * (1 - √(1 - x)) - (1 - √(1 - x) ^ 2) ^ 2 := by
  unfold F; rw [Real.sq_sqrt (by linarith)]; ring

private theorem key (s : ℝ) :
    32 / 27 * (1 - s) - (1 - s ^ 2) ^ 2 = (1 - s) * ((s - 1 / 3) ^ 2 * (s + 5 / 3)) := by ring

/-- At `τ = 32/27` the weight is nonnegative on `[0, 1]`. -/
theorem F_critical_nonneg (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ F (32 / 27) x := by
  rw [F_in_s _ _ h1, key]
  have hs0 : 0 ≤ √(1 - x) := Real.sqrt_nonneg _
  have hs1 : √(1 - x) ≤ 1 := by rw [Real.sqrt_le_one]; linarith
  apply mul_nonneg (by linarith); positivity

/-- Its zeros on `[0, 1]` are `x = 0` and `x = 8/9`. -/
theorem F_critical_zero (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    F (32 / 27) x = 0 ↔ x = 0 ∨ x = 8 / 9 := by
  have hs0 : 0 ≤ √(1 - x) := Real.sqrt_nonneg _
  have hsq : √(1 - x) ^ 2 = 1 - x := Real.sq_sqrt (by linarith)
  rw [F_in_s _ _ h1, key]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · left; have : √(1 - x) = 1 := by linarith
      nlinarith
    · rcases mul_eq_zero.mp h' with h'' | h''
      · right; have : √(1 - x) = 1 / 3 := by nlinarith [sq_nonneg (√(1 - x) - 1 / 3)]
        nlinarith
      · linarith
  · rintro (rfl | rfl)
    · simp
    · have : √(1 - 8 / 9 : ℝ) = 1 / 3 := by
        rw [show (1 - 8 / 9 : ℝ) = (1 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [this]; norm_num

/-- Above `τ_c` the gas wins for every cap. -/
theorem gas_wins (τ : ℝ) (hτ : 32 / 27 < τ) (x : ℝ) (h0 : 0 < x) (h1 : x ≤ 1) : 0 < F τ x := by
  have hc := F_critical_nonneg x h0.le h1
  have hs : √(1 - x) < 1 := by rw [Real.sqrt_lt' one_pos]; linarith
  have : F τ x = F (32 / 27) x + (τ - 32 / 27) * (1 - √(1 - x)) := by unfold F; ring
  rw [this]; nlinarith

/-- Below `τ_c` the cap with `x = 8/9` wins. -/
theorem cap_wins (τ : ℝ) (hτ : τ < 32 / 27) : F τ (8 / 9) < 0 := by
  have : √(1 - 8 / 9 : ℝ) = 1 / 3 := by
    rw [show (1 - 8 / 9 : ℝ) = (1 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  unfold F; rw [this]; nlinarith

/-- Coexistence: `F = 0` and `∂F/∂x = τ/(2√(1−x)) − 2x = 0` at `(32/27, 8/9)`; the entropy jump is
`x² = 64/81` of the boundary channels; `T_c r_B = 1/(π τ_c) = 27/(32π)`. -/
theorem coexistence :
    F (32 / 27) (8 / 9) = 0 ∧
    (32 / 27 : ℝ) / (2 * √(1 - 8 / 9)) - 2 * (8 / 9) = 0 ∧
    (8 / 9 : ℝ) ^ 2 = 64 / 81 ∧
    1 / (π * (32 / 27)) = 27 / (32 * π) := by
  have h : √(1 - 8 / 9 : ℝ) = 1 / 3 := by
    rw [show (1 - 8 / 9 : ℝ) = (1 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨?_, ?_, by norm_num, ?_⟩
  · unfold F; rw [h]; norm_num
  · rw [h]; norm_num
  · have := Real.pi_pos; field_simp

/-- The stationarity condition `τ = 4x√(1−x)` has solutions only for `τ ≤ 8√3/9`. -/
theorem stationary_bound (x : ℝ) (_h0 : 0 ≤ x) (h1 : x ≤ 1) :
    4 * x * √(1 - x) ≤ 8 * √3 / 9 := by
  set s := √(1 - x) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ 2 = 1 - x := Real.sq_sqrt (by linarith)
  set u := √3 with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hx : x = 1 - s ^ 2 := by linarith
  rw [hx]
  have hid : 8 * u / 9 - 4 * (1 - s ^ 2) * s = 4 * (s - u / 3) ^ 2 * (s + 2 * u / 3) := by
    have hu3 : u ^ 3 = 3 * u := by rw [pow_succ, hu2]
    nlinarith [hu2, hu3]
  have : 0 ≤ 4 * (s - u / 3) ^ 2 * (s + 2 * u / 3) := by positivity
  linarith

/-- A boundary weight `e^{−γ}` per channel: `T_H/(1 − γ/ln 2) = T_H` only for `γ = 0`. -/
theorem unbiased_boundary (TH γ : ℝ) (hT : TH ≠ 0) (hγ : γ ≠ Real.log 2) :
    TH / (1 - γ / Real.log 2) = TH ↔ γ = 0 := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hd : 1 - γ / Real.log 2 ≠ 0 := by
    intro h; apply hγ; field_simp at h; linarith
  constructor
  · intro h
    rw [div_eq_iff hd] at h
    have : TH * (γ / Real.log 2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hT
    · rcases div_eq_zero_iff.mp h' with h'' | h''
      · exact h''
      · exact absurd h'' hl
  · rintro rfl; simp

end Entropic.Extensions20261119.Cavity
