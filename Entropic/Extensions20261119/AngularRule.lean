import Entropic.BlackHole
import Entropic.AppQ.Algebra
import Mathlib.Tactic

/-!
# Flat subdivision fixes the angular rule (Appendix Q.11)

Q.11 specifies the wedge transfer `K_h(θ) = e^{−bθ} I₂` with `K_h(2π) = ρ_h = I₂/2`. This file proves
that the rule is forced by two conditions:

* the wedge factor is a positive scalar `k(θ)` of the wedge angle alone, continuous, and multiplicative
  under splitting a wedge, `k(θ₁ + θ₂) = k(θ₁) k(θ₂)` (inserting a point in a flat four-simplex splits
  every old wedge in an arbitrary ratio);
* a new flat interior triangle, whose wedges close to `2π`, carries weight one: `2 k(2π) = 1`.

Then `k(θ) = e^{−bθ}` with `b = ln 2/(2π)` (`flat_subdivision_fixes_rule`), which is `AppQ.bH`.
For any other amplitude a flat interior hinge carries log-weight `ln 2 − 2πb' ≠ 0` per channel
(`wrong_amplitude_weight`). The multiplicative step reuses the Cauchy argument of
`BlackHole.lapse_is_power`.

Input, as in the manuscript: that the wedge factor is a scalar depending on the angle alone (port-number
conservation, occupation exchange, and the lattice Bisognano–Wichmann property of the bond vacuum).
-/

noncomputable section
namespace Entropic.Extensions20261119.AngularRule
open Real Set

/-- The amplitude of the angular rule. -/
def bFlat : ℝ := Real.log 2 / (2 * π)

theorem bFlat_eq_bH : bFlat = Entropic.AppQ.bH := rfl

theorem two_pi_bFlat : 2 * π * bFlat = Real.log 2 := by unfold bFlat; field_simp

variable {k : ℝ → ℝ}

/-- Flat-subdivision invariance forces `k(θ) = e^{−θ ln 2/(2π)}` for every `θ ≥ 0`. -/
theorem flat_subdivision_fixes_rule
    (hpos : ∀ θ, 0 ≤ θ → 0 < k θ)
    (hcont : ContinuousOn k (Ici 0))
    (hsplit : ∀ a, 0 ≤ a → ∀ c, 0 ≤ c → k (a + c) = k a * k c)
    (hflat : 2 * k (2 * π) = 1) :
    ∀ θ, 0 ≤ θ → k θ = Real.exp (-bFlat * θ) := by
  -- transport to the multiplicative law on (0,1]
  set f : ℝ → ℝ := fun q => k (-Real.log q) with hf
  have hlog : ∀ q ∈ Ioc (0:ℝ) 1, 0 ≤ -Real.log q := fun q hq => by
    have := Real.log_nonpos hq.1.le hq.2; linarith
  have fpos : ∀ q ∈ Ioc (0:ℝ) 1, 0 < f q := fun q hq => hpos _ (hlog q hq)
  have fmul : ∀ x ∈ Ioc (0:ℝ) 1, ∀ y ∈ Ioc (0:ℝ) 1, f (x * y) = f x * f y := by
    intro x hx y hy
    simp only [hf]
    rw [Real.log_mul hx.1.ne' hy.1.ne', neg_add]
    exact hsplit _ (hlog x hx) _ (hlog y hy)
  have fcont : ContinuousOn f (Ioc (0:ℝ) 1) := by
    have hl : ContinuousOn (fun q : ℝ => -Real.log q) (Ioc (0:ℝ) 1) :=
      (Real.continuousOn_log.mono (fun q hq => (show q ≠ 0 from hq.1.ne'))).neg
    exact hcont.comp hl (fun q hq => hlog q hq)
  obtain ⟨α, hα⟩ := Entropic.BlackHole.lapse_is_power fpos fmul fcont
  have hk : ∀ θ, 0 ≤ θ → k θ = Real.exp (-α * θ) := by
    intro θ hθ
    have hm := Entropic.BlackHole.exp_neg_mem hθ
    have h1 := hα _ hm
    simp only [hf, Real.log_exp, neg_neg] at h1
    rw [h1, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]; ring_nf
  -- the flat condition fixes α
  have h2 : Real.exp (-α * (2 * π)) = 1 / 2 := by
    have := hk (2 * π) (by positivity); linarith [this ▸ hflat]
  have h3 : -α * (2 * π) = -Real.log 2 := by
    have := congrArg Real.log h2
    rw [Real.log_exp, one_div, Real.log_inv] at this; exact this
  have hαb : α = bFlat := by
    unfold bFlat; field_simp; linarith
  intro θ hθ; rw [hk θ hθ, hαb]

/-- The rule itself satisfies the conditions. -/
theorem rule_satisfies :
    (∀ a c : ℝ, Real.exp (-bFlat * (a + c)) = Real.exp (-bFlat * a) * Real.exp (-bFlat * c)) ∧
    2 * Real.exp (-bFlat * (2 * π)) = 1 := by
  refine ⟨fun a c => by rw [← Real.exp_add]; ring_nf, ?_⟩
  rw [show -bFlat * (2 * π) = -Real.log 2 by rw [← two_pi_bFlat]; ring, Real.exp_neg,
    Real.exp_log (by norm_num)]
  norm_num

/-- A flat interior hinge with amplitude `b'` has log-weight `ln 2 − 2πb'` per channel; it vanishes only
at `b' = ln 2/(2π)`. -/
theorem wrong_amplitude_weight (b' : ℝ) :
    Real.log (2 * Real.exp (-b' * (2 * π))) = Real.log 2 - 2 * π * b' ∧
    (Real.log 2 - 2 * π * b' = 0 ↔ b' = bFlat) := by
  constructor
  · rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]; ring
  · unfold bFlat; constructor
    · intro h; field_simp; linarith
    · intro h; rw [h]; field_simp; ring

/-- The hinge weight of the rule is exactly linear in the deficit angle: `2 e^{−b(2π−δ)} = e^{bδ}`. -/
theorem hinge_linear (δ : ℝ) : 2 * Real.exp (-bFlat * (2 * π - δ)) = Real.exp (bFlat * δ) := by
  rw [show -bFlat * (2 * π - δ) = -(2 * π * bFlat) + bFlat * δ by ring, two_pi_bFlat, Real.exp_add,
    Real.exp_neg, Real.exp_log (by norm_num)]; ring

end Entropic.Extensions20261119.AngularRule
