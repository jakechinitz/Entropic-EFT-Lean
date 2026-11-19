import Mathlib.Tactic

/-!
# Count content of the host couplings (Appendix J.12)

On a closed causal triangulation of `S¹ × S³` with one channel per spacelike triangle and `r` channels
per timelike triangle, the hinge traces give `ln 2 (N₂^SL + r N₂^TL)`. With the counting identities
`N₂^SL = N₄₁` and `N₂^TL = 2N₀ + N₄₁ + 2N₃₂` (Dehn–Sommerville relations, Ambjørn–Jurkiewicz–Loll 2001;
checked on twenty triangulations in `02 Research/Einstein weight as a count 2026-11-18`), every
per-simplex scalar factor leaves the coefficient of `N₀` at `2r ln 2`.

Matching to `S_E = −(κ₀+6Δ)N₀ + (κ₄+2Δ)N₄₁ + (κ₄+Δ)N₃₂`:

* `einstein_coefficient`: `κ₀ + 6Δ = 2r ln 2`, whatever the per-simplex factors `c₄₁, c₃₂`;
* `delta_from_amplitude`: with the angular factors `c_σ = −(b'/b) ln 2 · S_σ`,
  `Δ = ln 2 [(r − 1) − (b'/b)(S₃₂ − S₄₁)]`;
* `centring_shift`: a term `−x N₄₁/2` in `S_E` shifts `(κ₀, Δ, κ₄)` by `(3x, −x/2, x/2)` and
  leaves `κ₀ + 6Δ` unchanged;
* `alpha_seven`: `r = 3` is the bundle of `α = 7` (`r² = (4α − 1)/3`).

The coverage sums `S₄₁ = 4.5013`, `S₃₂ = 6.0308` (dihedral angles at `α = 7`) are numerical inputs.
-/

noncomputable section
namespace Entropic.Extensions20261119.HostCount

/-- Log-weight of the hinge traces and per-simplex factors. -/
def logW (r c41 c32 N41 N32 N2SL N2TL : ℝ) : ℝ :=
  Real.log 2 * (N2SL + r * N2TL) + c41 * N41 + c32 * N32

/-- With the counting identities, the log-weight is linear in `(N₀, N₄₁, N₃₂)` with `N₀`-coefficient
`2r ln 2`. -/
theorem logW_counts (r c41 c32 N0 N41 N32 N2SL N2TL : ℝ)
    (hSL : N2SL = N41) (hTL : N2TL = 2 * N0 + N41 + 2 * N32) :
    logW r c41 c32 N41 N32 N2SL N2TL =
      2 * r * Real.log 2 * N0 + ((1 + r) * Real.log 2 + c41) * N41 + (2 * r * Real.log 2 + c32) * N32 := by
  unfold logW; rw [hSL, hTL]; ring

/-- Couplings `(κ₀, Δ, κ₄)` whose action `−S_E` equals the log-weight on every count triple have
`κ₀ + 6Δ = 2r ln 2`, independently of the per-simplex factors. -/
theorem einstein_coefficient (r c41 c32 k0 D k4 : ℝ)
    (hmatch : ∀ N0 N41 N32 : ℝ,
      (k0 + 6 * D) * N0 - (k4 + 2 * D) * N41 - (k4 + D) * N32 =
        2 * r * Real.log 2 * N0 + ((1 + r) * Real.log 2 + c41) * N41 + (2 * r * Real.log 2 + c32) * N32) :
    k0 + 6 * D = 2 * r * Real.log 2 ∧
    D = (r - 1) * Real.log 2 + c32 - c41 ∧
    k4 = -(2 * r * Real.log 2 + c32) - D := by
  have h0 := hmatch 1 0 0; have h1 := hmatch 0 1 0; have h2 := hmatch 0 0 1
  refine ⟨by linarith, by linarith, by linarith⟩

/-- Angular factors `c_σ = −(b'/b) ln 2 · S_σ` give `Δ = ln 2 [(r−1) − (b'/b)(S₃₂ − S₄₁)]`. -/
theorem delta_from_amplitude (r ρ S41 S32 k0 D k4 : ℝ)
    (hmatch : ∀ N0 N41 N32 : ℝ,
      (k0 + 6 * D) * N0 - (k4 + 2 * D) * N41 - (k4 + D) * N32 =
        2 * r * Real.log 2 * N0 + ((1 + r) * Real.log 2 + (-ρ * Real.log 2 * S41)) * N41 +
          (2 * r * Real.log 2 + (-ρ * Real.log 2 * S32)) * N32) :
    D = Real.log 2 * ((r - 1) - ρ * (S32 - S41)) ∧ k0 + 6 * D = 2 * r * Real.log 2 := by
  obtain ⟨h1, h2, -⟩ := einstein_coefficient r _ _ k0 D k4 hmatch
  exact ⟨by rw [h2]; ring, h1⟩

/-- A term `−x N₄₁/2` in `S_E` (so `+x N₄₁/2` in `−S_E`) shifts the couplings by `(3x, −x/2, x/2)`. -/
theorem centring_shift (k0 D k4 x N0 N41 N32 : ℝ) :
    ((k0 + 3 * x) + 6 * (D - x / 2)) * N0 - ((k4 + x / 2) + 2 * (D - x / 2)) * N41 -
        ((k4 + x / 2) + (D - x / 2)) * N32 =
      (k0 + 6 * D) * N0 - (k4 + 2 * D) * N41 - (k4 + D) * N32 + x * N41 / 2 ∧
    (k0 + 3 * x) + 6 * (D - x / 2) = k0 + 6 * D := by
  constructor <;> ring

/-- The bundle `r = 3` belongs to `α = 7`: `r² = (4α − 1)/3`. -/
theorem alpha_seven : (3:ℝ) ^ 2 = (4 * 7 - 1) / 3 := by norm_num

/-- At `α = 7` the coefficient of `N₀` is `6 ln 2`. -/
theorem six_ln_two (k0 D k4 c41 c32 : ℝ)
    (hmatch : ∀ N0 N41 N32 : ℝ,
      (k0 + 6 * D) * N0 - (k4 + 2 * D) * N41 - (k4 + D) * N32 =
        2 * 3 * Real.log 2 * N0 + ((1 + 3) * Real.log 2 + c41) * N41 + (2 * 3 * Real.log 2 + c32) * N32) :
    k0 + 6 * D = 6 * Real.log 2 := by
  have := (einstein_coefficient 3 c41 c32 k0 D k4 hmatch).1; linarith

end Entropic.Extensions20261119.HostCount
