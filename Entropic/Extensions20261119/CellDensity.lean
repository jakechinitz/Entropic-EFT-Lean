import Mathlib

/-!
# Response-cell density of Appendix O.3

O.3 fixes the cell density by equipartition matching, `𝒩 Θ = g_b² n(1+n)/(4πG)`, with `Θ = k_B T_H`,
`n = n_B(x)`, `x² = g_b/a₀`. This file proves the equivalent forms used in the manuscript of 19 November 2026:

* `half_theta_mutual`: `𝒩Θ/2 = g_R g_obs/(8πG)` with `g_R = n g_b`, `g_obs = (1+n) g_b`;
* `cell_grip`: with `a₀ = ε c H`, `Θ = ħH/2π`, `G = L_*² c³/ħ`, `ε = g/4π²`, one register per `L_*³` and the
  register grip `ħ g_b/(2πc)`, the grip of one cell is `(4π/g) ħc/L_* / C_E(x)`, `C_E = x² n(1+n)`;
* `horizon_fraction`: the density over the bulk density `3/(4 R_H L_*²)` of horizon nats is
  `(2/3) ε² x⁴ n(1+n)`;
* `x4_einstein_le`: `x⁴ n(1+n) ≤ 24` for `x > 0`, hence `horizon_bound`: the cells never outnumber the horizon
  nats when `ε ≤ 1/5` (`eps_le` gives `ε < 1/5` for `g ≤ 7.42`);
* `tilt_spread`: a frame with the N.8 inertia `I = għ/(2πH)` and `x = 2πω/H` has
  `(ħ/Iω)(1 + 2n) = (1 + 2n)/(εx)`, the two-polarization thermal tilt spread.

The equipartition matching of O.3 is the input. The numerical maximum `0.115` is not formalized.
-/

noncomputable section
namespace Entropic.Extensions20261119.CellDensity
open Real

/-- Bose occupation. -/
def nB (x : ℝ) : ℝ := 1 / (Real.exp x - 1)

/-- Einstein function `x² n(1+n)`. -/
def CE (x : ℝ) : ℝ := x ^ 2 * nB x * (1 + nB x)

/-- The O.3 cell density. -/
def density (gb n G Θ : ℝ) : ℝ := gb ^ 2 * n * (1 + n) / (4 * π * G * Θ)

theorem half_theta_mutual (gb n G Θ : ℝ) (hG : G ≠ 0) (hΘ : Θ ≠ 0) :
    density gb n G Θ * Θ / 2 = (n * gb) * ((1 + n) * gb) / (8 * π * G) := by
  unfold density; have := Real.pi_pos.ne'; field_simp; ring

theorem nB_pos {x : ℝ} (hx : 0 < x) : 0 < nB x := by
  unfold nB; have : 1 < Real.exp x := (by have := Real.add_one_lt_exp hx.ne'; linarith : 1 < Real.exp x); apply div_pos one_pos; linarith

/-- Grip of one cell: registers per cell `1/(𝒩 L³)` times the register grip `ħ g_b/(2πc)`. -/
theorem cell_grip (g c H ħ L x : ℝ) (hg : 0 < g) (hc : 0 < c) (hH : 0 < H) (hħ : 0 < ħ) (hL : 0 < L)
    (hx : 0 < x) :
    let ε := g / (4 * π ^ 2); let a₀ := ε * c * H; let gb := a₀ * x ^ 2
    let Θ := ħ * H / (2 * π); let G := L ^ 2 * c ^ 3 / ħ
    (1 / (density gb (nB x) G Θ * L ^ 3)) * (ħ * gb / (2 * π * c)) = (4 * π / g) * (ħ * c / L) / CE x := by
  intro ε a₀ gb Θ G
  have hn := nB_pos hx; have hp := Real.pi_pos
  simp only [density, CE, gb, a₀, ε, Θ, G]
  field_simp
  try ring

/-- Ratio of the cell density to the bulk density of horizon nats, `n_H = 3/(4 R_H L²)`, `R_H = c/H`. -/
theorem horizon_fraction (g c H ħ L x : ℝ) (hg : 0 < g) (hc : 0 < c) (hH : 0 < H) (hħ : 0 < ħ) (hL : 0 < L)
    (hx : 0 < x) :
    let ε := g / (4 * π ^ 2); let gb := ε * c * H * x ^ 2
    density gb (nB x) (L ^ 2 * c ^ 3 / ħ) (ħ * H / (2 * π)) / (3 / (4 * (c / H) * L ^ 2)) =
      (2 / 3) * ε ^ 2 * x ^ 4 * nB x * (1 + nB x) := by
  intro ε gb
  have hn := nB_pos hx; have hp := Real.pi_pos
  simp only [density, gb, ε]; field_simp

/-- `x⁴ n(1+n) ≤ 24` for every positive gap. -/
theorem x4_einstein_le {x : ℝ} (hx : 0 < x) : x ^ 4 * nB x * (1 + nB x) ≤ 24 := by
  set u := Real.exp x - 1 with hu
  have hexp : 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 ≤ Real.exp x := by
    have := Real.sum_le_exp_of_nonneg hx.le 5
    simp [Finset.sum_range_succ, Nat.factorial] at this; linarith
  have hup : x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 ≤ u := by linarith
  have hu0 : 0 < u := by have := (by have := Real.add_one_lt_exp hx.ne'; linarith : 1 < Real.exp x); linarith
  have hform : x ^ 4 * nB x * (1 + nB x) = x ^ 4 * (1 + u) / u ^ 2 := by
    simp only [nB, ← hu]; field_simp; ring
  rw [hform, div_le_iff₀ (by positivity)]
  have hx4 : 0 ≤ x ^ 4 := by positivity
  have h1 : x ≤ u := by nlinarith [sq_nonneg x, pow_pos hx 3, pow_pos hx 4]
  have h2 : x ^ 4 ≤ 24 * u := by nlinarith [sq_nonneg x, pow_pos hx 3]
  -- 24 u² - x⁴ u - x⁴ = u (24 u - x⁴) - x⁴ ≥ u (24 x) - x⁴ ... use u ≥ p(x)
  have h3 : 24 * u - x ^ 4 ≥ 24 * x := by nlinarith [pow_pos hx 2, pow_pos hx 3]
  have h4 : u * (24 * u - x ^ 4) ≥ x * (24 * x) := by nlinarith
  have h5 : x * (24 * x) ≥ x ^ 4 ∨ x ^ 2 > 24 := by
    by_cases h : x ^ 2 ≤ 24
    · left; nlinarith [sq_nonneg x]
    · right; linarith
  rcases h5 with h5 | h5
  · nlinarith
  · -- large x: u ≥ x⁴/24 ≥ x², so u (24u - x⁴) ≥ 24 u x ≥ 24 x · x² ... use u ≥ x^3/6 · x/4
    have h6 : u ≥ x ^ 4 / 24 := by nlinarith [pow_pos hx 2, pow_pos hx 3]
    have h7 : 24 * u - x ^ 4 ≥ 0 := by linarith
    nlinarith [mul_nonneg hu0.le h7, pow_pos hx 3]

theorem eps_le (g : ℝ) (hg : g ≤ 7.42) : g / (4 * π ^ 2) < 1 / 5 := by
  have hp := Real.pi_gt_d2
  have h2 : (3.14:ℝ) ^ 2 < π ^ 2 := by nlinarith
  rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- The cells never outnumber the bulk horizon nats when `0 ≤ ε ≤ 1/5`. -/
theorem horizon_bound {ε x : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 5) (hx : 0 < x) :
    (2 / 3) * ε ^ 2 * x ^ 4 * nB x * (1 + nB x) < 1 := by
  have h := x4_einstein_le hx
  have hn := nB_pos hx
  have he2 : ε ^ 2 ≤ 1 / 25 := by nlinarith
  have hpos : 0 ≤ x ^ 4 * nB x * (1 + nB x) := by positivity
  calc (2 / 3) * ε ^ 2 * x ^ 4 * nB x * (1 + nB x) = (2 / 3) * ε ^ 2 * (x ^ 4 * nB x * (1 + nB x)) := by ring
    _ ≤ (2 / 3) * (1 / 25) * 24 := by
        apply mul_le_mul (by nlinarith) h hpos (by positivity)
    _ < 1 := by norm_num

/-- Two-polarization thermal tilt spread with the N.8 inertia. -/
theorem tilt_spread (g ħ H ω n : ℝ) (hg : 0 < g) (hħ : 0 < ħ) (hH : 0 < H) (hω : 0 < ω) :
    let I := g * ħ / (2 * π * H); let x := 2 * π * ω / H; let ε := g / (4 * π ^ 2)
    ħ / (I * ω) * (1 + 2 * n) = (1 + 2 * n) / (ε * x) := by
  intro I x ε; have hp := Real.pi_pos; simp only [I, x, ε]; field_simp; ring

end Entropic.Extensions20261119.CellDensity
