import Mathlib
import Entropic.GalacticLaw

/-!
# The response-cell gap as a horizon-thermal tilt mode (Section 15, Appendix N.8)

The galactic response cell is the small-oscillation tilt mode of the transverse carrier frame. The
projected baryonic field is its restoring stiffness and its inertia lever is `ℓ = g_s c / H`
(`g_s = g_share,eff`). For `U(θ) = M g ℓ (1 − cos θ)` and kinetic term `½ M ℓ² θ̇²` the frequency obeys
`ω² = g/ℓ` (`tilt_stiffness`, `tilt_frequency_sq`). Populated by the apparent-horizon bath at
`T_H = ħ H / (2π k_B)`, the gap is `x = ħω/(k_B T_H) = 2π ω / H` (`ħ`, `k_B` cancel), and
* `x² = g / a₀` with `a₀ = g_s c H / 4π²` (`gap_sq`), so `x = √(g/a₀)` (`gap_eq`);
* `x = 1` exactly at `g = a₀` (`unit_gap_iff`);
* in the projected field `g cos δ` the gap is `x √(cos δ)`, the director-completion gap (`gap_tilt`);
* `g·n_B(x)` lies between `√(g a₀) − g/2` and `√(g a₀)` (`excess_bounds`): the deep regime is the
  Rayleigh–Jeans (equipartition) limit of the mode;
* `a₀ · (4π²/g_s) = c H` (`a0_times_abundance`).
The matching inputs (identification of the cell with this mode, its horizon thermalization, and the lever
`ℓ = g_s c / H`) are not derived here; `gap` is defined as `2π ω / H`, so `ħω/(k_B T_H) = 2πω/H` is a definition.
-/

noncomputable section
open Real

namespace Entropic.RAR

/-- **Tilt mode in a field.** For the potential `U(θ) = M g ℓ (1 - cos θ)` and kinetic term `½ M ℓ² θ̇²`,
the small-oscillation stiffness is `U''(0) = M g ℓ`, so `ω² = U''(0)/(M ℓ²) = g/ℓ`: the field is the stiffness,
the lever sets the inertia. -/
theorem tilt_stiffness (M g ℓ : ℝ) :
    deriv (deriv (fun θ : ℝ => M * g * ℓ * (1 - cos θ))) 0 = M * g * ℓ := by
  have h1 : deriv (fun θ : ℝ => M * g * ℓ * (1 - cos θ)) = fun θ => M * g * ℓ * sin θ := by
    funext θ
    have := ((hasDerivAt_cos θ).const_sub 1).const_mul (M * g * ℓ)
    rw [this.deriv]; ring
  rw [h1]
  have := (hasDerivAt_sin (0:ℝ)).const_mul (M * g * ℓ)
  rw [this.deriv, cos_zero, mul_one]

theorem tilt_frequency_sq {M g ℓ : ℝ} (hM : M ≠ 0) (hℓ : ℓ ≠ 0) :
    deriv (deriv (fun θ : ℝ => M * g * ℓ * (1 - cos θ))) 0 / (M * ℓ ^ 2) = g / ℓ := by
  rw [tilt_stiffness]; field_simp

/-- Horizon-thermal gap of the pendular mode: `x = 2π ω / H` with `ω = √(g/ℓ)`. -/
def gap (g ℓ H : ℝ) : ℝ := 2 * π * Real.sqrt (g / ℓ) / H

/-- The acceleration scale implied by the lever `ℓ = g_s c / H`. -/
def a0 (gs c H : ℝ) : ℝ := gs * c * H / (4 * π ^ 2)

/-- **Pure-number lever.** With `ℓ = κ c / H` the gap is `x = √(g / a₀)` with `a₀ = κ c H / 4π²` for any `κ > 0`
(`gap_sq`). This identity is the algebra behind `a₀ · (Ω_c/Ω_b) = c H` when the abundance reads `Ω_c/Ω_b = 4π²/κ`;
that reading is a separate premise and is not proved here. -/
theorem a0_times_abundance {κ c H : ℝ} (hκ : 0 < κ) :
    a0 κ c H * (4 * π ^ 2 / κ) = c * H := by
  unfold a0; field_simp

/-- **Projected field.** In a field tilted by `δ` from the director the pendular gap is `x √(cos δ)`;
this is the director-completion gap `x̃ = √(ê·∇Φ_b / a₀)` of Section 15. -/
theorem gap_tilt {g ℓ H δ : ℝ} (hc : 0 ≤ cos δ) :
    gap (g * cos δ) ℓ H = gap g ℓ H * Real.sqrt (cos δ) := by
  unfold gap
  rw [show g * cos δ / ℓ = g / ℓ * cos δ by ring, Real.sqrt_mul' _ hc]
  ring

theorem gap_sq {g gs c H : ℝ} (hg : 0 ≤ g) (hgs : 0 < gs) (hc : 0 < c) (hH : 0 < H) :
    gap g (gs * c / H) H ^ 2 = g / a0 gs c H := by
  have hl : 0 < gs * c / H := by positivity
  unfold gap a0
  rw [div_pow, mul_pow, Real.sq_sqrt (div_nonneg hg hl.le)]
  field_simp
  ring

theorem gap_eq {g gs c H : ℝ} (hg : 0 ≤ g) (hgs : 0 < gs) (hc : 0 < c) (hH : 0 < H) :
    gap g (gs * c / H) H = Real.sqrt (g / a0 gs c H) := by
  have h0 : 0 ≤ gap g (gs * c / H) H := by unfold gap; positivity
  rw [← gap_sq hg hgs hc hH, Real.sqrt_sq h0]

theorem unit_gap_iff {g gs c H : ℝ} (hg : 0 ≤ g) (hgs : 0 < gs) (hc : 0 < c) (hH : 0 < H) :
    gap g (gs * c / H) H = 1 ↔ g = a0 gs c H := by
  have ha : 0 < a0 gs c H := by unfold a0; positivity
  rw [gap_eq hg hgs hc hH]
  constructor
  · intro h
    have h2 := congrArg (· ^ 2) h
    rw [Real.sq_sqrt (div_nonneg hg ha.le), one_pow] at h2
    field_simp at h2; linarith
  · intro h; rw [h, div_self ha.ne', Real.sqrt_one]

/-- Bose occupation. -/
def nB (x : ℝ) : ℝ := 1 / (exp x - 1)

/-- `1/x - 1/2 ≤ n_B(x) ≤ 1/x` for `x > 0`. -/
theorem nB_bounds {x : ℝ} (hx : 0 < x) : 1 / x - 1 / 2 ≤ nB x ∧ nB x ≤ 1 / x := by
  have hex : 0 < exp x - 1 := by have := Real.add_one_lt_exp hx.ne'; linarith
  unfold nB
  constructor
  · have key : (2 - x) * exp x ≤ 2 + x := Entropic.GalacticLaw.lower_core hx.le
    rw [div_sub_div _ _ hx.ne' (by norm_num : (2:ℝ) ≠ 0), div_le_div_iff₀ (by positivity) hex]
    nlinarith
  · rw [div_le_div_iff₀ hex hx]; have := Real.add_one_le_exp x; linarith

/-- The excess field `g n_B(√(g/a₀))` lies between `√(g a₀) − g/2` and `√(g a₀)`. -/
theorem excess_bounds {g a : ℝ} (hg : 0 < g) (ha : 0 < a) :
    Real.sqrt (g * a) - g / 2 ≤ g * nB (Real.sqrt (g / a)) ∧ g * nB (Real.sqrt (g / a)) ≤ Real.sqrt (g * a) := by
  have hx : 0 < Real.sqrt (g / a) := Real.sqrt_pos.mpr (div_pos hg ha)
  obtain ⟨h1, h2⟩ := nB_bounds hx
  have key : g * (1 / Real.sqrt (g / a)) = Real.sqrt (g * a) := by
    have hsg : 0 < Real.sqrt g := Real.sqrt_pos.mpr hg
    rw [Real.sqrt_div hg.le, one_div_div, Real.sqrt_mul hg.le]
    calc g * (Real.sqrt a / Real.sqrt g)
        = (Real.sqrt g * Real.sqrt g) * Real.sqrt a / Real.sqrt g := by rw [Real.mul_self_sqrt hg.le]; ring
      _ = Real.sqrt g * Real.sqrt a := by field_simp
  constructor
  · have := mul_le_mul_of_nonneg_left h1 hg.le; rw [mul_sub, key] at this; linarith
  · have := mul_le_mul_of_nonneg_left h2 hg.le; rwa [key] at this

/-- **The local director tilt is frozen.** A relativistic frame term `Z_θ[(∂_t ê)²/c² − (∇ê)²]` against the
restoring density of Section 15 gives the uniform tilt `ω = c/ξ_θ` (`ξ_θ` the coherence length). Its horizon gap
`2π (c/ξ_θ)/H` exceeds one whenever `ξ_θ < 2π c/H`, i.e. for every galactic coherence length. -/
theorem local_mode_frozen {c H ξ : ℝ} (hH : 0 < H) (hξ : 0 < ξ) (h : ξ * H < 2 * π * c) :
    1 < 2 * π * (c / ξ) / H := by
  rw [lt_div_iff₀ hH, one_mul, mul_div_assoc', lt_div_iff₀ hξ]; linarith

/-- **Coherence length of the cell.** A tilt mode with `ω = c/ξ` has the cell gap `gap g ℓ H` exactly when
`ξ² = c² ℓ / g`: the cell is coherent over the geometric mean of the lever and `c²/g`. -/
theorem coherence_length {g ℓ c ξ H : ℝ} (hg : 0 < g) (hℓ : 0 < ℓ) (hc : 0 < c) (hξ : 0 < ξ)
    (h : ξ ^ 2 = c ^ 2 * ℓ / g) :
    2 * π * (c / ξ) / H = gap g ℓ H := by
  unfold gap
  have e : g / ℓ = (c / ξ) ^ 2 := by
    rw [div_pow, h]; field_simp
  rw [e, Real.sqrt_sq (div_pos hc hξ).le]

/-- **Unruh form.** With `ℓ = κ c/H`, `x² = (2π)² (g/c) / (κ H)`: the squared gap is `(2π)²/κ` times the ratio of
the Unruh rate `g/c` of the baryonic field to the Hubble rate. -/
theorem gap_unruh {g κ c H : ℝ} (hg : 0 ≤ g) (hκ : 0 < κ) (hc : 0 < c) (hH : 0 < H) :
    gap g (κ * c / H) H ^ 2 = (2 * π) ^ 2 * (g / c) / (κ * H) := by
  rw [gap_sq hg hκ hc hH]; unfold a0; field_simp; ring

end Entropic.RAR
