import Mathlib

/-!
# The O.3 cell count as a register state count, and one-cell means at fixed marginals (Appendices O.3, N.8)

* `register_state_count`: with the N.8 register inertia `I = g ħ/(2π H)` and `k_B T_H = ħ H/(2π)`,
  `I k_B T_H/ħ² = g/(4π²) = ε`, the classical orientation count of one headless register at `T_H`.
* `field_energy_count`: the energy density `g_b²/(8πG)` of the baryonic field in units of the register grip
  `k_B T_U = ħ g_b/(2πc)` is half the displaced-nat density `n_nat = g_b c/(2Għ)`.
* `cell_density_count`: hence the O.3 density `ε n_nat C` equals `2 [u_b/(k_B T_U)] [I k_B T_H/ħ²] C` for any
  factor `C` (the Einstein function `C_E(x)` in the manuscript).
* `one_cell_mean`: for any joint law `P` of `N` cells whose one-cell marginals all equal `p`, the mean of a sum of
  one-cell observables is `N` times the one-cell mean, whatever the correlations. With the one-cell state held fixed,
  the derivative `∂F/∂q = ⟨Σ_i h_i⟩` of a field term `q Σ_i h_i` therefore does not depend on `q`. This is the classical
  finite form of the statement in N.8; the quantum trace form and the vanishing of the thermal response that follows
  from it are stated in the manuscript and not formalized here.

The identification of the count with a number of states holds for frames of many registers; the exact count for one
register (one accessible state) and the 1% threshold near a hundred registers are numerical
(02 Research/UV origin of carrier and thermal matching 2026-11-19, EPS_AS_A_STATE_COUNT_2026-11-20).
-/

noncomputable section
namespace Entropic.Extensions20261120.CellCount
open Real

theorem register_state_count (g ħ H : ℝ) (hħ : 0 < ħ) (hH : 0 < H) :
    (g * ħ / (2 * π * H)) * (ħ * H / (2 * π)) / ħ ^ 2 = g / (4 * π ^ 2) := by
  have hπ : 0 < π := Real.pi_pos
  field_simp
  try ring

theorem field_energy_count (gb G ħ c : ℝ) (hg : 0 < gb) (hG : 0 < G) (hħ : 0 < ħ) (hc : 0 < c) :
    (gb ^ 2 / (8 * π * G)) / (ħ * gb / (2 * π * c)) = (gb * c / (2 * G * ħ)) / 2 := by
  have hπ : 0 < π := Real.pi_pos
  field_simp
  try ring

theorem cell_density_count (g gb G ħ c H C : ℝ) (hg : 0 < gb) (hG : 0 < G) (hħ : 0 < ħ) (hc : 0 < c)
    (hH : 0 < H) :
    (g / (4 * π ^ 2)) * (gb * c / (2 * G * ħ)) * C =
      2 * ((gb ^ 2 / (8 * π * G)) / (ħ * gb / (2 * π * c))) *
        ((g * ħ / (2 * π * H)) * (ħ * H / (2 * π)) / ħ ^ 2) * C := by
  rw [field_energy_count gb G ħ c hg hG hħ hc, register_state_count g ħ H hħ hH]
  ring

theorem one_cell_mean {S : Type*} [Fintype S] [DecidableEq S] {N : ℕ}
    (P : (Fin N → S) → ℝ) (p h : S → ℝ)
    (hmarg : ∀ (i : Fin N) (s : S), ∑ x : Fin N → S, (if x i = s then P x else 0) = p s) :
    ∑ x : Fin N → S, P x * ∑ i : Fin N, h (x i) = N * ∑ s, p s * h s := by
  have key : ∀ i : Fin N, ∑ x : Fin N → S, P x * h (x i) = ∑ s, p s * h s := by
    intro i
    have hx : ∀ x : Fin N → S, P x * h (x i) = ∑ s, (if x i = s then P x else 0) * h s := by
      intro x
      simp [ite_mul]
    simp_rw [hx]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [← Finset.sum_mul, hmarg i s]
  calc ∑ x : Fin N → S, P x * ∑ i : Fin N, h (x i)
        = ∑ x : Fin N → S, ∑ i : Fin N, P x * h (x i) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [Finset.mul_sum]
    _ = ∑ i : Fin N, ∑ x : Fin N → S, P x * h (x i) := Finset.sum_comm
    _ = ∑ _i : Fin N, ∑ s, p s * h s := Finset.sum_congr rfl (fun i _ => key i)
    _ = N * ∑ s, p s * h s := by simp

end Entropic.Extensions20261120.CellCount
