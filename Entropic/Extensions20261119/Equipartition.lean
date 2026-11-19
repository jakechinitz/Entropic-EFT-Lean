import Mathlib

/-!
# Equipartition over the tilt polarizations (Appendices N.8, O.3; Section 20)

A response cell carries `m` degenerate tilt polarizations, `q` baryonic field units per quantum, and the O.3
matching coefficient `λ`. With `n` the Bose occupation of each polarization, the O.3 matching gives the mean
mutual field energy per cell `E = Θ (1 + q m n)/(2 q λ (1 + n))`. This file proves:

* `cell_energy`: that expression from `𝒩 = λ g_b² q² m n(1+n)/(4πGΘ)`, `g_R = q m n g_b`, `g_obs = (1 + q m n) g_b`;
* `equipartition_iff`: `E = m Θ/2` for every `n > 0` if and only if `λ = 1` and `q m = 1`;
* `mean_response`: with `q m = 1` the mean response is `1 + n`, the exponential law;
* `displaced_nat_mass`: a mass `M` with `2π M c R/ħ` displaced nats has `ħ/(2π c R)` per nat, the N.8 horizon nat;
* `holographic_equipartition`: `n_nat k_B T_U = g²/(4πG)` with `n_nat = (2g/c²)/(4 L_*²)`,
  `k_B T_U = ħ g/(2π c)`, `G = L_*² c³/ħ`.

The equipartition identification itself is the physical input; the abundance and galaxy measurements are not
formalized.
-/

noncomputable section
namespace Entropic.Extensions20261119.Equipartition
open Real

/-- Mean mutual field energy per cell. -/
def cellEnergy (Θ q m lam n : ℝ) : ℝ := Θ * (1 + q * m * n) / (2 * q * lam * (1 + n))

theorem cell_energy (Θ q m lam n gb G : ℝ) (hΘ : 0 < Θ) (hq : 0 < q) (hm : 0 < m) (hl : 0 < lam)
    (hn : 0 < n) (hg : 0 < gb) (hG : 0 < G) :
    (q * m * n * gb) * ((1 + q * m * n) * gb) / (8 * π * G * (lam * gb ^ 2 * q ^ 2 * m * n * (1 + n) / (4 * π * G * Θ)))
      = cellEnergy Θ q m lam n := by
  unfold cellEnergy
  have hπ : 0 < π := Real.pi_pos
  field_simp
  ring

theorem equipartition_iff (Θ q m lam : ℝ) (hΘ : 0 < Θ) (hq : 0 < q) (hm : 0 < m) (hl : 0 < lam) :
    (∀ n : ℝ, 0 < n → cellEnergy Θ q m lam n = m * Θ / 2) ↔ (lam = 1 ∧ q * m = 1) := by
  have key : ∀ n : ℝ, 0 < n → (cellEnergy Θ q m lam n = m * Θ / 2 ↔ 1 + q * m * n = lam * q * m * (1 + n)) := by
    intro n hn
    unfold cellEnergy
    have h1 : (0:ℝ) < 2 * q * lam * (1 + n) := by positivity
    rw [div_eq_iff h1.ne']
    constructor
    · intro h
      have : Θ * (1 + q * m * n) = Θ * (lam * q * m * (1 + n)) := by linarith
      exact mul_left_cancel₀ hΘ.ne' this
    · intro h
      rw [h]; ring
  constructor
  · intro h
    have e1 := (key 1 one_pos).1 (h 1 one_pos)
    have e2 := (key 2 two_pos).1 (h 2 two_pos)
    have hqm : 0 < q * m := mul_pos hq hm
    have hl1 : lam = 1 := by
      have : q * m = lam * q * m := by linarith
      have : q * m * 1 = q * m * lam := by linarith
      exact (mul_left_cancel₀ hqm.ne' this).symm
    refine ⟨hl1, ?_⟩
    rw [hl1] at e1; linarith
  · rintro ⟨hl1, hqm⟩ n hn
    apply (key n hn).2
    rw [hl1]
    have : q * m * n = n := by rw [hqm]; ring
    nlinarith [hqm]

theorem mean_response (q m n : ℝ) (h : q * m = 1) : 1 + q * m * n = 1 + n := by rw [h]; ring

theorem displaced_nat_mass (M c R ħ : ℝ) (hM : 0 < M) (hc : 0 < c) (hR : 0 < R) (hħ : 0 < ħ) :
    M / (2 * π * M * c * R / ħ) = ħ / (2 * π * c * R) := by
  have hπ : 0 < π := Real.pi_pos
  field_simp

theorem holographic_equipartition (g c L ħ : ℝ) (hc : 0 < c) (hL : 0 < L) (hħ : 0 < ħ) :
    ((2 * g / c ^ 2) / (4 * L ^ 2)) * (ħ * g / (2 * π * c)) = g ^ 2 / (4 * π * (L ^ 2 * c ^ 3 / ħ)) := by
  have hπ : 0 < π := Real.pi_pos
  field_simp

end Entropic.Extensions20261119.Equipartition
