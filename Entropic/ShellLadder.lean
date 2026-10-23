import Entropic.GenerationCutoff
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-! Charged-lepton shell ladder (App. I.1).

* The shell grades are exactly N ∈ {0, 1, 2}: a grade exists only if every way of
  excluding N labels leaves a nonempty reduced ensemble with nonconstant K²
  (`shell_allowed_iff`). The closure collapse that ends the ladder at three generations
  leaves N ≥ 3 undefined, so the formula 720^N (2/7)^{N²} applies on these three
  grades only.
* The coefficients come from counting: each single-label exclusion leaves
  2·P(6,4) = 720 = 6! oriented states (`shell_load`), and the singlet overlap of an
  N-shell source is N²/7 (`singlet_source_norm`).
* Zero-parameter test: the baseline obeys m₂m₀/m₁² = (2/7)², independent of the
  shell load 720 (`baseline_curvature`). With PDG/CODATA masses the measured value
  lies within 0.4% of 4/49 (`curvature_vs_data`). -/

namespace Entropic.ShellLadder
open Entropic.FiniteModel Entropic.GenerationCutoff

/-- A shell grade N exists when every N-label exclusion leaves a nonempty reduced
ensemble with nonconstant K² (positive closure variance). -/
def shellAllowed (N : ℕ) : Bool :=
  decide (N ≤ 7) &&
    (labels.sublistsLen N).all fun ex => !(tuples (reduced ex)).isEmpty && !constantK2 (reduced ex)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allowed_small : shellAllowed 0 = true ∧ shellAllowed 1 = true ∧ shellAllowed 2 = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem forbidden_3_to_7 : shellAllowed 3 = false ∧ shellAllowed 4 = false ∧
    shellAllowed 5 = false ∧ shellAllowed 6 = false ∧ shellAllowed 7 = false := by
  decide

theorem forbidden_large (N : ℕ) (h : 8 ≤ N) : shellAllowed N = false := by
  unfold shellAllowed
  have : ¬ N ≤ 7 := by omega
  simp [this]

/-- The grades are exactly {0, 1, 2}. -/
theorem shell_allowed_iff (N : ℕ) : shellAllowed N = true ↔ N ≤ 2 := by
  obtain ⟨h0, h1, h2⟩ := allowed_small
  obtain ⟨h3, h4, h5, h6, h7⟩ := forbidden_3_to_7
  constructor
  · intro h
    by_contra hN
    push_neg at hN
    rcases le_or_gt 8 N with hbig | hsmall
    · rw [forbidden_large N hbig] at h; exact absurd h (by decide)
    · interval_cases N <;> simp_all
  · intro h
    interval_cases N <;> assumption

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Shell load: every single-label exclusion leaves 2·P(6,4) = 720 oriented states. -/
theorem shell_load : (labels.sublistsLen 1).all (fun ex => 2 * (tuples (reduced ex)).length == 720) = true ∧
    720 = Nat.factorial 6 := by
  refine ⟨by decide, by decide⟩

/-- Singlet projector on the seven labels: ⟨a|P|b⟩ = 1/7 for all a, b; an N-shell
source J = Σ_r |a_r⟩ has ⟨J|P|J⟩ = N²/7 (any labels). -/
theorem singlet_source_norm (N : ℕ) :
    (∑ _r : Fin N, ∑ _s : Fin N, (1 / 7 : ℚ)) = (N : ℚ) ^ 2 / 7 := by
  simp [Finset.sum_const, Finset.card_univ]; ring

/-- Baseline ladder m_N/m_e = Ω^N q^{N²}. -/
def ladder (Ω q : ℚ) (N : ℕ) : ℚ := Ω ^ N * q ^ (N ^ 2)

/-- Zero-parameter curvature: m₂ m₀ / m₁² = q², independent of the shell load Ω. -/
theorem baseline_curvature (Ω q : ℚ) (hΩ : Ω ≠ 0) (hq : q ≠ 0) :
    ladder Ω q 2 * ladder Ω q 0 / ladder Ω q 1 ^ 2 = q ^ 2 := by
  unfold ladder; field_simp <;> ring

/-- Against data (m_μ/m_e = 206.7682827 CODATA 2022; m_τ = 1776.93 MeV, m_e = 0.51099895 MeV):
m_τ m_e/m_μ² lies within 0.4% of (2/7)² = 4/49. -/
theorem curvature_vs_data :
    let mt : ℚ := 1776.93 / 0.51099895
    let mm : ℚ := 206.7682827
    |mt / mm ^ 2 - 4 / 49| / (4 / 49) < 0.004 := by
  norm_num [abs_of_neg, abs_of_pos]

end Entropic.ShellLadder
