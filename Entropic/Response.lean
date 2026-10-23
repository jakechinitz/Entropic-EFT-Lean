import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Algebraic checks on the response formulas (p. 265) and the homogeneous
release prescription (p. 274). These are NOT a formalization of quantum KMS
theory, spacetime causality, or an observational likelihood. -/

noncomputable section
namespace Entropic.Response

def noise (gamma n omega : ℝ) : ℝ :=
  2 * gamma * n * (1 + n) / (omega ^ 2 + gamma ^ 2)

/-- Minus the imaginary part of the susceptibility, for the sign convention
printed in the manuscript. -/
def dissipativePart (beta gamma n omega : ℝ) : ℝ :=
  beta * n * (1 + n) * gamma * omega / (gamma ^ 2 + omega ^ 2)

/-- The printed noise and susceptibility satisfy the classical FDT factor.
This alone neither proves nor disproves the full finite-frequency quantum FDT. -/
theorem classical_fdt_identity (beta gamma n omega : ℝ)
    (hb : beta ≠ 0) (hw : omega ≠ 0) :
    noise gamma n omega = (2 / (beta * omega)) *
      dissipativePart beta gamma n omega := by
  have hd : omega ^ 2 + gamma ^ 2 ≠ 0 := by nlinarith [sq_pos_of_ne_zero hw]
  have hd' : gamma ^ 2 + omega ^ 2 ≠ 0 := by nlinarith [sq_pos_of_ne_zero hw]
  unfold noise dissipativePart
  field_simp <;> ring

/-- A two-region abstraction of same-slice spatial averaging, not a derivation
of the manuscript's metric volume measure. -/
def averagedRelease (eta q₁ q₂ : ℝ) : ℝ := eta * ((q₁ + q₂) / 2)

theorem remote_region_changes_average (eta q₁ q₂ delta : ℝ) :
    averagedRelease eta q₁ (q₂ + delta) - averagedRelease eta q₁ q₂ =
      eta * delta / 2 := by
  unfold averagedRelease
  ring

end Entropic.Response
