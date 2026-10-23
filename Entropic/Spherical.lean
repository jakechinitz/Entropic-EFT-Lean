import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Spherical response and a positivity test

Source: main manuscript pp. 34–36 and 276. `x` is the dimensionless
sqrt(g_b/a_0), restricted to x > 0; no pointwise disk approximation is made.
These are conditional mathematical consequences of the displayed spherical law.
-/

noncomputable section
namespace Entropic.Spherical

def occupation (x : ℝ) : ℝ := 1 / (Real.exp x - 1)

def acceleration (a₀ x : ℝ) : ℝ := a₀ * x ^ 2 / (1 - Real.exp (-x))

def excessMass (M x : ℝ) : ℝ := M / (Real.exp x - 1)

theorem exp_sub_one_pos {x : ℝ} (hx : 0 < x) : 0 < Real.exp x - 1 := by
  have h := Real.exp_lt_exp.mpr hx
  rw [Real.exp_zero] at h
  linarith

/-- The two expressions in the manuscript's spherical acceleration law agree. -/
theorem acceleration_eq_thermal {a₀ x : ℝ} (hx : 0 < x) :
    acceleration a₀ x = a₀ * x ^ 2 * (1 + occupation x) := by
  have he : Real.exp x ≠ 0 := ne_of_gt (Real.exp_pos x)
  have hd : Real.exp x - 1 ≠ 0 := ne_of_gt (exp_sub_one_pos hx)
  unfold acceleration occupation
  rw [Real.exp_neg]
  field_simp
  ring

/-- The spherical excess is positive as an enclosed mass, for positive inputs.
This does not establish positivity of its radial derivative. -/
theorem excessMass_pos {M x : ℝ} (hM : 0 < M) (hx : 0 < x) :
    0 < excessMass M x :=
  div_pos hM (exp_sub_one_pos hx)

/-- A uniform-density baryonic core in scaled coordinates r = x² has
M_b = A x⁶. The constant A absorbs the positive dimensional conversion. -/
def coreExcessMass (A x : ℝ) : ℝ := excessMass (A * x ^ 6) x

def coreSlope (A x : ℝ) : ℝ :=
  A * x ^ 5 * (6 * (Real.exp x - 1) - x * Real.exp x) /
    (Real.exp x - 1) ^ 2

/-- This derivative is proved from the exponential formula, not postulated. -/
theorem core_hasDerivAt {A x : ℝ} (hx : 0 < x) :
    HasDerivAt (coreExcessMass A) (coreSlope A x) x := by
  have hd : Real.exp x - 1 ≠ 0 := ne_of_gt (exp_sub_one_pos hx)
  have h := ((hasDerivAt_pow 6 x).const_mul A).fun_div
    ((Real.hasDerivAt_exp x).sub_const 1) hd
  convert h using 1
  · funext y; simp only [coreExcessMass, excessMass]
  · simp only [coreSlope]; field_simp; ring

/-- x >= 6 is an exact sufficient condition; no decimal root is trusted. -/
theorem coreSlope_neg {A x : ℝ} (hA : 0 < A) (hx : 6 ≤ x) :
    coreSlope A x < 0 := by
  have hx0 : 0 < x := by linarith
  have hexp := Real.exp_pos x
  have hnum : 6 * (Real.exp x - 1) - x * Real.exp x < 0 := by
    nlinarith
  have hpre : 0 < A * x ^ 5 := mul_pos hA (pow_pos hx0 5)
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hpre hnum)
    (pow_pos (exp_sub_one_pos hx0) 2)

theorem core_deriv_neg {A x : ℝ} (hA : 0 < A) (hx : 6 ≤ x) :
    deriv (coreExcessMass A) x < 0 := by
  rw [(core_hasDerivAt (by linarith : 0 < x)).deriv]
  exact coreSlope_neg hA hx

/-- Conditional incompatibility: a stock with nonnegative enclosed-mass
derivative cannot have this exact enclosed-mass profile at x >= 6.
The equality identifying the physical stock with the spherical excess is
explicit. The theorem does not prohibit signed effective/phantom densities. -/
theorem no_nonnegative_stock_matching_core
    {A x : ℝ} (hA : 0 < A) (hx : 6 ≤ x) (stock : ℝ → ℝ)
    (hmatch : stock = coreExcessMass A)
    (hpositive : 0 ≤ deriv stock x) : False := by
  rw [hmatch] at hpositive
  exact (not_le_of_gt (core_deriv_neg hA hx)) hpositive

end Entropic.Spherical
