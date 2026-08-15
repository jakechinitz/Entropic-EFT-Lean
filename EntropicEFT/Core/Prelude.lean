import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.Pow

/-!
# EntropicEFT.Core.Prelude

LOCAL CONTRACT
* Manuscript: Appendix A; shared notation only.
* Status: mathematical infrastructure, not a physical claim.
* Assumes: Mathlib.
* Proves: tiny algebraic definitions used across sectors.
* Does not prove: any substrate ontology, continuum limit, or empirical statement.
* Downstream: every module may import this file.

DESIGN RULE
Physical premises are never global `axiom`s.  A conditional physical statement is
represented by an explicit structure or a theorem parameter.  Open completions are
uninhabited interfaces, not `sorry`s.
-/

open scoped BigOperators

namespace EntropicEFT

/-- Rational enclosure for a real quantity; used instead of floating-point theorem claims. -/
structure RatInterval (x : ℝ) where
  lo : ℚ
  hi : ℚ
  lo_lt : (lo : ℝ) < x
  lt_hi : x < (hi : ℝ)

/-- The induced gravitational scale associated with a substrate length. -/
noncomputable def inducedG (c hbar L : ℝ) : ℝ := c^3 * L^2 / hbar

/-- Weak-field capacity-to-potential coordinate map. -/
noncomputable def potentialFromDeficit (c SInf deltaS : ℝ) : ℝ :=
  -c^2 * deltaS / (2 * SInf)

/-- Bounded static occupancy coordinate. -/
noncomputable def capacityFraction (SInf deltaS : ℝ) : ℝ := 1 - deltaS / SInf

/-- A named equality whose physical interpretation is conditional. -/
structure Bridge (α β : Type*) where
  map : α → β
  statement : String

/-- A predicate for an explicitly adopted model branch. -/
structure ModelPremise where
  id : String
  statement : String

end EntropicEFT
