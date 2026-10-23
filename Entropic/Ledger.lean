import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Scalar components of the source ledger, main manuscript pp. 53, 275–278.
The covariant action and its variation are not proved here. -/

noncomputable section
namespace Entropic.Ledger

def sourceCurrent (q : ℝ) : ℝ := -q
def reallocatedCurrent (q Q : ℝ) : ℝ := q - Q
def vacuumCurrent (Q : ℝ) : ℝ := Q

theorem exchange_conserves (q Q : ℝ) :
    sourceCurrent q + reallocatedCurrent q Q + vacuumCurrent Q = 0 := by
  unfold sourceCurrent reallocatedCurrent vacuumCurrent
  ring

/-- The total capacity continuity equation at a point, with expansion theta.
No field equation or positivity is hidden in this definition. -/
def Continuity (rho rhoDot theta Q : ℝ) : Prop :=
  rhoDot + theta * rho = -Q

theorem vacuum_boundary_points_outward {rhoDot theta Q : ℝ}
    (hQ : 0 < Q) (h : Continuity 0 rhoDot theta Q) : rhoDot < 0 := by
  unfold Continuity at h
  nlinarith

/-- A nonexpanding exact solution with a constant positive drain. This is
a counterexample to positivity preservation by the continuity equation alone;
it is not a claimed solution of the full cosmological model. -/
def constantDrain (rho₀ Q t : ℝ) : ℝ := rho₀ - Q * t

theorem constantDrain_hasDerivAt (rho₀ Q t : ℝ) :
    HasDerivAt (constantDrain rho₀ Q) (-Q) t := by
  unfold constantDrain
  convert ((hasDerivAt_id t).const_mul Q).const_sub rho₀ using 1 <;> simp

theorem constantDrain_solves (rho₀ Q t : ℝ) :
    Continuity (constantDrain rho₀ Q t) (deriv (constantDrain rho₀ Q) t) 0 Q := by
  rw [(constantDrain_hasDerivAt rho₀ Q t).deriv]
  simp [Continuity]

theorem constantDrain_negative {rho₀ Q t : ℝ} (hQ : 0 < Q)
    (ht : rho₀ / Q < t) : constantDrain rho₀ Q t < 0 := by
  have h := (div_lt_iff₀ hQ).mp ht
  unfold constantDrain
  nlinarith

/-- Fully concrete positive-initial-stock counterexample for the reduced
continuity equation, in arbitrary consistent scaled units. -/
theorem constantDrain_counterexample :
    0 < constantDrain 1 1 0 ∧
    (∀ t : ℝ, Continuity (constantDrain 1 1 t)
      (deriv (constantDrain 1 1) t) 0 1) ∧
    constantDrain 1 1 2 < 0 := by
  refine ⟨?_, constantDrain_solves 1 1, ?_⟩ <;> norm_num [constantDrain]

/-- The manuscript's homogeneous branch does have a separate positivity
bound, assuming the released fraction and efficiency stay in [0,1]. -/
def backgroundStock (B a eta F : ℝ) : ℝ := B / a ^ 3 * (1 - eta * F)

theorem backgroundStock_nonnegative {B a eta F : ℝ}
    (hB : 0 ≤ B) (ha : 0 < a)
    (he0 : 0 ≤ eta) (he1 : eta ≤ 1) (_hF0 : 0 ≤ F) (hF1 : F ≤ 1) :
    0 ≤ backgroundStock B a eta F := by
  have hef : eta * F ≤ 1 := by nlinarith
  exact mul_nonneg (div_nonneg hB (le_of_lt (pow_pos ha 3))) (by linarith)

/-- Bare, pre-release abundance identity. Mass-convention conversion is not
silently equated to one: the next theorem keeps that factor explicit. -/
theorem bare_acceleration_abundance (eps c H : ℝ) (heps : eps ≠ 0) :
    (eps * c * H) * (1 / eps) = c * H := by
  field_simp <;> ring

theorem converted_depleted_identity (eps c H conversion eta F : ℝ)
    (heps : eps ≠ 0) :
    (eps * c * H) * (conversion / eps * (1 - eta * F)) =
      c * H * conversion * (1 - eta * F) := by
  field_simp <;> ring

/-- An effective w inferred by treating the growing vacuum separately as
conserved. numerator denotes a^-3 dF/dln a; integral denotes the positive
accumulated release integral. This does not formalize a fitted CPL w0,wa. -/
def effectiveW (numerator integral : ℝ) : ℝ := -1 - numerator / (3 * integral)

theorem active_release_effectiveW_lt_neg_one {n I : ℝ} (hn : 0 < n) (hI : 0 < I) :
    effectiveW n I < -1 := by
  have h := div_pos hn (mul_pos (by norm_num : (0 : ℝ) < 3) hI)
  unfold effectiveW
  linarith

end Entropic.Ledger
