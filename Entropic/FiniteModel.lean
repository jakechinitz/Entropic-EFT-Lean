import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Finite boundary ensemble, main manuscript pp. 104–105.
The physical choice of seven labels, four distinguishable ports, no repeated
labels and two orientations is INPUT. The enumeration is kernel checked.
No numerical fixed point is asserted as an exact real number. -/

namespace Entropic.FiniteModel

def labels : List Int := [-3, -2, -1, 0, 1, 2, 3]
abbrev FaceState := Int × Int × Int × Int

def states : List FaceState :=
  labels.flatMap fun a => labels.flatMap fun b =>
    labels.flatMap fun c => labels.filterMap fun d =>
      if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d
      then some (a, b, c, d) else none

/-- Integer-valued 3K²; this avoids rounding and rational evaluation. -/
def threeK2 (s : FaceState) : Int :=
  let (a, b, c, d) := s
  144 - ((a + b + c + d) ^ 2 - (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2))

def levels : List Int := [122, 134, 142, 146, 152, 154, 158, 162, 164, 166, 170]

def spectrum : List (Int × Nat) :=
  levels.map fun k => (k, 2 * (states.filter fun s => threeK2 s == k).length)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem unoriented_count : states.length = 840 := by decide

theorem oriented_count : 2 * states.length = 1680 := by rw [unoriented_count]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem exact_spectrum : spectrum =
    [(122, 96), (134, 96), (142, 96), (146, 288), (152, 192), (154, 144),
     (158, 384), (162, 192), (164, 48), (166, 96), (170, 48)] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem spectral_bounds :
    (states.map threeK2).all (fun k => decide (122 ≤ k ∧ k ≤ 170)) = true := by
  decide

theorem total_multiplicity : (spectrum.map Prod.snd).sum = 1680 := by
  rw [exact_spectrum]
  decide

/-- The two polynomial forms of the closure invariant agree. -/
theorem closure_polynomial (a b c d : ℝ) :
    48 - ((a+b+c+d)^2 - (a^2+b^2+c^2+d^2)) / 3 =
      48 - (2/3 : ℝ) * (a*b+a*c+a*d+b*c+b*d+c*d) := by ring

noncomputable section

def partition (eta : ℝ) : ℝ :=
  (spectrum.map fun kn => (kn.2 : ℝ) * Real.exp (-eta * (kn.1 : ℝ) / 3)).sum

def meanK2 (eta : ℝ) : ℝ :=
  (spectrum.map fun kn =>
    (kn.2 : ℝ) * ((kn.1 : ℝ) / 3) * Real.exp (-eta * (kn.1 : ℝ) / 3)).sum /
      partition eta

/-- A statement of the paper's stationary condition; existence, uniqueness
and the decimal value of eta are NOT claimed to be proved by this definition. -/
def ClosureStationary (eta : ℝ) : Prop := 0 < eta ∧ meanK2 eta = 3 / (2 * eta)

end
end Entropic.FiniteModel
