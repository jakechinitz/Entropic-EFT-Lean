import Entropic.FiniteModel
import Mathlib.Data.List.Sublists

/-! Alphabet-independent generation cutoff (main manuscript App. K, "The generation
cutoff has also been checked without choosing a preferred excluded alphabet").
Removing one or two labels from the seven-label alphabet always leaves a
nonconstant closure functional K²; removing any three labels makes it constant
(zero closure variance). The enumeration is kernel checked with `decide`.
The physical reading of "excluded labels" as generations is input. -/

namespace Entropic.GenerationCutoff
open Entropic.FiniteModel

/-- Injective four-port states over an arbitrary alphabet. -/
def tuples (A : List Int) : List FaceState :=
  A.flatMap fun a => A.flatMap fun b => A.flatMap fun c => A.filterMap fun d =>
    if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then some (a, b, c, d) else none

/-- K² (as the integer 3K²) is constant over the reduced ensemble, i.e. its variance is zero. -/
def constantK2 (A : List Int) : Bool :=
  match tuples A with
  | [] => true
  | s :: rest => rest.all fun t => threeK2 t == threeK2 s

def reduced (ex : List Int) : List Int := labels.filter fun m => decide (m ∉ ex)

theorem tuples_full : tuples labels = states := rfl

theorem exclusion_counts :
    (labels.sublistsLen 1).length = 7 ∧ (labels.sublistsLen 2).length = 21 ∧
    (labels.sublistsLen 3).length = 35 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every one-label exclusion leaves K² nonconstant (nonzero variance). -/
theorem one_exclusion_nonconstant :
    (labels.sublistsLen 1).all (fun ex => !constantK2 (reduced ex)) = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every two-label exclusion leaves K² nonconstant (nonzero variance). -/
theorem two_exclusion_nonconstant :
    (labels.sublistsLen 2).all (fun ex => !constantK2 (reduced ex)) = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every three-label exclusion makes K² constant (zero variance), and the
reduced ensemble is still nonempty (24 states). -/
theorem three_exclusion_constant :
    (labels.sublistsLen 3).all (fun ex => constantK2 (reduced ex) && (tuples (reduced ex)).length == 24) = true := by
  decide

/-- The structural reason, for any integer alphabet: 3K² is invariant under all
permutations of the four ports (it depends only on the label multiset). -/
theorem threeK2_swap12 (a b c d : Int) : threeK2 (a, b, c, d) = threeK2 (b, a, c, d) := by
  simp only [threeK2]; ring
theorem threeK2_swap23 (a b c d : Int) : threeK2 (a, b, c, d) = threeK2 (a, c, b, d) := by
  simp only [threeK2]; ring
theorem threeK2_swap34 (a b c d : Int) : threeK2 (a, b, c, d) = threeK2 (a, b, d, c) := by
  simp only [threeK2]; ring

end Entropic.GenerationCutoff
