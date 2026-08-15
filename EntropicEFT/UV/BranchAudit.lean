import EntropicEFT.UV.EtaStar

/-!
# EntropicEFT.UV.BranchAudit

LOCAL CONTRACT
* Manuscript: Appendix B.5, Appendix L.
* Exact arithmetic is separated from historical/empirical branch selection.
* No theorem says a branch is physically realized.
-/

namespace EntropicEFT.UV

/-- If primitive spin is represented by `twoJ = 2j`, maximal fusion has dimension 4j+1. -/
def transmittedAlphabet (twoJ : ℕ) : ℕ := 2*twoJ + 1

/-- Two orientations times P(n,4). -/
def orientedInjectiveCount (n : ℕ) : ℕ :=
  if 4 ≤ n then 2*n*(n-1)*(n-2)*(n-3) else 0

theorem canonical_branch_alphabet : transmittedAlphabet 3 = 7 := by decide
theorem canonical_branch_count : orientedInjectiveCount 7 = 1680 := by decide

theorem count_without_orientation : 7*6*5*4 = 840 := by norm_num
theorem count_with_repetition_and_orientation : 2*7^4 = 4802 := by norm_num

theorem quotient_ports_count : 2 * Nat.choose 7 4 = 70 := by decide

theorem quotient_ports_and_orientation_count : Nat.choose 7 4 = 35 := by decide

/-- A branch-selection claim must expose the criterion that selects it. -/
structure BranchSelectionCriterion where
  score : ℕ → ℝ
  selected : ℕ
  minimal : ∀ n, score selected ≤ score n
  unique : ∀ n, score n = score selected → n = selected

end EntropicEFT.UV
