import EntropicEFT.Scale.Electron

/-!
# EntropicEFT.Scale.Leptons

LOCAL CONTRACT
* Manuscript: Section 13.5; Appendix I.1.
* Closed arithmetic: 720 = P(6,4), 2/7 singlet/orientation factor, N^2 pair count,
  baseline and marked mass-ratio formulas.
* Physical/model bridge: exponentiating the shell log-overlap functional is a selected
  mass-dressing map; generation termination requires the reduced-spectrum collapse theorem.
-/

namespace EntropicEFT.Scale
open EntropicEFT.Marked

/-- First reduced alphabet count P(6,4) = 6!/(6-4)! = 360 per orientation, doubled = 720. -/
def firstShellMultiplicity : ℕ := 2*6*5*4*3

theorem firstShellMultiplicity_eq : firstShellMultiplicity = 720 := by norm_num [firstShellMultiplicity]

/-- Ordered shell incidences include self terms and both cross directions.
The finite charged-lepton branch only uses N=0,1,2, which are checked exactly here. -/
theorem orderedPairCount_zero : 0^2 = 0 + 2 * Nat.choose 0 2 := by norm_num
theorem orderedPairCount_one : 1^2 = 1 + 2 * Nat.choose 1 2 := by norm_num
theorem orderedPairCount_two : 2^2 = 2 + 2 * Nat.choose 2 2 := by norm_num

/-- Generic combinatorial identity, isolated as ordinary mathematics rather than delegated
to an opaque arithmetic tactic. -/
structure OrderedPairCountMath where
  identity : ∀ N : ℕ, N^2 = N + 2 * Nat.choose N 2

/-- Baseline shell ladder used for N=0,1,2. -/
noncomputable def baselineLeptonRatio (N : ℕ) : ℝ :=
  (720 : ℝ)^N * scalarPassage^(N^2)

/-- Decorated muon ratio. -/
noncomputable def muonRatio (ζ : ℝ) : ℝ := baselineLeptonRatio 1 * Zmu ζ

/-- Decorated tau ratio. -/
noncomputable def tauRatio (ζ : ℝ) : ℝ := baselineLeptonRatio 2 * Zmu ζ * Ztau2 ζ

theorem baselineMuon_closed : baselineLeptonRatio 1 = 1440/7 := by
  norm_num [baselineLeptonRatio, scalarPassage]

theorem baselineTau_closed : baselineLeptonRatio 2 =
    720^2 * (2/7 : ℝ)^4 := by
  norm_num [baselineLeptonRatio, scalarPassage]

/-- Exact shell-spectrum statement required for the three-generation cutoff. -/
structure ShellSpectrumCollapse where
  N0Nondegenerate : Prop
  N1Nondegenerate : Prop
  N2Nondegenerate : Prop
  N3PermutationInvariant : Prop
  noFurtherDistinctClosureShell : Prop

/-- Physical reading of the log-overlap functional as a multiplicative mass dressing. -/
structure ShellMassDressingSpec where
  firstPowerSupportMap : Prop
  orderedPairLogOverlap : Prop
  noFittedLeptonCoefficient : Prop

end EntropicEFT.Scale
