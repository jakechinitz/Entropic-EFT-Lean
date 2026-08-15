import EntropicEFT.Edge.TetrahedralFrame

/-!
# EntropicEFT.Edge.Kernel

LOCAL CONTRACT
* Manuscript: Sections 7--9; Appendix C.1--C.4.
* Closed algebra: tree coupling, minimal-return trace, Dyson resummation, continuum
  stiffness formula once the named minimal return operator is adopted.
* Conditional premise: completeness and relative weights of the minimal return operator.
-/

namespace EntropicEFT.Edge

/-- Bare edge coupling from the 2/3 tetrahedral transverse projection. -/
noncomputable def Jbare (η : ℝ) : ℝ := (2/3 : ℝ) * η

/-- Rooted z=4 tree-to-lattice map. -/
noncomputable def Jtree (η : ℝ) : ℝ := Jbare η / 3

theorem Jtree_closed (η : ℝ) : Jtree η = 2*η/9 := by
  simp [Jtree, Jbare]
  ring

/-- Trace of seven label-diagonal returns plus a rank-one singlet weighted 2/9. -/
noncomputable def SigmaReturn : ℝ := 7 + 2/9

theorem SigmaReturn_closed : SigmaReturn = 65/9 := by
  norm_num [SigmaReturn]

/-- Local Dyson dressing. -/
noncomputable def Jren (η : ℝ) : ℝ := Jtree η / (1 + Jtree η * SigmaReturn)

/-- Ratio of renormalized to tree coupling. -/
noncomputable def loopFactor (η : ℝ) : ℝ := 1 / (1 + Jtree η * SigmaReturn)

theorem Jren_eq_tree_mul_loop (η : ℝ) : Jren η = Jtree η * loopFactor η := by
  simp [Jren, loopFactor]
  ring

/-- The physical premise that no additional return motifs alter the specified operator. -/
structure MinimalReturnCompletion where
  sevenDiagonalReturns : Prop
  singletWeightTwoNinths : Prop
  noAdditionalRelevantMotifs : Prop

/-- Continuum stiffness in the one-sublattice Euclidean convention. -/
noncomputable def gammaStiffness (hbar c L η : ℝ) : ℝ :=
  (4*hbar*c/(3*Real.pi^2*L^2)) * Jren η

/-- The loop dressing is algebraically present in gamma; source matching later shows it
cancels from kappa/gamma. -/
structure EuclideanNormalizationSpec where
  eachUndirectedEdgeCountedOnce : Prop
  cellFourVolumeConvention : Prop

end EntropicEFT.Edge
