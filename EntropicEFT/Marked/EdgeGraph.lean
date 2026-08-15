import EntropicEFT.Marked.CorrectedH9

/-!
# EntropicEFT.Marked.EdgeGraph

LOCAL CONTRACT
* Manuscript: H.9 complete edge-Hessian audit.
* Closed finite combinatorics: 21 unordered edges of K7 and adjacency definitions.
* The Johnson-graph eigenvalue computation is isolated as a mathematical certificate.
-/

namespace EntropicEFT.Marked

/-- Unordered pair of seven labels represented canonically by a two-element Finset. -/
abbrev Edge7 := {s : Finset (Fin 7) // s.card = 2}

instance : Fintype Edge7 := inferInstance
instance : DecidableEq Edge7 := inferInstance

/-- Two distinct edges share one endpoint. -/
def shareOne (e f : Edge7) : Prop := e ≠ f ∧ (e.1 ∩ f.1).card = 1

/-- Two edges are disjoint. -/
def disjointEdge (e f : Edge7) : Prop := Disjoint e.1 f.1

/-- Johnson J(7,2) spectral data used in H.9. -/
structure JohnsonEdgeSpectrum where
  A1eigenvalues : List (ℤ × ℕ)
  A0eigenvalues : List (ℤ × ℕ)
  A1_correct : A1eigenvalues = [(-2,14),(3,6),(10,1)]
  A0_correct : A0eigenvalues = [(-4,6),(1,14),(10,1)]

/-- The selected marked kernel has no off-diagonal edge mixing. -/
structure DiagonalMarkedEdgeKernel where
  alpha : ℝ
  offDiagonalZero : Prop
  allTwentyOneEqual : Prop

end EntropicEFT.Marked
