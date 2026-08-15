import EntropicEFT.Representation.FusionSpec

/-!
# EntropicEFT.Representation.MarkedComplement

LOCAL CONTRACT
* Manuscript: Appendix B.4.2e; H.9.
* Closed arithmetic: equality of the multiplicity-free endpoint ranges forces `2j = 2s+1`.
* Representation-theoretic premise: both decompositions really contain exactly one copy of
  every spin from zero through their displayed endpoints; that content lives in `FusionSpec`.
* Physical incidence remains separate.
-/

namespace EntropicEFT.Representation

/-- At the level of the displayed multiplicity-free spin ranges, equality of endpoints is unique. -/
theorem endpoint_match_unique {twoJ twoS : ℕ}
    (h : twoJ = twoS + 1) : ComplementEndpointMatch twoJ twoS := h

/-- A three-component response has spin one, i.e. twice-spin two; its unique primitive endpoint
match has twice-spin three, i.e. j=3/2. -/
theorem vector_response_endpoint_unique {twoJ : ℕ}
    (h : ComplementEndpointMatch twoJ 2) : twoJ = 3 := by
  simpa [ComplementEndpointMatch] using h

/-- Dimension equality alone is a useful necessary arithmetic check. -/
theorem three_halves_dimension_match :
    nonmaxComplementDim 3 = markedDim 2 := by
  norm_num [nonmaxComplementDim, markedDim, spinDim, maximalFusionDim]

/-- This structure marks the extra mathematical fact needed to upgrade matching dimensions
into an SU(2)-equivariant identification. -/
structure EquivariantComplementMatch where
  fusion : FusionThreeHalvesSpec
  sameIrrepRange : Prop
  multiplicityOne : Prop
  intertwinerUnitaryOnComplement : Prop

end EntropicEFT.Representation
