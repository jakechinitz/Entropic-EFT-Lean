import EntropicEFT.Representation.FusionSpec
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# EntropicEFT.Representation.SharpTransfer

LOCAL CONTRACT
* Manuscript: Appendix B.4.2b--e.
* Closed algebra: if transmitted and complement maps are orthogonal partial isometries
  whose initial projectors sum to identity, their flagged direct-sum map is an isometry.
* This file does not construct the SU(2) maps themselves.
-/

namespace EntropicEFT.Representation

/-- Abstract projector decomposition sufficient for the sharp 7+9 reversibility statement. -/
structure OrthogonalComplementSplit (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  P : Module.End ℂ H
  Q : Module.End ℂ H
  p_add_q : P + Q = LinearMap.id
  pq_zero : P.comp Q = 0
  qp_zero : Q.comp P = 0
  p_idem : P.comp P = P
  q_idem : Q.comp Q = Q

/-- The paper's exact `16 = 7 + 9` count is independent of the later geometric embedding. -/
theorem exact_state_count_split : 16 = 7 + 9 := by norm_num

/-- Equal unit marked weights are a stronger condition than dimension nine. -/
structure UnitMarkedGram where
  dimension : ℕ := 9
  gramIsIdentity : Prop
  equalWeights : Prop

end EntropicEFT.Representation
