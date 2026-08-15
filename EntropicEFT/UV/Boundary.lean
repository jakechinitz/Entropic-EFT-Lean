import EntropicEFT.Core.PhysicalInterfaces

/-!
# EntropicEFT.UV.Boundary

LOCAL CONTRACT
* Manuscript: Sections 5--6; Appendix B.1, B.4.3--B.4.4.
* Primitive input encoded: seven labels, four distinguishable ports, single-copy
  injectivity, and two global orientations.
* Closed outputs: 840 unoriented assignments and 1680 oriented states.
* Does not prove: why Nature chooses this alphabet or tetrahedral UV architecture.

LLM NOTE
`0 : Fin 7` represents m=-3 and `6 : Fin 7` represents m=+3.
-/

namespace EntropicEFT.UV

abbrev Label := Fin 7

def labelInt (m : Label) : ℤ := (m.val : ℤ) - 3

structure PortAssignment where
  m0 : Label
  m1 : Label
  m2 : Label
  m3 : Label
  deriving DecidableEq, Fintype, Repr

structure BoundaryCode where
  orientation : Fin 2
  assignment : PortAssignment
  deriving DecidableEq, Fintype, Repr

/-- One cell-level channel cannot be routed through two ports. -/
def PortAssignment.injective (a : PortAssignment) : Prop :=
  a.m0 ≠ a.m1 ∧ a.m0 ≠ a.m2 ∧ a.m0 ≠ a.m3 ∧
  a.m1 ≠ a.m2 ∧ a.m1 ≠ a.m3 ∧ a.m2 ≠ a.m3

instance (a : PortAssignment) : Decidable a.injective := by
  unfold PortAssignment.injective; infer_instance

/-- Exact unoriented single-copy state space. -/
def unorientedStates : Finset PortAssignment :=
  Finset.univ.filter PortAssignment.injective

/-- Exact oriented boundary ensemble. -/
def boundaryStates : Finset BoundaryCode :=
  Finset.univ.filter (fun b => b.assignment.injective)

theorem allPortAssignments_card : Fintype.card PortAssignment = 2401 := by
  native_decide

theorem unorientedStates_card : unorientedStates.card = 840 := by
  native_decide

theorem boundaryStates_card : boundaryStates.card = 1680 := by
  native_decide

/-- Raw combinatorial entropy is log 1680; the theorem is an exact rewrite, not a decimal claim. -/
noncomputable def sharingEntropyMax : ℝ := Real.log 1680

theorem sharingEntropyMax_def : sharingEntropyMax = Real.log 1680 := rfl

end EntropicEFT.UV
