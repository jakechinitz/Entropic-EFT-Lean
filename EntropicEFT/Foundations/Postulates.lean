import EntropicEFT.Core.PhysicalInterfaces

/-!
# EntropicEFT.Foundations.Postulates

LOCAL CONTRACT
* Manuscript: Sections 1--4.
* Purpose: name the theory-defining commitments without turning them into mathematical axioms.
* Status: physical premises only.  No theorem in this file claims that Nature satisfies them.
* Downstream modules receive an explicit `TheoryInputs` value when a physical implication needs it.
-/

namespace EntropicEFT.Foundations

/-- The five theory-defining commitments stated in Section 1.1, plus the common
faithful-resolution rule used on states and histories. -/
structure TheoryInputs where
  finiteCapacity : Prop
  informationGeometry : Prop
  massEntropy : Prop
  manyPasts : Prop
  tetrahedralArchitecture : Prop
  faithfulResolution : Prop

/-- Translation to the common core interface.  This is bookkeeping, not a proof of the fields. -/
def TheoryInputs.toFoundationSpec (T : TheoryInputs) : FoundationSpec where
  finiteLocalCapacity := T.finiteCapacity
  geometryCapacityEquivalence := T.informationGeometry
  massEntropyEquivalence := T.massEntropy
  manyPastsOntology := T.manyPasts
  tetrahedralUVArchitecture := T.tetrahedralArchitecture
  faithfulFullSupportResolution := T.faithfulResolution

/-- Quantum kinematics and the Born/decoherence functional are imported operational inputs,
not an attempted derivation from the substrate. -/
structure OperationalQuantumInputs where
  hilbertKinematics : Prop
  unitaryDynamics : Prop
  initialState : Prop
  sufficientlyRichRecordProjectors : Prop
  decoherenceFunctionalImported : Prop

/-- Relativity/covariance is a continuum target of the relational substrate, not a theorem
of the finite state count by itself. -/
structure ContinuumSymmetryTarget where
  invariantFiniteSignalSpeed : Prop
  lorentzianCoarseKinematics : Prop
  noPreferredFrameOperators : Prop
  generalCovariance : Prop

end EntropicEFT.Foundations
