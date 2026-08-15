import EntropicEFT.Core.Status

/-!
# EntropicEFT.Core.PhysicalInterfaces

LOCAL CONTRACT
* Manuscript: Sections 1--4, 23--26; Appendices H, N, O.
* Status: interfaces for premises and open completions.
* Proves: nothing about whether Nature instantiates these structures.
* Purpose: prevent physical assumptions from being hidden inside mathematical theorems.
-/

namespace EntropicEFT

/-- Theory-defining UV ontology; the finite calculations begin after these fields are fixed. -/
structure FoundationSpec where
  finiteLocalCapacity : Prop
  geometryCapacityEquivalence : Prop
  massEntropyEquivalence : Prop
  manyPastsOntology : Prop
  tetrahedralUVArchitecture : Prop
  faithfulFullSupportResolution : Prop

/-- The incidence statement needed to read the marked fiber as the complete nonmaximal
primitive-fusion record. -/
structure MarkedFusionIncidence where
  holds : Prop

/-- Physical support-to-rate reading used by the electron anchor. -/
structure SurvivalGapMassBridge where
  holds : Prop

/-- Minimal marked-source reading: the already normalized scalar return reuses the same
closure-response coupling and introduces no second response coefficient. -/
structure SameClosureCouplingMarkedSource where
  holds : Prop

/-- Common continuum gate required by the geometric embedding. -/
structure CommonGeometryCapacityLimit where
  holds : Prop

/-- Fixed primitive event count becomes a nondynamical continuum volume form. -/
structure FixedContinuumEventMeasure where
  holds : Prop

/-- The unique extensive connectivity-independent coefficient maps to the coarse volume operator. -/
structure VolumeConjugacy where
  holds : Prop

/-- Caustic release is dynamically the failure of the committed source-scale clock. -/
structure CausticReleaseBridge where
  holds : Prop

/-- O.13 energy conversion bridge.  Kept distinct from the Gaussian algebra in H.9. -/
structure EqualIRConversionNormalization where
  holds : Prop

/-- O.13 trigger condition: release selection does not reweight internal K^2 microstates. -/
structure ReleaseTriggerIndependentOfClosure where
  holds : Prop

/-- Open geometric GFT/CDT completion.  No global instance is supplied by this project. -/
structure GeometricEmbeddingSpec where
  stableCondensate : Prop
  commonPhysicalSupport : Prop
  uniqueLightSourceCoupledCapacityMode : Prop
  covariantAssembly : Prop
  diffeomorphismWardIdentity : Prop
  correctNewtonNormalization : Prop
  positiveEuclideanTransfer : Prop
  lorentzianContinuation : Prop

/-- Open transverse Schwinger--Keldysh/influence-functional completion. -/
structure TransverseInfluenceSpec where
  retarded : Prop
  causal : Prop
  wardIdentity : Prop
  thermalOccupationCorrect : Prop
  highAccelerationDecoupling : Prop
  lensingKernelDerived : Prop

/-- Open strong-field substrate boundary completion. -/
structure StrongBoundarySpec where
  boundedCausalCapacityEvolution : Prop
  capacityEqualsGeometricInvariant : Prop
  boundaryActionDerived : Prop
  relaxationSpectrumDerived : Prop

/-- Open typicality theorem required for the Many-Pasts arrow of time. -/
structure ArrowOfTimeSpec where
  substratePastHypothesis : Prop
  mixing : Prop
  largeDeviation : Prop
  ordinaryEntropyIncreaseTypical : Prop

end EntropicEFT
