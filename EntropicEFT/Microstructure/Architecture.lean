import EntropicEFT.Core.PhysicalInterfaces

/-!
# EntropicEFT.Microstructure.Architecture

LOCAL CONTRACT
* Manuscript: Section 23; Appendix H.1--H.8.
* Purpose: collect microscopic action/condensate obligations without contaminating finite
  UV theorems or the corrected H.9 transfer algebra.
* Closed elsewhere: renewal kernel, recurrence algebra, marked routing.
* Open here: stable geometric condensate, full source-coupled Hessian and physical native gate.
-/

namespace EntropicEFT.Microstructure

/-- Seven history layers resolve the same full 1680-state marginal; they are not seven
simultaneous mutually exclusive labels in one tetrahedron. -/
structure SevenLayerHistoryReading where
  layerCount : ℕ := 7
  eachLayerUsesFullBoundaryMarginal : Prop
  onePassVisitsEachLayerOnce : Prop
  noPhysicalSevenFactorOrdering : Prop

/-- Lightest one-bit branch theorem package. -/
structure LightestBranchMath where
  subadditivityDeficitNonnegative : Prop
  fermionicCeilingSeven : Prop
  massFunctionalDecreasesWithResolvedSupport : Prop
  minimumAtSevenAndZeroDeficit : Prop

/-- Distinct operators that the manuscript insists must not be conflated. -/
structure OperatorSeparation where
  refreshProjectorDistinctFromSurvival : Prop
  survivalDistinctFromGftHessian : Prop
  mixingGapDistinctFromChargedGap : Prop

/-- Native whole-tetrahedron renewal circuit. -/
structure NativeRenewalGate where
  fullEnsembleReachable : Prop
  exportsOldClosureRegisterToHistory : Prop
  preparesFreshStationaryAmplitude : Prop
  retainsPositionAndMarkedFiber : Prop
  discardedOutputBranchIndependent : Prop

/-- Full microscopic geometric target. -/
structure DecoratedGeometricAction where
  historyReading : SevenLayerHistoryReading
  nativeGate : NativeRenewalGate
  embedding : GeometricEmbeddingSpec
  markedDecorationRealized : Prop
  noAdditionalLightSourceCoupledMode : Prop

end EntropicEFT.Microstructure
