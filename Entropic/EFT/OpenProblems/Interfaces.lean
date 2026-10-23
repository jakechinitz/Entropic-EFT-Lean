import Entropic.EFT.Core.PhysicalInterfaces

/-!
# Entropic.EFT.OpenProblems.Interfaces

Local contract
* Purpose: index of the unresolved completions.
* No field below is inhabited globally in this repository.
* This prevents `open` in the manuscript from becoming `axiom` in Lean.
-/

namespace Entropic.EFT.OpenProblems

/-- Principal unresolved mathematical-physics completions of the current manuscript. -/
structure RemainingCompletion where
  geometricEmbedding : GeometricEmbeddingSpec
  transverseInfluence : TransverseInfluenceSpec
  strongBoundary : StrongBoundarySpec
  arrowOfTime : ArrowOfTimeSpec
  commonContinuum : CommonGeometryCapacityLimit
  microstructureHamiltonianDerived : Prop
  finiteLoopReturnOperatorDerived : Prop
  lorentzViolationLoopAuditPassed : Prop
  sourceRegisterCoherenceLengthDerived : Prop
  causticEnergyBookkeepingDerived : Prop
  qcdMatterSectorDerived : Prop

end Entropic.EFT.OpenProblems
