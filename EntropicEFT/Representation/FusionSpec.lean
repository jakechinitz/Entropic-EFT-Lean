import EntropicEFT.Representation.SpinDimensions
import EntropicEFT.Core.PhysicalInterfaces

/-!
# EntropicEFT.Representation.FusionSpec

LOCAL CONTRACT
* Manuscript: Appendix B.4.2a--f; H.9, H.10.I.
* Status: external mathematical interface for the SU(2) representation layer.
* Purpose: distinguish actual representation content from dimension arithmetic.
* An inhabitant should eventually be constructed from Mathlib SU(2) representation theory
  or explicit Clebsch--Gordan matrices for j=3/2.
* No physical incidence statement is included here.
-/

namespace EntropicEFT.Representation

/-- Minimal data needed downstream from the exact j=3/2 Clebsch--Gordan construction. -/
structure FusionThreeHalvesSpec where
  pairSpace : Type
  transmitted : Type
  complement : Type
  marked : Type
  pairFinite : Fintype pairSpace
  transmittedFinite : Fintype transmitted
  complementFinite : Fintype complement
  markedFinite : Fintype marked
  pairCard : @Fintype.card pairSpace pairFinite = 16
  transmittedCard : @Fintype.card transmitted transmittedFinite = 7
  complementCard : @Fintype.card complement complementFinite = 9
  markedCard : @Fintype.card marked markedFinite = 9
  /-- Mathematical content of V_3 plus (V_0+V_1+V_2). -/
  multiplicityFreeDecomposition : Prop
  /-- Complement and V_1^P tensor V_1^H carry one copy of J=0,1,2. -/
  complementMarkedIntertwinerExists : Prop
  /-- Exact coherent matching selects the maximal J=3 sector. -/
  sharpMatchingProjectorSelectsMaximal : Prop
  /-- Finite-width mismatch spectrum is 6,5,3,0 on J=0,1,2,3. -/
  mismatchSpectrumCorrect : Prop

/-- Physical incidence is deliberately separate from the mathematical representation spec. -/
structure PhysicalFusionRecord (F : FusionThreeHalvesSpec) where
  incidence : MarkedFusionIncidence
  incidenceHolds : incidence.holds

end EntropicEFT.Representation
