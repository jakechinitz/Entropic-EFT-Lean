import EntropicEFT.UV.ClosureInvariant
import EntropicEFT.Core.PhysicalInterfaces

/-!
# EntropicEFT.Gauge.ProjectiveColor

LOCAL CONTRACT
* Manuscript: Appendix I.2.
* Closed algebra: three tetrahedral route polynomials, their closure-scalar sum identity,
  primitive Gram eigenvalue ratio 7/6, t8 and diamond blocking formulas once the named
  minimal kinetic completion is adopted.
* Conditional physical premise: a colored defect carries one persistent open routing leg.
* Open: global SU(3) endpoint lift, quarks/chirality/hypercharge, continuum scheme matching,
  confinement and hadron observables.
-/

namespace EntropicEFT.Gauge
open EntropicEFT.UV

private def mvals (a : PortAssignment) : ℤ × ℤ × ℤ × ℤ :=
  (labelInt a.m0, labelInt a.m1, labelInt a.m2, labelInt a.m3)

/-- Three opposite-face route observables. -/
def routeA (a : PortAssignment) : ℤ :=
  let (m1,m2,m3,m4) := mvals a
  m1*m2 + m3*m4

def routeB (a : PortAssignment) : ℤ :=
  let (m1,m2,m3,m4) := mvals a
  m1*m3 + m2*m4

def routeC (a : PortAssignment) : ℤ :=
  let (m1,m2,m3,m4) := mvals a
  m1*m4 + m2*m3

/-- Twice the route sum equals S^2-Sigma^2. -/
theorem route_sum_identity (a : PortAssignment) :
    2*(routeA a + routeB a + routeC a) = (sumM a)^2 - sumSq a := by
  simp [routeA, routeB, routeC, mvals, sumM, sumSq]
  ring

/-- Therefore route sum and closure K3 are affine complements. -/
theorem route_sum_closure_identity (b : BoundaryCode) :
    2*(routeA b.assignment + routeB b.assignment + routeC b.assignment) =
      144 - quantumK3 b := by
  rw [route_sum_identity]
  simp [quantumK3]
  ring

/-- Primitive route Gram eigenvalues from diagonal 1 and common overlap -1/20. -/
def routeSingletEigenvalue : ℚ := 9/10

def routeDoubletEigenvalue : ℚ := 21/20

theorem primitive_route_ratio : routeDoubletEigenvalue/routeSingletEigenvalue = 7/6 := by
  norm_num [routeDoubletEigenvalue, routeSingletEigenvalue]

/-- Cross-sector arithmetic coincidence: same ratio as inverse one-label source fraction. -/
theorem route_ratio_eq_seven_six : routeDoubletEigenvalue/routeSingletEigenvalue = (7/6 : ℚ) :=
  primitive_route_ratio

/-- Conditional physical identification of the open route qutrit. -/
structure PersistentOpenRoute where
  oneUnclosedRoutingLeg : Prop
  correlationsPreservedWithReference : Prop
  routeSpaceThreeDimensional : Prop

/-- Mathematical channel/group result downstream of the open-route premise. -/
structure ProjectiveQutritMath where
  reversibleReferencePreservingChannelIsUnitary : Prop
  globalPhaseInvisible : Prop
  physicalChannelGroupPU3 : Prop
  lieAlgebraSu3 : Prop
  tracelessEndpointDirectionsEight : Prop
  adjointWilsonForm : Prop

/-- Minimal primitive transfer. -/
noncomputable def primitiveAdjointTransfer : ℚ := 13/14

theorem primitiveAdjointTransfer_pos : 0 < primitiveAdjointTransfer := by norm_num [primitiveAdjointTransfer]

noncomputable def gHKStepSq : ℝ := (2/3 : ℝ) * Real.log (14/13 : ℝ)

/-- Equal spatial/history primitive heat times on the diamond product regulator. -/
noncomputable def diamondTimeToSpace : ℝ := 4*Real.sqrt 2/3

noncomputable def diamondBlockingFactor : ℝ := 2*Real.sqrt 6

noncomputable def graphHKSq : ℝ := diamondBlockingFactor * gHKStepSq

/-- Microscopic assumptions specific to the fixed primitive transfer number. -/
structure MinimalColorKineticCompletion where
  openRoute : PersistentOpenRoute
  identityPrimitivePairing : Prop
  maximumFaithfulThroughput : Prop
  routeFrameIsotropy : Prop
  equalPrimitiveHeatTimes : Prop

/-- Explicit open Standard Model tasks. -/
structure StandardModelCompletion where
  globalSU3Lift : Prop
  trialityCarryingQuarks : Prop
  weakChiralityAndDoublets : Prop
  hyperchargeAssignments : Prop
  latticeFermionAction : Prop
  continuumSchemeMatching : Prop
  confinementDerived : Prop
  hadronObservablesDerived : Prop

end EntropicEFT.Gauge
