import EntropicEFT.Edge.SourceProjection

/-!
# EntropicEFT.Gravity.Static

LOCAL CONTRACT
* Manuscript: Sections 10--14; Appendices D.1--D.2, N.1--N.3.
* Closed algebra: capacity-field redefinition, coefficient match, fixed-epoch scaling,
  and the exact matched-G cancellation.
* External mathematics: variation of Einstein--Hilbert+GHY to the two-potential scalar
  constraint action and PDE uniqueness are explicit interfaces.
* Physical status: ordinary longitudinal branch only; transverse galactic lensing is not inferred.
-/

namespace EntropicEFT.Gravity
open EntropicEFT.Edge

/-- Weak-field bridge deltaS = -2 SInf Phi / c^2. -/
noncomputable def deltaSFromPhi (c SInf Phi : ℝ) : ℝ := -2*SInf*Phi/c^2

/-- Newton coupling implied by capacity coefficients. -/
noncomputable def newtonFromCapacity (c kappa gamma SInf : ℝ) : ℝ :=
  c^2*kappa/(8*Real.pi*gamma*SInf)

/-- Overall action normalization after the field redefinition. -/
noncomputable def ZS (c kappa SInf : ℝ) : ℝ := 2*kappa*SInf/c^2

/-- Equality of kinetic coefficients after substituting the bridge. -/
theorem kinetic_coefficient_match {c kappa gamma SInf : ℝ}
    (hc : c ≠ 0) (hk : kappa ≠ 0) (hg : gamma ≠ 0) (hS : SInf ≠ 0) :
    -gamma/2 * (2*SInf/c^2)^2 =
      -ZS c kappa SInf / (8*Real.pi*newtonFromCapacity c kappa gamma SInf) := by
  unfold ZS newtonFromCapacity
  field_simp
  try ring

/-- Equality of source coefficients after substituting deltaS. -/
theorem source_coefficient_match {c kappa SInf : ℝ} (hc : c ≠ 0) :
    kappa * (-2*SInf/c^2) = -ZS c kappa SInf := by
  simp [ZS]
  field_simp [hc]

/-- Fixed-epoch entropy-unit convention leaves the potential bridge invariant. -/
theorem bridge_rescaling_invariant {c SInf deltaS K : ℝ}
    (hK : K ≠ 0) (hS : SInf ≠ 0) :
    potentialFromDeficit c (K*SInf) (K*deltaS) =
      potentialFromDeficit c SInf deltaS := by
  simp [potentialFromDeficit]
  field_simp [hK, hS]

/-- One-bit mass-per-entropy map evaluated at the substrate scale. -/
noncomputable def kappaMAtCell (hbar c L : ℝ) : ℝ := hbar / (c*L*Real.log 2)

/-- Green-matched source ratio in the canonical cell gauge. -/
noncomputable def sourceRatioAtCell (hbar c L G0 : ℝ) : ℝ :=
  kappaOverGamma L G0 (kappaMAtCell hbar c L)

/-- Newton normalization after substituting the exact source ratio and cell SInf. -/
noncomputable def matchedG (hbar c L G0 : ℝ) : ℝ :=
  c^2/(8*Real.pi*SInfCell G0) * sourceRatioAtCell hbar c L G0

/-- Key dependency theorem: G0, log 2, and any loop stiffness cancel identically. -/
theorem matchedG_eq_inducedG {hbar c L G0 : ℝ}
    (hh : hbar ≠ 0) (hc : c ≠ 0) (hL : L ≠ 0)
    (hG : G0 ≠ 0) (hlog : Real.log 2 ≠ 0) :
    matchedG hbar c L G0 = inducedG c hbar L := by
  simp [matchedG, sourceRatioAtCell, kappaOverGamma, kappaMAtCell,
    SInfCell, inducedG]
  field_simp [hh, hc, hL, hG, hlog, Real.pi_ne_zero]
  ring

/-- Mathematical reduction from EH+GHY in Newtonian gauge.  This is an external math
proof obligation, not a physical premise. -/
structure EinsteinScalarReduction where
  twoPotentialActionDerived : Prop
  variationPhiGivesPoisson : Prop
  variationPsiGivesSlipConstraint : Prop
  boundaryTermsHandled : Prop

/-- PDE facts required to turn the slip constraint into Phi=Psi under asymptotic flatness. -/
structure StaticPDEMath where
  poissonUniqueness : Prop
  harmonicDecayImpliesZero : Prop
  pointSourceGreenFunction : Prop

/-- Baseline no-slip theorem is conditional only on the mathematical reduction and boundary conditions. -/
structure BaselineNoSlipSpec where
  einsteinReduction : EinsteinScalarReduction
  pdeMath : StaticPDEMath
  asymptoticFlatness : Prop
  phiEqualsPsi : Prop
  ppnGammaOne : Prop
  ppnBetaOne : Prop

end EntropicEFT.Gravity
