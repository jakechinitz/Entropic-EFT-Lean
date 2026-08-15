import EntropicEFT.Cosmology.SaturatedDust

/-!
# EntropicEFT.Clusters.Projection

LOCAL CONTRACT
* Manuscript: Section 18; Section 26 cluster rows.
* Closed algebra: capacity ceiling inherited from epsilon, residual/source bookkeeping formulas.
* Conditional physics: diffuse suppression, hot-bath weighting, coherence lift and regime split.
* Empirical inputs: X-ray/SZ hot-atmosphere factor and lensing maps remain data, not axioms.
-/

namespace EntropicEFT.Clusters
open EntropicEFT.Cosmology

/-- Capacity ceiling inherited from the same epsilon as the galactic branch. -/
noncomputable def capacityCeiling (gShare : ℝ) : ℝ := 1/epsilon gShare

/-- Generic relaxed-cluster residual bookkeeping. -/
noncomputable def relaxedResidual (Wbath fcont : ℝ) : ℝ := 1 + (Wbath-1)*fcont

/-- Three-component resolved merger source used as the principal empirical test. -/
noncomputable def resolvedLensingSource (eps Bbath SigmaBath SigmaShock SigmaDec : ℝ) : ℝ :=
  (1 + (1-eps)*Bbath)*SigmaBath + eps*SigmaShock + SigmaDec

/-- The linear coherence-lift candidate is registered as excluded by amplitude; this is an
empirical status field, not a mathematical theorem. -/
structure ClusterDataStatus where
  linearLiftExcluded : Prop
  capacityCeilingRespectedInSample : Prop
  hookMorphologySupported : Prop
  bulletFlexibleReconstructionsNonDiscriminating : Prop

/-- Conditional microscopic cluster completion. -/
structure ClusterCompletion where
  diffuseSuppressionDerived : Prop
  bathWeightMicroscopicOriginDerived : Prop
  coherenceGrowthProfileDerived : Prop
  mergerRegimeBoundaryDerived : Prop
  resolvedMapTestPerformedWithoutFreeDarkHalo : Prop

end EntropicEFT.Clusters
