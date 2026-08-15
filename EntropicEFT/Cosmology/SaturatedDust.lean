import EntropicEFT.Transport.Telegrapher

/-!
# EntropicEFT.Cosmology.SaturatedDust

LOCAL CONTRACT
* Manuscript: Section 20; Appendix M.
* Closed algebra: epsilon definition, pinned abundance formula, cross-sector reciprocal identity.
* Conditional physics: recruitment reaches the source cap, coherent clock is pinned, allocations
  add per defect, and commitment occurs early enough.
* External field theory: constrained scalar action gives pressureless dust on X=1/2.
-/

namespace EntropicEFT.Cosmology
open EntropicEFT.Transverse

/-- Compact two-phase coefficient. -/
noncomputable def epsilon (gShare : ℝ) : ℝ := gShare/(4*Real.pi^2)

/-- Pinned committed-to-baryon abundance. -/
noncomputable def committedAbundance (gShare : ℝ) : ℝ := 1/epsilon gShare

/-- Same transverse normalization written in epsilon form. -/
noncomputable def galacticScaleFromEpsilon (gShare c H0 : ℝ) : ℝ := epsilon gShare * c*H0

/-- Exact reciprocal structure; independent of the numerical value of gShare. -/
theorem acceleration_abundance_identity {gShare c H0 : ℝ}
    (he : epsilon gShare ≠ 0) :
    galacticScaleFromEpsilon gShare c H0 * committedAbundance gShare = c*H0 := by
  simp [galacticScaleFromEpsilon, committedAbundance]
  field_simp [he]

/-- Per-source recruitment variable sigma_A = epsilon M_c/M_b. -/
noncomputable def recruitmentSigma (eps Mc Mb : ℝ) : ℝ := eps*Mc/Mb

/-- Physical pinned branch conditions. -/
structure PinnedCommittedBranch where
  allRecruitedSourcesAtCap : Prop
  coherentSingleStreamPhase : Prop
  oneTickPerElectronCalibratedInterval : Prop
  perDefectBookkeeping : Prop
  allocationsAdd : Prop
  preAcousticCommitment : Prop

/-- Mathematical constrained-scalar/dust theorem package. -/
structure ConstrainedDustMath where
  XequalsHalf : Prop
  eulerLagrangeConservation : Prop
  stressTensorDustForm : Prop
  pressureZero : Prop
  soundSpeedZero : Prop
  densityScalesAsAminusThree : Prop

/-- Caustic/shell-crossing transition remains conditional. -/
structure CommittedReleaseSpec where
  pinned : PinnedCommittedBranch
  causticBridge : CausticReleaseBridge
  causticBridgeHolds : causticBridge.holds
  firstShellCrossingBreaksSinglePhase : Prop
  recommitmentForbiddenByArrow : Prop

/-- Appendix M exclusion ledger; empirical/numerical premises are not promoted to theorems. -/
structure CarrierExclusionLedger where
  growthLimitedRelaxationExcluded : Prop
  laggedResponseExcluded : Prop
  plateauGradientUnstable : Prop
  railAtSoundSpeedPole : Prop
  releasedBranchesFreeStream : Prop
  conservedIntegratingVariableRequired : Prop

end EntropicEFT.Cosmology
