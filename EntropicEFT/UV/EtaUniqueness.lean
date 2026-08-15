import EntropicEFT.UV.EtaStar

/-!
# EntropicEFT.UV.EtaUniqueness

LOCAL CONTRACT
* Manuscript: Appendix B.2.
* Goal: isolate the real-analysis theorem proving the stationary closure point is globally unique.
* Exact finite inputs already proved elsewhere: K^2 lies in [122/3,170/3], hence range 16.
* Remaining work is ordinary finite-Gibbs calculus; no physical premise is involved.
-/

namespace EntropicEFT.UV

/-- The derivative of the closure evidence is the stationary residual. -/
noncomputable def closureResidual (η : ℝ) : ℝ := 3/(2*η) - meanK2 η

/-- A fully internal uniqueness proof may discharge these standard real-analysis facts.
No downstream physical theorem is allowed to treat this structure as a physical premise. -/
structure EtaUniquenessMath extends GibbsAnalysis where
  residualContinuousPositive : ContinuousOn closureResidual (Set.Ioi 0)
  residualTendsPositiveAtZero : ∃ δ > 0, ∀ η, 0 < η → η < δ → 0 < closureResidual η
  residualStrictlyDecreasingBelowCutoff :
    StrictAntiOn closureResidual (Set.Ioc 0 (9/244 : ℝ))
  residualNegativeAtCutoff : closureResidual (9/244 : ℝ) < 0

/-- Certified final mathematical status intended for the exact finite spectrum. -/
structure UniqueEtaStarCertificate where
  eta : EtaStarSpec
  uniqueness : ∀ x : ℝ, StationaryClosure x → x = eta.value
  globalMaximum : ∀ x : ℝ, 0 < x → closureEvidenceLog x ≤ closureEvidenceLog eta.value

end EntropicEFT.UV
