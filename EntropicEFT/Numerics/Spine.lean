import EntropicEFT.Scale.Leptons
import EntropicEFT.UV.EtaUniqueness

/-!
# EntropicEFT.Numerics.Spine

LOCAL CONTRACT
* Manuscript: Appendix P.
* Purpose: specification of certified numerical enclosures, never floating-point proof by fiat.
* Exact combinatorics belong in UV/Marked/Scale modules.  Transcendental decimal values need
  interval certificates or an external verified evaluator.
-/

namespace EntropicEFT.Numerics
open EntropicEFT.UV EntropicEFT.Marked EntropicEFT.Scale

/-- A numerical certificate must connect every decimal to the exact definitions. -/
structure NumericalSpineCertificate where
  eta : UniqueEtaStarCertificate
  gShare : ℝ
  gShareDefinition : gShare = sharingEntropy eta.eta.value
  zetaValue : ℝ
  zetaDefinition : zetaValue = zeta gShare eta.eta.value
  etaInterval : RatInterval eta.eta.value
  gShareInterval : RatInterval gShare
  zetaInterval : RatInterval zetaValue

/-- CODATA/PDG values are comparison inputs only. -/
structure EmpiricalComparisonInputs where
  hbar : ℝ
  c : ℝ
  electronMass : ℝ
  measuredG : ℝ
  measuredMuonElectronRatio : ℝ
  measuredTauElectronRatio : ℝ

end EntropicEFT.Numerics
