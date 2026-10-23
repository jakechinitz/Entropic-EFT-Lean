import Entropic.EFT.Scale.Leptons
import Entropic.EFT.UV.EtaUniqueness

/-!
# Entropic.EFT.Numerics.Spine

Local contract
* Manuscript: Appendix P.
* Purpose: specification of certified numerical enclosures, never floating-point proof by fiat.
* Exact combinatorics belong in UV/Marked/Scale modules.  Transcendental decimal values need
  interval certificates or an external verified evaluator.
-/

namespace Entropic.EFT.Numerics
open Entropic.EFT.UV Entropic.EFT.Marked Entropic.EFT.Scale

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

end Entropic.EFT.Numerics
