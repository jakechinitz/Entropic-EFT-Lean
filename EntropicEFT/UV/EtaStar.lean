import EntropicEFT.UV.Admissibility

/-!
# EntropicEFT.UV.EtaStar

LOCAL CONTRACT
* Manuscript: Appendix B.2.
* Separates finite exact input from real-analysis proof obligations.
* The manuscript root is represented by `EtaStarSpec` only after stationarity and a
  rational enclosure are supplied.
* No physical assumption occurs here.

IMPORTANT
`GibbsAnalysis` is an external-mathematics interface, not a theory axiom.  It isolates
Mathlib work still required for a fully internal proof of differentiation and certified
root existence.  Downstream physical modules may use only an explicit `EtaStarSpec`.
-/

namespace EntropicEFT.UV

/-- Mathematical facts of the exact finite Gibbs family that can be proved from finite
sum differentiation and elementary variance bounds. -/
structure GibbsAnalysis where
  mean_bounds : ∀ η : ℝ, 0 < η → (122/3 : ℝ) ≤ meanK2 η ∧ meanK2 η ≤ (170/3 : ℝ)
  variance_bound : ∀ η : ℝ, 0 < η → varK2 η ≤ 64
  evidence_deriv : ∀ η : ℝ, 0 < η →
    HasDerivAt closureEvidenceLog (3/(2*η) - meanK2 η) η
  mean_deriv : ∀ η : ℝ, 0 < η → HasDerivAt meanK2 (-varK2 η) η

/-- Any stationary solution lies below 9/244, using only the exact spectral floor. -/
theorem stationary_le_cutoff (A : GibbsAnalysis) {η : ℝ} (h : StationaryClosure η) :
    η ≤ (9/244 : ℝ) := by
  rcases h with ⟨hη, hm⟩
  have hb := (A.mean_bounds η hη).1
  have hmul := mul_le_mul_of_nonneg_left hb (le_of_lt hη)
  rw [hm] at hmul
  have hne : η ≠ 0 := ne_of_gt hη
  field_simp [hne] at hmul
  nlinarith

/-- Certified specification of the manuscript root. -/
structure EtaStarSpec where
  value : ℝ
  stationary : StationaryClosure value
  decimal_lo : (298668443934 : ℝ) / 10^13 < value
  decimal_hi : value < (298668443936 : ℝ) / 10^13

namespace EtaStarSpec

theorem positive (s : EtaStarSpec) : 0 < s.value := s.stationary.1

theorem closure_product (s : EtaStarSpec) : s.value * meanK2 s.value = 3/2 :=
  closure_saturation_of_stationary s.stationary

end EtaStarSpec

end EntropicEFT.UV
