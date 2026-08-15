import EntropicEFT.UV.Spectrum

/-!
# EntropicEFT.UV.Admissibility

LOCAL CONTRACT
* Manuscript: Sections 6.1--6.3; Appendix B.2.
* Defines: exact finite Gibbs family on the 1680 states.
* Closed here: normalization-ready finite sums and stationary-product algebra.
* Analytic differentiation / certified root isolation lives in `UV.EtaStar`.
-/

open scoped BigOperators
namespace EntropicEFT.UV

/-- Finite partition function. -/
noncomputable def Z (η : ℝ) : ℝ :=
  ∑ b ∈ boundaryStates, Real.exp (-η * quantumK2R b)

noncomputable def weight (η : ℝ) (b : BoundaryCode) : ℝ :=
  Real.exp (-η * quantumK2R b)

noncomputable def prob (η : ℝ) (b : BoundaryCode) : ℝ := weight η b / Z η

noncomputable def meanK2 (η : ℝ) : ℝ :=
  (∑ b ∈ boundaryStates, quantumK2R b * weight η b) / Z η

noncomputable def meanClassicalClosureSq (η : ℝ) : ℝ :=
  (∑ b ∈ boundaryStates, classicalClosureSqR b * weight η b) / Z η

noncomputable def meanQuantumVariance (η : ℝ) : ℝ :=
  (∑ b ∈ boundaryStates, quantumVarianceR b * weight η b) / Z η

noncomputable def secondMomentK2 (η : ℝ) : ℝ :=
  (∑ b ∈ boundaryStates, (quantumK2R b)^2 * weight η b) / Z η

noncomputable def varK2 (η : ℝ) : ℝ := secondMomentK2 η - (meanK2 η)^2

noncomputable def sharingEntropy (η : ℝ) : ℝ :=
  - ∑ b ∈ boundaryStates, prob η b * Real.log (prob η b)

noncomputable def closureEvidenceLog (η : ℝ) : ℝ :=
  Real.log (Z η) + (3/2 : ℝ) * Real.log η

/-- Stationarity proposition independent of the decimal root. -/
noncomputable def StationaryClosure (η : ℝ) : Prop :=
  0 < η ∧ meanK2 η = 3 / (2*η)

theorem closure_saturation_of_stationary {η : ℝ} (h : StationaryClosure η) :
    η * meanK2 η = 3/2 := by
  rcases h with ⟨hη, hm⟩
  have hne : η ≠ 0 := ne_of_gt hη
  rw [hm]
  field_simp [hne]

end EntropicEFT.UV
