import EntropicEFT.UV.EtaStar
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# EntropicEFT.UV.RootExistence

LOCAL CONTRACT
* Manuscript: Appendix B.2 stationarity root.
* Upgrade: existence of a stationary closure root is now a THEOREM conditional only on
  the calculus fields of `GibbsAnalysis` (finite-sum differentiation), no longer a bare
  field of `EtaStarSpec`.
* Proved unconditionally here (no certificate needed): positivity of the partition
  function; the exact bounds `122/3 ≤ meanK2 η ≤ 170/3` for every real η, discharging
  the `mean_bounds` field of `GibbsAnalysis` outright.
* The IVT endpoints are exact rationals: `g(1/100) ≤ 17/30 < 3/2` and
  `g(9/244) ≥ (9/244)·(122/3) = 3/2` — the same arithmetic coincidence behind the
  cutoff theorem, now used constructively.
* NOT proved here: the thirteen-digit decimal enclosure of `EtaStarSpec` (an interval
  arithmetic project) and the derivative fields of `GibbsAnalysis` themselves.
-/

namespace EntropicEFT.UV

open scoped BigOperators

/-! ## Unconditional groundwork -/

theorem boundaryStates_nonempty : boundaryStates.Nonempty := by
  rw [← Finset.card_pos, boundaryStates_card]
  norm_num

theorem Z_pos (η : ℝ) : 0 < Z η :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) boundaryStates_nonempty

theorem quantumK2R_lower {b : BoundaryCode} (hb : b ∈ boundaryStates) :
    (122/3 : ℝ) ≤ quantumK2R b := by
  have h := spectrum_min b hb
  unfold quantumK2R
  have h' : (122 : ℝ) ≤ (quantumK3 b : ℝ) := by exact_mod_cast h
  linarith

theorem quantumK2R_upper {b : BoundaryCode} (hb : b ∈ boundaryStates) :
    quantumK2R b ≤ (170/3 : ℝ) := by
  have h := spectrum_max b hb
  unfold quantumK2R
  have h' : ((quantumK3 b : ℝ)) ≤ 170 := by exact_mod_cast h
  linarith

/-- The Gibbs mean never leaves the exact spectral window, for EVERY real η.
This discharges the `mean_bounds` field of `GibbsAnalysis` as a theorem. -/
theorem meanK2_bounds (η : ℝ) : (122/3 : ℝ) ≤ meanK2 η ∧ meanK2 η ≤ (170/3 : ℝ) := by
  constructor
  · unfold meanK2
    rw [le_div_iff₀ (Z_pos η)]
    unfold Z
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    exact mul_le_mul_of_nonneg_right (quantumK2R_lower hb) (Real.exp_pos _).le
  · unfold meanK2
    rw [div_le_iff₀ (Z_pos η)]
    unfold Z
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    exact mul_le_mul_of_nonneg_right (quantumK2R_upper hb) (Real.exp_pos _).le

/-! ## The closure product and its endpoints -/

/-- The closure product `g η = η · ⟨K²⟩_η`; stationarity is `g η = 3/2`. -/
noncomputable def closureProduct (η : ℝ) : ℝ := η * meanK2 η

theorem closureProduct_left_endpoint : closureProduct (1/100) ≤ 17/30 := by
  unfold closureProduct
  have h := (meanK2_bounds (1/100)).2
  nlinarith

theorem closureProduct_right_endpoint : (3/2 : ℝ) ≤ closureProduct (9/244) := by
  unfold closureProduct
  have h := (meanK2_bounds (9/244)).1
  nlinarith

/-! ## Continuity from the certificate's derivative field -/

theorem closureProduct_continuousOn (A : GibbsAnalysis) :
    ContinuousOn closureProduct (Set.Icc (1/100 : ℝ) (9/244)) := by
  apply ContinuousOn.mul continuousOn_id
  intro η hη
  have hpos : (0 : ℝ) < η := lt_of_lt_of_le (by norm_num) hη.1
  exact ((A.mean_deriv η hpos).continuousAt).continuousWithinAt

/-! ## Existence -/

/-- MAIN THEOREM: the stationarity equation has a root in the exact rational window
`[1/100, 9/244]`, conditional only on the finite-sum calculus certificate. -/
theorem stationary_root_exists (A : GibbsAnalysis) :
    ∃ η : ℝ, StationaryClosure η ∧ η ∈ Set.Icc (1/100 : ℝ) (9/244) := by
  have hab : (1/100 : ℝ) ≤ 9/244 := by norm_num
  have hsub := intermediate_value_Icc hab (closureProduct_continuousOn A)
  have hmem : (3/2 : ℝ) ∈ Set.Icc (closureProduct (1/100)) (closureProduct (9/244)) := by
    constructor
    · linarith [closureProduct_left_endpoint]
    · exact closureProduct_right_endpoint
  obtain ⟨η, hη, hg⟩ := hsub hmem
  refine ⟨η, ⟨lt_of_lt_of_le (by norm_num) hη.1, ?_⟩, hη⟩
  have hne : η ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hη.1)
  unfold closureProduct at hg
  field_simp
  linarith [hg]

/-! ## Uniqueness on the window -/

/-- The closure product is strictly increasing on the window: its derivative is
`⟨K²⟩ − η·Var(K²)`, and either the variance is nonpositive (derivative ≥ mean > 0) or
it is bounded by 64 so `η·Var ≤ (9/244)·64 < 122/3 ≤ ⟨K²⟩`. -/
theorem closureProduct_strictMonoOn (A : GibbsAnalysis) :
    StrictMonoOn closureProduct (Set.Icc (1/100 : ℝ) (9/244)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (closureProduct_continuousOn A)
  intro η hη
  rw [interior_Icc] at hη
  have hpos : (0 : ℝ) < η := by linarith [hη.1]
  have hd : HasDerivAt closureProduct (meanK2 η - η * varK2 η) η := by
    have h := (hasDerivAt_id η).mul (A.mean_deriv η hpos)
    simp only [id_eq, one_mul] at h
    unfold closureProduct
    have heq : meanK2 η + η * -varK2 η = meanK2 η - η * varK2 η := by ring
    rw [heq] at h
    exact h
  rw [hd.deriv]
  have hmean := (meanK2_bounds η).1
  rcases le_or_gt (varK2 η) 0 with hv | hv
  · have hnp : η * varK2 η ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpos.le hv
    linarith
  · have hvb := A.variance_bound η hpos
    have h1 : η * varK2 η ≤ (9/244) * varK2 η :=
      mul_le_mul_of_nonneg_right (le_of_lt hη.2) hv.le
    have h2 : (9/244 : ℝ) * varK2 η ≤ (9/244) * 64 :=
      mul_le_mul_of_nonneg_left hvb (by norm_num)
    linarith

/-- The root in the window is unique. -/
theorem stationary_root_unique (A : GibbsAnalysis) {η₁ η₂ : ℝ}
    (h₁ : StationaryClosure η₁) (h₂ : StationaryClosure η₂)
    (m₁ : η₁ ∈ Set.Icc (1/100 : ℝ) (9/244)) (m₂ : η₂ ∈ Set.Icc (1/100 : ℝ) (9/244)) :
    η₁ = η₂ := by
  have g₁ : closureProduct η₁ = 3/2 := closure_saturation_of_stationary h₁
  have g₂ : closureProduct η₂ = 3/2 := closure_saturation_of_stationary h₂
  exact (closureProduct_strictMonoOn A).injOn m₁ m₂ (by rw [g₁, g₂])

end EntropicEFT.UV
