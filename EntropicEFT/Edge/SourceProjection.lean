import EntropicEFT.Edge.Kernel

/-!
# EntropicEFT.Edge.SourceProjection

LOCAL CONTRACT
* Manuscript: Appendix C.5--C.7.
* Closed algebra: exclusion information log(7/6), source/stiffness ratio formula,
  fixed-epoch entropy-normalization cancellation.
* External mathematics: exact diamond-lattice Green-function evaluation.
* Physical input: mass-per-entropy map at L* and isotropic coarse defect population.
-/

namespace EntropicEFT.Edge

/-- Exact isotropic exclusion information. -/
noncomputable def exclusionInformation : ℝ := Real.log (7/6 : ℝ)

/-- External mathematical certificate for Joyce's diamond-lattice Green function. -/
structure DiamondGreenMath where
  G0 : ℝ
  positive : 0 < G0
  integralRepresentation : Prop
  joyceClosedForm : Prop

/-- Source-to-stiffness ratio after Green matching. -/
noncomputable def kappaOverGamma (L G0 kappaM : ℝ) : ℝ := 3*L / (4*G0*kappaM)

/-- Cell-normalized S_infinity used in the matched Newton normalization. -/
noncomputable def SInfCell (G0 : ℝ) : ℝ := 3*Real.log 2 / (32*Real.pi*G0)

/-- Fixed-epoch entropy unit rescaling: the observable ratio kappa/(gamma*SInf) is invariant
if kappa/gamma and SInf scale together. -/
theorem entropy_unit_ratio_invariant {r S K : ℝ}
    (hK : K ≠ 0) (hS : S ≠ 0) :
    (K*r) / (K*S) = r/S := by
  field_simp [hK, hS]

/-- The exact source likelihood ratio depends only on the exclusion indicator. -/
structure ExclusionSufficiency where
  conditionedVacuum : Prop
  likelihoodRatioIndicatorOnly : Prop
  relativeInformationPreserved : Prop
  independentExclusionsAdd : Prop

end EntropicEFT.Edge
