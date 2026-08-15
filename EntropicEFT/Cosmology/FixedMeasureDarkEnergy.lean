import EntropicEFT.Cosmology.SaturatedDust
import EntropicEFT.Marked.CorrectedH9

/-!
# EntropicEFT.Cosmology.FixedMeasureDarkEnergy

LOCAL CONTRACT
* Manuscript: Section 25; Appendix O.1--O.5, O.13.
* Closed algebra: common fixed-N factors cancel from normalized weights; routing ratio
  `(3/2)/<K^2> = eta` at any stationary closure point; monotone-release w_eff inequality
  under explicit sign assumptions.
* Conditional physics: fixed event count becomes a nondynamical continuum measure;
  caustic leak current sources Lambda; volume conjugacy/common continuum limit set Lambda_i=0;
  O.13 uses the selected single-strand canonical realization of the repaired H.9 auxiliary, then
  converts its one-sided stationary record energy to IR energy with the same normalization and
  an unbiased release trigger.
-/

open scoped BigOperators
namespace EntropicEFT.Cosmology
open EntropicEFT.UV

variable {α : Type*} [Fintype α]

/-- Normalized finite weight. -/
noncomputable def normalizedWeight (w : α → ℝ) (x : α) : ℝ := w x / ∑ y, w y

/-- Any nonzero factor common to a fixed-N sector cancels from normalized history weights. -/
theorem common_factor_cancels (w : α → ℝ) (K : ℝ) (hK : K ≠ 0)
    (hsum : (∑ y, w y) ≠ 0) (x : α) :
    normalizedWeight (fun y => K*w y) x = normalizedWeight w x := by
  unfold normalizedWeight
  rw [← Finset.mul_sum]
  field_simp [hK, hsum]

/-- Algebraic O.13 routing ratio before physical interpretation. -/
noncomputable def stationaryRoutingRatio (η : ℝ) : ℝ := (3/2 : ℝ) / meanK2 η

/-- This equality is exactly a restatement of the stationary closure equation. -/
theorem stationaryRoutingRatio_eq_eta {η : ℝ} (h : StationaryClosure η) :
    stationaryRoutingRatio η = η := by
  rcases h with ⟨hη, hm⟩
  have hne : η ≠ 0 := ne_of_gt hη
  rw [stationaryRoutingRatio, hm]
  field_simp [hne]

/-- Pure mathematical O.13 ratio supplied by the selected one-strand finite ledger.
This theorem has no claim yet that the ledger is physical released energy. -/
theorem singleStrand_stationary_ratio_eq_eta {η : ℝ} (h : StationaryClosure η) :
    EntropicEFT.Marked.stationaryRecordEnergyR / meanK2 η = η := by
  rw [EntropicEFT.Marked.stationaryRecordEnergyR_eq_three_halves]
  simpa [stationaryRoutingRatio] using stationaryRoutingRatio_eq_eta h

/-- The physical O.13 theorem requires the single-strand realization plus the downstream
energy/routing bridges.  The value `3/2` itself is no longer a free structure field: it is
the exact zero-point ledger proved in `Marked.SingleStrandRecord`. -/
structure RoutingEnergyBridge where
  etaStar : EtaStarSpec
  markedVertex : EntropicEFT.Marked.MarkedVertexSpec
  sameEta : markedVertex.etaStar.value = etaStar.value
  singleStrand : EntropicEFT.Marked.SingleStrandCanonicalRealization
  singleStrandHolds : singleStrand.holds
  /-- This identifies the selected one-sided stationary record ledger with physical routed IR energy. -/
  recordGeneratorIsPhysicalRoutedEnergy : Prop
  equalConversion : EqualIRConversionNormalization
  equalConversionHolds : equalConversion.holds
  triggerIndependent : ReleaseTriggerIndependentOfClosure
  triggerIndependentHolds : triggerIndependent.holds

namespace RoutingEnergyBridge

noncomputable def etaLeak (B : RoutingEnergyBridge) : ℝ :=
  EntropicEFT.Marked.stationaryRecordEnergyR / meanK2 B.etaStar.value

theorem etaLeak_eq_etaStar (B : RoutingEnergyBridge)
    (_hSingle : B.singleStrand.holds)
    (_hEnergy : B.recordGeneratorIsPhysicalRoutedEnergy)
    (_hConversion : B.equalConversion.holds)
    (_hTrigger : B.triggerIndependent.holds) :
    B.etaLeak = B.etaStar.value := by
  exact singleStrand_stationary_ratio_eq_eta B.etaStar.stationary

end RoutingEnergyBridge

/-- Differential-geometric unimodular theorem package. -/
structure UnimodularMath where
  fixedMeasureVariationTraceFree : Prop
  traceFreeEinsteinEquation : Prop
  contractedBianchi : Prop
  conservedMatterGivesConstantLambda : Prop
  vacuumShiftDropsFromTracelessSource : Prop
  equationOfStateMinusOne : Prop

/-- Physical gate from primitive event counting to the mathematical unimodular package. -/
structure FixedMeasureGravity where
  fixedEventMeasure : FixedContinuumEventMeasure
  fixedEventMeasureHolds : fixedEventMeasure.holds
  math : UnimodularMath
  noIndependentConformalVolumeMode : Prop

/-- If coarse stress is not conserved, its current accumulates into Lambda in the selected
unimodular branch. -/
structure LambdaSourceLaw where
  JExact : Prop
  divergenceLaw : Prop
  dLambdaEqualsEightPiGJ : Prop

/-- Homogeneous accumulation law. -/
structure ReleaseHistory where
  F : ℝ → ℝ
  eta : ℝ
  rhoWouldBeToday : ℝ
  rhoInitialLambda : ℝ
  monotone : Monotone F

/-- Effective equation-of-state algebra written in terms of a positive accumulated integral I
and a nonnegative logarithmic release rate R. -/
noncomputable def wEffFromRelease (R I : ℝ) : ℝ := -1 - R/(3*I)

theorem wEff_le_minus_one {R I : ℝ} (hR : 0 ≤ R) (hI : 0 < I) :
    wEffFromRelease R I ≤ -1 := by
  simp [wEffFromRelease]
  have h3I : 0 < 3*I := by positivity
  have : 0 ≤ R/(3*I) := div_nonneg hR (le_of_lt h3I)
  linarith

/-- Exact finite-regulator centering plus two named continuum bridges required for Lambda_i=0. -/
structure InitialLambdaZeroSpec where
  equilibriumBulkCoefficientZero : Prop
  energyOriginInvariant : Prop
  volumeConjugacy : VolumeConjugacy
  volumeConjugacyHolds : volumeConjugacy.holds
  commonLimit : CommonGeometryCapacityLimit
  commonLimitHolds : commonLimit.holds
  lambdaInitialZero : Prop

end EntropicEFT.Cosmology
