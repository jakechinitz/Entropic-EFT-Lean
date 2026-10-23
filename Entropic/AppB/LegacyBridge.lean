import Entropic.EFT.UV.EtaUniqueness
import Entropic.EFT.UV.RootExistence
import Entropic.EFT.Numerics.Spine
import Entropic.AppB.GibbsCalculus
import Entropic.Spine

/-! Bridge to the v0.8 GitHub library (`Entropic.EFT`): its finite Gibbs family over the
1680 `BoundaryCode`s equals ours over the 11-level spectrum. This turns its certificate
structures `GibbsAnalysis`, `EtaUniquenessMath`, `EtaStarSpec`,
`UniqueEtaStarCertificate` and `NumericalSpineCertificate` into proved instances, so
every theorem there that takes them as hypotheses becomes unconditional. -/

noncomputable section
namespace Entropic.AppB.Legacy
open Entropic.EFT.UV

/-- Regroup any function of 3K² over the 1680 states by level, with the exact
multiplicities. -/
theorem regroup (φ : ℤ → ℝ) :
    ∑ b ∈ boundaryStates, φ (quantumK3 b) =
      96 * φ 122 + 96 * φ 134 + 96 * φ 142 + 288 * φ 146 + 192 * φ 152 + 144 * φ 154 +
      384 * φ 158 + 192 * φ 162 + 48 * φ 164 + 96 * φ 166 + 48 * φ 170 := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := quantumK3) (t := allowedK3) spectrum_complete]
  have hfib : ∀ k, ∑ b ∈ boundaryStates with quantumK3 b = k, φ (quantumK3 b) =
      (multiplicity k : ℝ) * φ k := by
    intro k
    rw [Finset.sum_congr rfl (fun b hb => by rw [(Finset.mem_filter.mp hb).2])]
    rw [Finset.sum_const, nsmul_eq_mul]; rfl
  simp only [hfib]
  simp [allowedK3, mult_122, mult_134, mult_142, mult_146, mult_152, mult_154, mult_158,
    mult_162, mult_164, mult_166, mult_170]
  ring

open Entropic.ClosureRoot in
theorem Z_eq (η : ℝ) : Entropic.EFT.UV.Z η = Entropic.ClosureRoot.Z η := by
  refine (regroup (fun k : ℤ => Real.exp (-η * ((k:ℝ) / 3)))).trans ?_
  simp only [Entropic.ClosureRoot.Z, specR, List.map, List.sum_cons, List.sum_nil]
  push_cast; ring_nf

theorem S1_eq (η : ℝ) :
    ∑ b ∈ boundaryStates, quantumK2R b * weight η b = Entropic.ClosureRoot.S1 η := by
  refine (regroup (fun k : ℤ => ((k:ℝ) / 3) * Real.exp (-η * ((k:ℝ) / 3)))).trans ?_
  simp only [Entropic.ClosureRoot.S1, Entropic.ClosureRoot.specR, List.map, List.sum_cons,
    List.sum_nil]
  push_cast; ring_nf

theorem S2_eq (η : ℝ) :
    ∑ b ∈ boundaryStates, (quantumK2R b) ^ 2 * weight η b = Entropic.AppB.S2 η := by
  refine (regroup (fun k : ℤ => ((k:ℝ) / 3) ^ 2 * Real.exp (-η * ((k:ℝ) / 3)))).trans ?_
  simp only [Entropic.AppB.S2, Entropic.ClosureRoot.specR, List.map, List.sum_cons, List.sum_nil]
  push_cast; ring_nf

theorem meanK2_eq (η : ℝ) : Entropic.EFT.UV.meanK2 η = Entropic.FiniteModel.meanK2 η := by
  rw [Entropic.ClosureRoot.meanK2_eq, Entropic.EFT.UV.meanK2, S1_eq, Z_eq]

theorem varK2_eq (η : ℝ) : Entropic.EFT.UV.varK2 η = Entropic.AppB.varK2 η := by
  rw [Entropic.EFT.UV.varK2, secondMomentK2, S2_eq, Z_eq, meanK2_eq,
    Entropic.ClosureRoot.meanK2_eq, Entropic.AppB.varK2]

theorem evidence_eq (η : ℝ) : closureEvidenceLog η = Entropic.ClosureRoot.evidence η := by
  rw [closureEvidenceLog, Z_eq]; rfl

theorem stationary_iff (η : ℝ) :
    StationaryClosure η ↔ Entropic.FiniteModel.ClosureStationary η := by
  unfold StationaryClosure Entropic.FiniteModel.ClosureStationary; rw [meanK2_eq]

theorem sharingEntropy_eq (η : ℝ) : sharingEntropy η = Entropic.ClosureRoot.gshare η := by
  have h := regroup (fun k : ℤ =>
    (Real.exp (-η * ((k:ℝ) / 3)) / Entropic.ClosureRoot.Z η) *
      Real.log (Real.exp (-η * ((k:ℝ) / 3)) / Entropic.ClosureRoot.Z η))
  unfold sharingEntropy prob weight
  rw [Z_eq]
  simp only [quantumK2R] at h ⊢
  rw [h]
  simp only [Entropic.ClosureRoot.gshare, Entropic.ClosureRoot.specR, List.map, List.sum_cons,
    List.sum_nil]
  push_cast; ring_nf

/-! ### Instances of the legacy certificate structures -/

/-- `GibbsAnalysis`: all four fields proved. -/
theorem gibbsAnalysis : GibbsAnalysis where
  mean_bounds := fun η _ => Entropic.EFT.UV.meanK2_bounds η
  variance_bound := fun η _ => by rw [varK2_eq]; exact Entropic.AppB.varK2_le η
  evidence_deriv := fun η hη => by
    have h := Entropic.AppB.evidence_slope hη
    rw [← meanK2_eq] at h
    have hf : closureEvidenceLog = Entropic.ClosureRoot.evidence := funext evidence_eq
    rw [hf]; exact h
  mean_deriv := fun η _ => by
    have h := Entropic.AppB.mean_hasDerivAt η
    have hf : Entropic.EFT.UV.meanK2 = Entropic.FiniteModel.meanK2 := funext meanK2_eq
    rw [hf, varK2_eq]; exact h

/-- `EtaStarSpec`: the 13-digit enclosure, proved. -/
def etaStarSpec : EtaStarSpec :=
  let h := Classical.choose_spec Entropic.ClosureRoot.stationary_exists
  { value := Classical.choose Entropic.ClosureRoot.stationary_exists
    stationary := (stationary_iff _).mpr h.1
    decimal_lo := by
      have := h.2.1; unfold Entropic.ClosureRoot.etaLo at this; exact this
    decimal_hi := by
      have := h.2.2; unfold Entropic.ClosureRoot.etaHi at this; exact this }

/-- `UniqueEtaStarCertificate`: uniqueness and global maximality, proved. -/
def uniqueEtaStar : UniqueEtaStarCertificate where
  eta := etaStarSpec
  uniqueness := fun x hx =>
    Entropic.ClosureRoot.stationary_unique ((stationary_iff x).mp hx)
      ((stationary_iff _).mp etaStarSpec.stationary)
  globalMaximum := fun x hx => by
    rw [evidence_eq, evidence_eq]
    by_cases hxe : x = etaStarSpec.value
    · rw [hxe]
    · exact (Entropic.ClosureRoot.evidence_unique_max
        ((stationary_iff _).mp etaStarSpec.stationary) hx hxe).le

/-! ### `EtaUniquenessMath`: residual analysis, proved -/

theorem meanK2_hasDerivAt' (η : ℝ) :
    HasDerivAt Entropic.EFT.UV.meanK2 (-Entropic.EFT.UV.varK2 η) η := by
  have h := Entropic.AppB.mean_hasDerivAt η
  have hf : Entropic.EFT.UV.meanK2 = Entropic.FiniteModel.meanK2 := funext meanK2_eq
  rw [hf, varK2_eq]; exact h

theorem residual_hasDerivAt {η : ℝ} (hη : 0 < η) :
    HasDerivAt closureResidual (-(3/2) / η ^ 2 + Entropic.EFT.UV.varK2 η) η := by
  have hinv := (hasDerivAt_inv hη.ne').const_mul (3/2 : ℝ)
  have h := hinv.sub (meanK2_hasDerivAt' η)
  convert h using 1
  · funext t; simp only [closureResidual, Pi.sub_apply]; rw [div_eq_mul_inv, mul_inv]; ring
  · field_simp; ring

theorem residual_continuousOn : ContinuousOn closureResidual (Set.Ioi 0) :=
  fun η hη => (residual_hasDerivAt hη).continuousAt.continuousWithinAt

theorem residual_antitone : StrictAntiOn closureResidual (Set.Ioc 0 (9/244 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc _ _)
    (residual_continuousOn.mono Set.Ioc_subset_Ioi_self)
  intro η hη
  rw [interior_Ioc] at hη
  obtain ⟨h0, h1⟩ := hη
  rw [(residual_hasDerivAt h0).deriv]
  have hv : Entropic.EFT.UV.varK2 η ≤ 64 := by rw [varK2_eq]; exact Entropic.AppB.varK2_le η
  have hsq : η ^ 2 < (9/244) ^ 2 := by nlinarith
  have hpos : 0 < η ^ 2 := by positivity
  have : (3/2) / (9/244 : ℝ) ^ 2 < (3/2) / η ^ 2 := div_lt_div_of_pos_left (by norm_num) hpos hsq
  rw [neg_div]; norm_num at this ⊢; linarith

theorem etaStar_mem : etaStarSpec.value ∈ Set.Ioc 0 (9/244 : ℝ) := by
  have h1 := etaStarSpec.decimal_lo
  have h2 := etaStarSpec.decimal_hi
  constructor <;> linarith

theorem residual_etaStar : closureResidual etaStarSpec.value = 0 := by
  have h := etaStarSpec.stationary
  unfold closureResidual; rw [h.2]; ring

theorem etaUniquenessMath : EtaUniquenessMath where
  toGibbsAnalysis := gibbsAnalysis
  residualContinuousPositive := residual_continuousOn
  residualTendsPositiveAtZero := ⟨9/340, by norm_num, fun η h0 h1 => by
    have hm := (Entropic.EFT.UV.meanK2_bounds η).2
    have : (170/3 : ℝ) < 3 / (2 * η) := by
      rw [lt_div_iff₀ (by positivity)]; nlinarith
    unfold closureResidual; linarith⟩
  residualStrictlyDecreasingBelowCutoff := residual_antitone
  residualNegativeAtCutoff := by
    have hm : (9/244 : ℝ) ∈ Set.Ioc 0 (9/244 : ℝ) := ⟨by norm_num, le_refl _⟩
    have hlt : etaStarSpec.value < 9/244 := by
      have := etaStarSpec.decimal_hi; linarith
    have := residual_antitone etaStar_mem hm hlt
    rw [residual_etaStar] at this; exact this

/-! ### `NumericalSpineCertificate`: η*, g_share and ζ with rational enclosures -/

theorem zeta_eq {η : ℝ} (h : η ≤ 49/8) :
    Entropic.EFT.Marked.zeta (Entropic.ClosureRoot.gshare η) η = Entropic.Spine.zeta η := by
  have hx : 0 ≤ 1 - 8 * η / 49 := by linarith
  unfold Entropic.EFT.Marked.zeta Entropic.EFT.Marked.edgeAmplitude
    Entropic.EFT.Marked.noEventAmplitude Entropic.Spine.zeta
  rw [Entropic.EFT.Marked.pairContractionU_closed, Entropic.Spine.rpow_21_2 hx,
    Entropic.EFT.Marked.edgeRecordCount_eq,
    show (21 : ℕ) = 2 * 10 + 1 from rfl, pow_succ, pow_mul, Real.sq_sqrt hx]

theorem etaStar_stationary : Entropic.FiniteModel.ClosureStationary etaStarSpec.value :=
  (stationary_iff _).mp etaStarSpec.stationary

def numericalSpine : Entropic.EFT.Numerics.NumericalSpineCertificate where
  eta := uniqueEtaStar
  gShare := Entropic.ClosureRoot.gshare etaStarSpec.value
  gShareDefinition := (sharingEntropy_eq _).symm
  zetaValue := Entropic.Spine.zeta etaStarSpec.value
  zetaDefinition := by
    show _ = Entropic.EFT.Marked.zeta _ etaStarSpec.value
    rw [zeta_eq]; have := etaStarSpec.decimal_hi; linarith
  etaInterval := ⟨298668443934 / 10 ^ 13, 298668443936 / 10 ^ 13,
    by show _ < etaStarSpec.value; have := etaStarSpec.decimal_lo; push_cast; linarith,
    by show etaStarSpec.value < _; have := etaStarSpec.decimal_hi; push_cast; linarith⟩
  gShareInterval := ⟨74198000220 / 10 ^ 10, 74198000250 / 10 ^ 10,
    by have := (Entropic.ClosureRoot.gshare_bracket etaStar_stationary).1
       unfold Entropic.ClosureRoot.gLo at this; push_cast; linarith,
    by have := (Entropic.ClosureRoot.gshare_bracket etaStar_stationary).2
       unfold Entropic.ClosureRoot.gHi at this; push_cast; linarith⟩
  zetaInterval := ⟨5123584484 / 10 ^ 12, 5123584486 / 10 ^ 12,
    by have := (Entropic.Spine.zeta_bracket etaStar_stationary).1
       refine lt_of_lt_of_le ?_ this
       norm_num [Entropic.Spine.EL, Entropic.Spine.sL, Entropic.ClosureRoot.etaHi],
    by have := (Entropic.Spine.zeta_bracket etaStar_stationary).2
       refine lt_of_le_of_lt this ?_
       norm_num [Entropic.Spine.EU, Entropic.Spine.sU, Entropic.ClosureRoot.etaLo]⟩

/-! ### Unconditional forms of the legacy conditional theorems -/

theorem stationary_root_exists' :
    ∃ η : ℝ, StationaryClosure η ∧ η ∈ Set.Icc (1/100 : ℝ) (9/244) :=
  stationary_root_exists gibbsAnalysis

theorem stationary_root_unique' {η₁ η₂ : ℝ} (h₁ : StationaryClosure η₁)
    (h₂ : StationaryClosure η₂) : η₁ = η₂ :=
  (uniqueEtaStar.uniqueness _ h₁).trans (uniqueEtaStar.uniqueness _ h₂).symm

theorem stationary_le_cutoff' {η : ℝ} (h : StationaryClosure η) : η ≤ 9/244 :=
  stationary_le_cutoff gibbsAnalysis h

theorem closureProduct_strictMonoOn' :
    StrictMonoOn closureProduct (Set.Icc (1/100 : ℝ) (9/244)) :=
  closureProduct_strictMonoOn gibbsAnalysis

end Entropic.AppB.Legacy
