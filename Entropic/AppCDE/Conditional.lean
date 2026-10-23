import Entropic.EFT.Structure.Connections
import Entropic.AppB.LegacyBridge
import Entropic.AppCDE.Information
import Entropic.Spine
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Conditioning on a label (ledger C05-71) and the muon comparison (C05-65). -/

noncomputable section
namespace Entropic.AppCDE.Conditional
open Entropic.EFT.UV Entropic.EFT.Structure

set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem card0 : (boundaryStates.filter fun b => (0 : Label) ∈ support b).card = 960 := by decide
theorem card1 : (boundaryStates.filter fun b => (1 : Label) ∈ support b).card = 960 := by decide
theorem card2 : (boundaryStates.filter fun b => (2 : Label) ∈ support b).card = 960 := by decide
theorem card3 : (boundaryStates.filter fun b => (3 : Label) ∈ support b).card = 960 := by decide
theorem card4 : (boundaryStates.filter fun b => (4 : Label) ∈ support b).card = 960 := by decide
theorem card5 : (boundaryStates.filter fun b => (5 : Label) ∈ support b).card = 960 := by decide
theorem card6 : (boundaryStates.filter fun b => (6 : Label) ∈ support b).card = 960 := by decide

/-- Every label is carried by exactly 960 = 1680·4/7 states. -/
theorem card_label (m : Label) : (boundaryStates.filter fun b => m ∈ support b).card = 960 := by
  fin_cases m
  exacts [card0, card1, card2, card3, card4, card5, card6]

theorem log960_lt : Real.log 960 < 7 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have : (2.7182818283 : ℝ) ^ 7 < Real.exp 1 ^ 7 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  nlinarith

/-- C05-71: for any law q supported on the states carrying label m (in particular
p_{η*}(·|m ∈ b)), H(q) ≤ ln 960 < 7 < g_share,eff; so conditioning on a label always changes
(lowers) the entropy. -/
theorem conditional_entropy_lt (m : Label) (q : BoundaryCode → ℝ) (hq : ∀ b, 0 ≤ q b)
    (hq1 : ∑ b, q b = 1) (hsupp : ∀ b, b ∉ (boundaryStates.filter fun b => m ∈ support b) → q b = 0)
    {η : ℝ} (h : Entropic.FiniteModel.ClosureStationary η) :
    Entropic.AppCDE.H q < sharingEntropy η := by
  have hS : (boundaryStates.filter fun b => m ∈ support b).Nonempty := by
    rw [← Finset.card_pos, card_label]; norm_num
  have h1 := Entropic.AppCDE.entropy_le_log_support q hq hq1 _ hS hsupp
  rw [card_label] at h1
  have hg := (Entropic.ClosureRoot.gshare_bracket h).1
  unfold Entropic.ClosureRoot.gLo at hg
  rw [Entropic.AppB.Legacy.sharingEntropy_eq]
  push_cast at h1
  linarith [log960_lt]

/-- The conditional law itself. -/
def condLaw (η : ℝ) (m : Label) (b : BoundaryCode) : ℝ :=
  if b ∈ boundaryStates.filter (fun b => m ∈ support b) then
    prob η b / ∑ c ∈ boundaryStates.filter (fun b => m ∈ support b), prob η c else 0

theorem condLaw_entropy_lt (m : Label) {η : ℝ} (h : Entropic.FiniteModel.ClosureStationary η) :
    Entropic.AppCDE.H (condLaw η m) < sharingEntropy η := by
  have hZ : 0 < Entropic.EFT.UV.Z η := by
    rw [Entropic.AppB.Legacy.Z_eq]; exact Entropic.ClosureRoot.Z_pos η
  have hp : ∀ b, 0 < prob η b := fun b => div_pos (Real.exp_pos _) hZ
  set S := boundaryStates.filter (fun b => m ∈ support b)
  have hS : S.Nonempty := by rw [← Finset.card_pos, card_label]; norm_num
  have hPS : 0 < ∑ c ∈ S, prob η c := Finset.sum_pos (fun c _ => hp c) hS
  apply conditional_entropy_lt m _ _ _ _ h
  · intro b; unfold condLaw; split_ifs
    · exact div_nonneg (hp b).le hPS.le
    · exact le_refl _
  · unfold condLaw
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b => b ∈ S)]
    have e1 : ∑ x ∈ Finset.univ.filter (fun b => b ∈ S),
        (if x ∈ S then prob η x / ∑ c ∈ S, prob η c else 0) = 1 := by
      rw [Finset.sum_congr rfl (fun x hx => if_pos (Finset.mem_filter.mp hx).2),
        ← Finset.sum_div]
      rw [show Finset.univ.filter (fun b => b ∈ S) = S by ext; simp]
      exact div_self hPS.ne'
    have e2 : ∑ x ∈ Finset.univ.filter (fun b => b ∉ S),
        (if x ∈ S then prob η x / ∑ c ∈ S, prob η c else 0) = 0 :=
      Finset.sum_eq_zero (fun x hx => if_neg (Finset.mem_filter.mp hx).2)
    rw [e1, e2, add_zero]
  · intro b hb; unfold condLaw; exact if_neg hb

/-- C05-65 (muon): m_μ/m_e ∈ (206.76828023, 206.76828024) sits at −0.538…−0.534σ from
CODATA 2022 206.7682827(46) (paper: −0.535σ). -/
theorem muon_sigma {η : ℝ} (h : Entropic.FiniteModel.ClosureStationary η) :
    -0.538 < (Entropic.Spine.muRatio η - 206.7682827) / 0.0000046 ∧
      (Entropic.Spine.muRatio η - 206.7682827) / 0.0000046 < -0.534 := by
  obtain ⟨a, b⟩ := Entropic.Spine.muRatio_bracket h
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

end Entropic.AppCDE.Conditional
