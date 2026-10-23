import Entropic.AppB.LegacyBridge
import Entropic.Spine

/-! Rényi entropies of the closure ensemble (ledger C05-55 numerics) and a reusable
logarithm enclosure. -/

noncomputable section
namespace Entropic.AppCDE
open Entropic.FiniteModel Entropic.ClosureRoot

/-- Logarithm enclosure around ln 1680: if x ≥ 1680·U(a) where U(a) ≥ e^{−a} then
ln x ≥ ln 1680 − a; if x ≤ 1680·L(a) where L(a) ≤ e^{−a} then ln x ≤ ln 1680 − a. -/
theorem log_ge_of {x a : ℝ} (hx : 0 < x) (h : 1680 * Real.exp (-a) ≤ x) :
    Real.log 1680 - a ≤ Real.log x := by
  have := Real.log_le_log (by positivity) h
  rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp, ← sub_eq_add_neg] at this

theorem log_le_of {x a : ℝ} (hx : 0 < x) (h : x ≤ 1680 * Real.exp (-a)) :
    Real.log x ≤ Real.log 1680 - a := by
  have := Real.log_le_log hx h
  rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp, ← sub_eq_add_neg] at this

def qL : ℝ := 98028568980143394629 / 10 ^ 20
def qU : ℝ := 98028568980156467106 / 10 ^ 20

/-- H_∞ = −ln max_b p(b) = ln Sq(q) ∈ (7.13438502, 7.13438504) (paper: 7.1343850). -/
theorem Hinf_value {η : ℝ} (h : ClosureStationary η) :
    7.134385020 < Real.log (Sq (Real.exp (-η * (2/3)))) ∧
      Real.log (Sq (Real.exp (-η * (2/3)))) < 7.134385045 := by
  obtain ⟨b1, b2⟩ := stationary_bracket h
  obtain ⟨s1, s2⟩ := Sq_bracket b1 b2
  obtain ⟨l1, l2⟩ := Entropic.AppB.log_1680
  have hS := Sq_pos (Real.exp_pos (-η * (2/3))).le
  constructor
  · have e := (Entropic.Spine.exp_neg_encl 14 (by norm_num) (a := 0.29216405) (by norm_num) (by norm_num)).2
    have := log_ge_of hS (le_trans (by
      refine le_trans (mul_le_mul_of_nonneg_left e (by norm_num)) ?_
      norm_num [Finset.sum_range_succ, Nat.factorial]) s1)
    linarith
  · have e := (Entropic.Spine.exp_neg_encl 14 (by norm_num) (a := 0.29216403) (by norm_num) (by norm_num)).1
    have := log_le_of hS (le_trans s2 (by
      refine le_trans ?_ (mul_le_mul_of_nonneg_left e (by norm_num))
      norm_num [Finset.sum_range_succ, Nat.factorial]))
    linarith

/-- H₂ = −ln Σ p² = ln(Sq(q)²/Sq(q²)) ∈ (7.41254862, 7.41254866) (paper: 7.4125486). -/
theorem H2_value {η : ℝ} (h : ClosureStationary η) :
    7.41254862 < Real.log (Sq (Real.exp (-η * (2/3))) ^ 2 / Sq (Real.exp (-η * (2/3)) ^ 2)) ∧
      Real.log (Sq (Real.exp (-η * (2/3))) ^ 2 / Sq (Real.exp (-η * (2/3)) ^ 2)) < 7.41254866 := by
  obtain ⟨b1, b2⟩ := stationary_bracket h
  obtain ⟨hL, hU⟩ := Entropic.AppB.q_bracket b1 b2
  obtain ⟨l1, l2⟩ := Entropic.AppB.log_1680
  set q := Real.exp (-η * (2/3))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hSq := Sq_pos hq0
  have hSq2 := Sq_pos (sq_nonneg q)
  have hqL0 : (0:ℝ) ≤ 98028568980143394629 / 10 ^ 20 := by norm_num
  -- monotone enclosures
  have A1 : Sq (98028568980143394629 / 10 ^ 20) ≤ Sq q := Sq_mono hqL0 hL
  have A2 : Sq q ≤ Sq (98028568980156467106 / 10 ^ 20) := Sq_mono hq0 hU
  have B1 : Sq ((98028568980143394629 / 10 ^ 20) ^ 2) ≤ Sq (q ^ 2) :=
    Sq_mono (sq_nonneg _) (pow_le_pow_left₀ hqL0 hL 2)
  have B2 : Sq (q ^ 2) ≤ Sq ((98028568980156467106 / 10 ^ 20) ^ 2) :=
    Sq_mono (sq_nonneg _) (pow_le_pow_left₀ hq0 hU 2)
  have hR : 0 < Sq q ^ 2 / Sq (q ^ 2) := by positivity
  have R1 : Sq (98028568980143394629 / 10 ^ 20) ^ 2 / Sq ((98028568980156467106 / 10 ^ 20) ^ 2)
      ≤ Sq q ^ 2 / Sq (q ^ 2) :=
    div_le_div₀ (by positivity) (pow_le_pow_left₀ (Sq_pos hqL0).le A1 2)
      (Sq_pos (sq_nonneg _)) B2
  have R2 : Sq q ^ 2 / Sq (q ^ 2) ≤
      Sq (98028568980156467106 / 10 ^ 20) ^ 2 / Sq ((98028568980143394629 / 10 ^ 20) ^ 2) :=
    div_le_div₀ (by positivity) (pow_le_pow_left₀ hSq.le A2 2) (Sq_pos (sq_nonneg _)) B1
  constructor
  · have e := (Entropic.Spine.exp_neg_encl 10 (by norm_num) (a := 0.01400045) (by norm_num) (by norm_num)).2
    have := log_ge_of hR (le_trans (by
      refine le_trans (mul_le_mul_of_nonneg_left e (by norm_num)) ?_
      norm_num [Sq, Finset.sum_range_succ, Nat.factorial]) R1)
    linarith
  · have e := (Entropic.Spine.exp_neg_encl 10 (by norm_num) (a := 0.01400042) (by norm_num) (by norm_num)).1
    have := log_le_of hR (le_trans R2 (by
      refine le_trans ?_ (mul_le_mul_of_nonneg_left e (by norm_num))
      norm_num [Sq, Finset.sum_range_succ, Nat.factorial]))
    linarith

/-! ### Identification with the 1680-state Gibbs law -/

open Entropic.EFT.UV in
/-- Σ_b p(b)² = Z(2η)/Z(η)² = Sq(q²)/Sq(q)², so H₂ above is −ln Σ p². -/
theorem sum_prob_sq (η : ℝ) :
    ∑ b ∈ boundaryStates, prob η b ^ 2 =
      Sq (Real.exp (-η * (2/3)) ^ 2) / Sq (Real.exp (-η * (2/3))) ^ 2 := by
  have hw : ∀ b, prob η b ^ 2 = weight (2 * η) b / Entropic.EFT.UV.Z η ^ 2 := by
    intro b; unfold prob weight; rw [div_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  simp_rw [hw]
  rw [← Finset.sum_div]
  have h1 : ∑ b ∈ boundaryStates, weight (2 * η) b = Entropic.EFT.UV.Z (2 * η) := rfl
  rw [h1, Entropic.AppB.Legacy.Z_eq, Entropic.AppB.Legacy.Z_eq, Z_factor, Z_factor]
  have hq : Real.exp (-(2 * η) * (2/3)) = Real.exp (-η * (2/3)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have he : Real.exp (-(2 * η) * (122/3)) = Real.exp (-η * (122/3)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [hq, he]
  have := Sq_pos (Real.exp_pos (-η * (2/3))).le
  have := Real.exp_pos (-η * (122/3))
  field_simp

open Entropic.EFT.UV in
/-- max_b p(b) = e^{−η·122/3}/Z = 1/Sq(q) (attained on the 96 ground states), so
H_∞ = ln Sq(q). -/
theorem max_prob {η : ℝ} (hη : 0 < η) :
    (∀ b ∈ boundaryStates, prob η b ≤ 1 / Sq (Real.exp (-η * (2/3)))) ∧
      ∃ b ∈ boundaryStates, prob η b = 1 / Sq (Real.exp (-η * (2/3))) := by
  have hZ : Entropic.EFT.UV.Z η = Real.exp (-η * (122/3)) * Sq (Real.exp (-η * (2/3))) := by
    rw [Entropic.AppB.Legacy.Z_eq, Z_factor]
  have hZp : 0 < Entropic.EFT.UV.Z η := by rw [hZ]; exact mul_pos (Real.exp_pos _) (Sq_pos (Real.exp_pos _).le)
  have key : 1 / Sq (Real.exp (-η * (2/3))) = Real.exp (-η * (122/3)) / Entropic.EFT.UV.Z η := by
    rw [hZ]; field_simp
  rw [key]
  constructor
  · intro b hb
    unfold prob weight
    apply div_le_div_of_nonneg_right _ hZp.le
    apply Real.exp_le_exp.mpr
    have := spectrum_min b hb
    have h3 : (122:ℝ) ≤ quantumK3 b := by exact_mod_cast this
    unfold quantumK2R; nlinarith
  · have hne : (boundaryStates.filter fun b => quantumK3 b = 122).Nonempty := by
      rw [← Finset.card_pos]; have := mult_122; unfold Entropic.EFT.UV.multiplicity at this; omega
    obtain ⟨b, hb⟩ := hne
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
    refine ⟨b, hb1, ?_⟩
    unfold prob weight quantumK2R; rw [hb2]; norm_num

end Entropic.AppCDE
