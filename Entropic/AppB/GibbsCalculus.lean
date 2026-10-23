import Entropic.ClosureRoot
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Appendix B.2 Gibbs calculus and certified moments (ledger C04-17, -20, -21, -24,
-27, -30, -35, -08). Builds on `ClosureRoot`. -/

noncomputable section
namespace Entropic.AppB
open Entropic.FiniteModel Entropic.ClosureRoot

/-- Second moment sum S₂(η) = Σ n x² e^{−ηx}. -/
def S2 (η : ℝ) : ℝ := (specR.map fun p => p.2 * p.1 ^ 2 * Real.exp (-η * p.1)).sum

/-- Variance of K² under the closure Gibbs family. -/
def varK2 (η : ℝ) : ℝ := S2 η / Z η - (S1 η / Z η) ^ 2

theorem S1_hasDerivAt (η : ℝ) : HasDerivAt S1 (-S2 η) η := by
  have h := Zsum_hasDerivAt (specR.map fun p => (p.1, p.2 * p.1)) η
  convert h using 1
  · funext t; simp only [S1, specR, List.map, List.sum_cons, List.sum_nil]; try ring
  · simp only [S2, specR, List.map, List.sum_cons, List.sum_nil]; try ring

/-- C04-27: M′(η) = −Var_η(K²). -/
theorem mean_hasDerivAt (η : ℝ) : HasDerivAt meanK2 (-varK2 η) η := by
  have hZ := Z_pos η
  have h := (S1_hasDerivAt η).fun_div (Z_hasDerivAt η) hZ.ne'
  have hfun : meanK2 = fun t => S1 t / Z t := funext meanK2_eq
  rw [hfun]; convert h using 1
  unfold varK2; field_simp; ring

/-- Evidence slope F′(η) = 3/(2η) − ⟨K²⟩. -/
theorem evidence_slope {η : ℝ} (he : 0 < η) :
    HasDerivAt evidence (3 / (2 * η) - meanK2 η) η := by
  have h := evidence_hasDerivAt he
  convert h using 1
  rw [meanK2_eq, N_eq]; have := Z_pos η; field_simp; ring

/-- C04-17: F″(η) = Var_η(K²) − 3/(2η²), as the derivative of F′. -/
theorem evidence_second {η : ℝ} (he : 0 < η) :
    HasDerivAt (fun t => 3 / (2 * t) - meanK2 t) (varK2 η - 3 / (2 * η ^ 2)) η := by
  have h1 : HasDerivAt (fun t : ℝ => 3 / (2 * t)) (-(3 / (2 * η ^ 2))) η := by
    have := ((hasDerivAt_id η).const_mul 2).inv (by positivity : (2 * η) ≠ 0)
    have := this.const_mul 3
    convert this using 1
    · funext t; simp [div_eq_mul_inv]; try ring
    · simp; field_simp; try ring
  convert h1.sub (mean_hasDerivAt η) using 1; ring

/-- C04-20: the Gibbs variance obeys the Popoviciu bound Var ≤ 64 for every η. -/
theorem varK2_le (η : ℝ) : varK2 η ≤ 64 := by
  have hZ := Z_pos η
  set m : ℝ := 146 / 3
  have hC : S2 η - 2 * m * S1 η + m ^ 2 * Z η ≤ 64 * Z η := by
    simp only [S2, S1, Z, specR, List.map, List.sum_cons, List.sum_nil]
    have e := fun x : ℝ => (Real.exp_pos x).le
    nlinarith [e (-η*(122/3)), e (-η*(134/3)), e (-η*(142/3)), e (-η*(146/3)), e (-η*(152/3)),
      e (-η*(154/3)), e (-η*(158/3)), e (-η*(162/3)), e (-η*(164/3)), e (-η*(166/3)), e (-η*(170/3))]
  have hid : varK2 η = (S2 η - 2 * m * S1 η + m ^ 2 * Z η) / Z η - (S1 η / Z η - m) ^ 2 := by
    unfold varK2; field_simp; ring
  rw [hid]
  have : (S2 η - 2 * m * S1 η + m ^ 2 * Z η) / Z η ≤ 64 := by rw [div_le_iff₀ hZ]; linarith
  nlinarith [sq_nonneg (S1 η / Z η - m)]

/-- C04-21: strict concavity on the window I = [9/340, 9/244]:
F″ ≤ 64 − (2/3)(122/3)² = −28040/27 < 0. -/
theorem concave_on_window {η : ℝ} (h1 : 9/340 ≤ η) (h2 : η ≤ 9/244) :
    varK2 η - 3 / (2 * η ^ 2) ≤ -28040 / 27 := by
  have hv := varK2_le η
  have hη : 0 < η := by linarith
  have : 2 / 3 * (122 / 3) ^ 2 ≤ 3 / (2 * η ^ 2) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  linarith

/-! ### Certified moments at η* (C04-24, C04-30) -/

def Num (q : ℝ) : ℝ :=
  96*(122/3)^2*q^0 + 96*(134/3)^2*q^6 + 96*(142/3)^2*q^10 + 288*(146/3)^2*q^12 + 192*(152/3)^2*q^15 + 144*(154/3)^2*q^16 + 384*(158/3)^2*q^18 + 192*(162/3)^2*q^20 + 48*(164/3)^2*q^21 + 96*(166/3)^2*q^22 + 48*(170/3)^2*q^24

theorem S2_factor (η : ℝ) : S2 η = Real.exp (-η * (122/3)) * Num (Real.exp (-η * (2/3))) := by
  simp only [S2, specR, List.map, List.sum_cons, List.sum_nil]
  rw [exp_split η 6 (134/3) (by norm_num)]
  rw [exp_split η 10 (142/3) (by norm_num)]
  rw [exp_split η 12 (146/3) (by norm_num)]
  rw [exp_split η 15 (152/3) (by norm_num)]
  rw [exp_split η 16 (154/3) (by norm_num)]
  rw [exp_split η 18 (158/3) (by norm_num)]
  rw [exp_split η 20 (162/3) (by norm_num)]
  rw [exp_split η 21 (164/3) (by norm_num)]
  rw [exp_split η 22 (166/3) (by norm_num)]
  rw [exp_split η 24 (170/3) (by norm_num)]
  unfold Num; ring

theorem Num_mono {q b : ℝ} (h0 : 0 ≤ q) (h : q ≤ b) : Num q ≤ Num b := by
  unfold Num
  have := tpos 0 (c := 96*(122/3)^2) (by norm_num) h0 h
  have := tpos 6 (c := 96*(134/3)^2) (by norm_num) h0 h
  have := tpos 10 (c := 96*(142/3)^2) (by norm_num) h0 h
  have := tpos 12 (c := 288*(146/3)^2) (by norm_num) h0 h
  have := tpos 15 (c := 192*(152/3)^2) (by norm_num) h0 h
  have := tpos 16 (c := 144*(154/3)^2) (by norm_num) h0 h
  have := tpos 18 (c := 384*(158/3)^2) (by norm_num) h0 h
  have := tpos 20 (c := 192*(162/3)^2) (by norm_num) h0 h
  have := tpos 21 (c := 48*(164/3)^2) (by norm_num) h0 h
  have := tpos 22 (c := 96*(166/3)^2) (by norm_num) h0 h
  have := tpos 24 (c := 48*(170/3)^2) (by norm_num) h0 h
  simp only [pow_zero, mul_one] at *
  linarith

theorem q_bracket {η : ℝ} (b1 : etaLo < η) (b2 : η < etaHi) :
    (98028568980143394629 / 10 ^ 20 : ℝ) ≤ Real.exp (-η * (2/3)) ∧
    Real.exp (-η * (2/3)) ≤ 98028568980156467106 / 10 ^ 20 :=
  ⟨le_trans qHi_L (Real.exp_le_exp.mpr (by nlinarith)),
   le_trans (Real.exp_le_exp.mpr (by nlinarith)) qLo_U⟩

/-- At any η in the root bracket, S₂/Z lies in [Num(q_L)/Sq(q_U), Num(q_U)/Sq(q_L)]. -/
theorem R2_bracket {η : ℝ} (b1 : etaLo < η) (b2 : η < etaHi) :
    Num (98028568980143394629 / 10 ^ 20) / Sq (98028568980156467106 / 10 ^ 20) ≤ S2 η / Z η ∧
    S2 η / Z η ≤ Num (98028568980156467106 / 10 ^ 20) / Sq (98028568980143394629 / 10 ^ 20) := by
  obtain ⟨hL, hU⟩ := q_bracket b1 b2
  have hq0 : (0:ℝ) ≤ Real.exp (-η * (2/3)) := (Real.exp_pos _).le
  rw [S2_factor, Z_factor, mul_div_mul_left _ _ (Real.exp_pos _).ne']
  have hS := Sq_pos hq0
  have hSL := Sq_pos (show (0:ℝ) ≤ 98028568980143394629 / 10 ^ 20 by norm_num)
  have hSU := Sq_pos (show (0:ℝ) ≤ 98028568980156467106 / 10 ^ 20 by norm_num)
  constructor
  · rw [div_le_div_iff₀ hSU hS]
    exact mul_le_mul (Num_mono (by norm_num) hL) (Sq_mono hq0 hU) hS.le (by unfold Num; positivity)
  · rw [div_le_div_iff₀ hS hSL]
    exact mul_le_mul (Num_mono hq0 hU) (Sq_mono (by norm_num) hL) hSL.le (by unfold Num; positivity)

/-- C04-24/C04-30: Var_{η*}(K²) ∈ (15.68897498, 15.68897503). -/
theorem var_at_root {η : ℝ} (h : ClosureStationary η) :
    15.68897498 < varK2 η ∧ varK2 η < 15.68897503 := by
  obtain ⟨b1, b2⟩ := stationary_bracket h
  obtain ⟨r1, r2⟩ := R2_bracket b1 b2
  have hM : S1 η / Z η = 3 / (2 * η) := by rw [← meanK2_eq]; exact h.2
  unfold etaLo at b1; unfold etaHi at b2
  have hM1 : 3 / (2 * (298668443936 / 10 ^ 13 : ℝ)) < 3 / (2 * η) :=
    div_lt_div_of_pos_left (by norm_num) (by positivity) (by linarith)
  have hM2 : 3 / (2 * η) < 3 / (2 * (298668443934 / 10 ^ 13 : ℝ)) :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) (by linarith)
  have hMpos : 0 < 3 / (2 * (298668443936 / 10 ^ 13 : ℝ)) := by norm_num
  have hsq1 := pow_lt_pow_left₀ hM1 hMpos.le (two_ne_zero)
  have hsq2 := pow_lt_pow_left₀ hM2 (by positivity) (two_ne_zero)
  unfold varK2; rw [hM]
  have n1 : (15.68897498 : ℝ) < Num (98028568980143394629 / 10 ^ 20) / Sq (98028568980156467106 / 10 ^ 20)
      - (3 / (2 * (298668443934 / 10 ^ 13 : ℝ))) ^ 2 := by norm_num [Num, Sq]
  have n2 : Num (98028568980156467106 / 10 ^ 20) / Sq (98028568980143394629 / 10 ^ 20)
      - (3 / (2 * (298668443936 / 10 ^ 13 : ℝ))) ^ 2 < 15.68897503 := by norm_num [Num, Sq]
  constructor <;> linarith

/-- C04-24: curvature F″(η*) = Var − 3/(2η*²) ∈ (−1665.87185, −1665.87184). -/
theorem curvature_at_root {η : ℝ} (h : ClosureStationary η) :
    -1665.87185 < varK2 η - 3 / (2 * η ^ 2) ∧ varK2 η - 3 / (2 * η ^ 2) < -1665.87184 := by
  obtain ⟨v1, v2⟩ := var_at_root h
  obtain ⟨b1, b2⟩ := stationary_bracket h
  unfold etaLo at b1; unfold etaHi at b2
  have hη : 0 < η := by linarith
  have c1 : 3 / (2 * η ^ 2) < 3 / (2 * (298668443934 / 10 ^ 13 : ℝ) ^ 2) :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) (by nlinarith)
  have c2 : 3 / (2 * (298668443936 / 10 ^ 13 : ℝ) ^ 2) < 3 / (2 * η ^ 2) :=
    div_lt_div_of_pos_left (by norm_num) (by positivity) (by nlinarith)
  have n1 : (-1665.87185 : ℝ) < 15.68897498 - 3 / (2 * (298668443934 / 10 ^ 13 : ℝ) ^ 2) := by norm_num
  have n2 : (15.68897503 : ℝ) - 3 / (2 * (298668443936 / 10 ^ 13 : ℝ) ^ 2) < -1665.87184 := by norm_num
  constructor <;> linarith

/-- C04-30: a_UV = 1/Var ∈ (0.0637390268, 0.0637390271). -/
theorem aUV_at_root {η : ℝ} (h : ClosureStationary η) :
    0.0637390268 < 1 / varK2 η ∧ 1 / varK2 η < 0.0637390271 := by
  obtain ⟨v1, v2⟩ := var_at_root h
  have hv : 0 < varK2 η := by linarith
  constructor
  · rw [lt_div_iff₀ hv]; nlinarith
  · rw [div_lt_iff₀ hv]; nlinarith

/-- C04-30: ⟨K²⟩_{η*} = 3/(2η*) ∈ (50.2229154252, 50.2229154257). -/
theorem mean_at_root {η : ℝ} (h : ClosureStationary η) :
    50.2229154252 < meanK2 η ∧ meanK2 η < 50.2229154257 := by
  obtain ⟨b1, b2⟩ := stationary_bracket h
  rw [h.2]; unfold etaLo at b1; unfold etaHi at b2
  have hη : 0 < η := by linarith
  constructor
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

/-! ### σ* and ln 1680 (C04-35, C04-08) -/

/-- C04-35: σ* = π/g_share,eff ∈ (0.4234066474, 0.4234066477). -/
theorem sigma_star {η : ℝ} (h : ClosureStationary η) :
    0.4234066474 < Real.pi / gshare η ∧ Real.pi / gshare η < 0.4234066477 := by
  obtain ⟨g1, g2⟩ := gshare_bracket h
  unfold gLo at g1; unfold gHi at g2
  have hg : 0 < gshare η := by linarith
  have p1 := Real.pi_gt_d20; have p2 := Real.pi_lt_d20
  constructor
  · rw [lt_div_iff₀ hg]; nlinarith
  · rw [div_lt_iff₀ hg]; nlinarith

/-- C04-08: ln 1680 ∈ (7.4265490723, 7.4265490725) (paper: 7.42654907240). -/
theorem log_1680 : 7.4265490723 < Real.log 1680 ∧ Real.log 1680 < 7.4265490725 := by
  have hU : Real.exp (7.4265490723 / 8) ≤ 253025132066591731448 / 10 ^ 20 := by
    refine le_trans (Real.exp_bound' (x := 7.4265490723 / 8) (by norm_num) (by norm_num) (n := 20)
      (by norm_num)) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hL : (253025132072917359548 / 10 ^ 20 : ℝ) ≤ Real.exp (7.4265490725 / 8) := by
    have hb := Real.exp_bound (x := 7.4265490725 / 8) (by rw [abs_of_pos (by norm_num)]; norm_num)
      (n := 20) (by norm_num)
    rw [abs_of_pos (by norm_num : (0:ℝ) < 7.4265490725 / 8)] at hb
    have h1 := (abs_le.mp hb).1
    generalize Real.exp (7.4265490725 / 8) = y at h1 ⊢
    norm_num [Finset.sum_range_succ, Nat.factorial] at h1 ⊢
    linarith
  have e1 : Real.exp 7.4265490723 = Real.exp (7.4265490723 / 8) ^ 8 := by
    rw [← Real.exp_nat_mul]; norm_num
  have e2 : Real.exp 7.4265490725 = Real.exp (7.4265490725 / 8) ^ 8 := by
    rw [← Real.exp_nat_mul]; norm_num
  constructor
  · rw [Real.lt_log_iff_exp_lt (by norm_num), e1]
    calc Real.exp (7.4265490723 / 8) ^ 8 ≤ (253025132066591731448 / 10 ^ 20 : ℝ) ^ 8 :=
          pow_le_pow_left₀ (Real.exp_pos _).le hU 8
      _ < 1680 := by norm_num
  · rw [Real.log_lt_iff_lt_exp (by norm_num), e2]
    calc (1680 : ℝ) < (253025132072917359548 / 10 ^ 20 : ℝ) ^ 8 := by norm_num
      _ ≤ Real.exp (7.4265490725 / 8) ^ 8 := pow_le_pow_left₀ (by norm_num) hL 8

end Entropic.AppB
