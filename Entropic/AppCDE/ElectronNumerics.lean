import Entropic.Spine
import Entropic.AppCDE.WeakField
import Entropic.AppCDE.Continuum
import Mathlib.Analysis.Real.Pi.Bounds

/-! Appendix D electron anchor: certified numbers at the closure root (ledger C05-58,
-63, -65, -72). Inputs: CODATA 2022 λ_e = 3.8615926744e-13 m, m_e = 9.1093837139e-31 kg,
exact h = 6.62607015e-34 J s and c = 299792458 m/s, G = 6.67430(15)e-11. -/

noncomputable section
namespace Entropic.AppCDE
open Entropic.FiniteModel Entropic.ClosureRoot Entropic.Spine

/-- e^{−g} at the root lies in (EL/S_U, EU/S_L). -/
theorem expneg_g_bracket {η : ℝ} (h : ClosureStationary η) :
    EL / (1254365353088095 / 10 ^ 12) ≤ Real.exp (-gshare η) ∧
      Real.exp (-gshare η) ≤ EU / (1254365353085696 / 10 ^ 12) := by
  obtain ⟨b1, b2⟩ := stationary_bracket h
  obtain ⟨hSL, hSU⟩ := Sq_bracket b1 b2
  rw [exp_neg_gshare h]
  have hE1 : EL ≤ Real.exp (-(3/2 - η * (122/3))) := by
    have e := (exp_neg_encl 14 (by norm_num) (a := 3/2 - etaLo * (122/3))
      (by norm_num [etaLo]) (by norm_num [etaLo])).1
    refine le_trans ?_ (le_trans e (Real.exp_le_exp.mpr (by linarith)))
    norm_num [EL, etaLo, Finset.sum_range_succ, Nat.factorial]
  have hE2 : Real.exp (-(3/2 - η * (122/3))) ≤ EU := by
    have e := (exp_neg_encl 14 (by norm_num) (a := 3/2 - etaHi * (122/3))
      (by norm_num [etaHi]) (by norm_num [etaHi])).2
    refine le_trans (le_trans (Real.exp_le_exp.mpr (by linarith)) e) ?_
    norm_num [EU, etaHi, Finset.sum_range_succ, Nat.factorial]
  have hS0 : 0 < Sq (Real.exp (-η * (2/3))) := Sq_pos (Real.exp_pos _).le
  constructor
  · exact div_le_div₀ (Real.exp_pos _).le hE1 hS0 hSU
  · exact div_le_div₀ (by norm_num [EU]) hE2 (by norm_num) hSL

def rLo : ℝ := 27755723378 / 10 ^ 33
def rHi : ℝ := 27755723381 / 10 ^ 33

/-- r = p_rec = e^{−7g} ∈ (2.7755723378, 2.7755723381)·10⁻²³. -/
theorem r_bracket {η : ℝ} (h : ClosureStationary η) :
    rLo < Real.exp (-7 * gshare η) ∧ Real.exp (-7 * gshare η) < rHi := by
  obtain ⟨a, b⟩ := expneg_g_bracket h
  have e7 : Real.exp (-7 * gshare η) = Real.exp (-gshare η) ^ 7 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e7]
  have h0 : 0 ≤ EL / (1254365353088095 / 10 ^ 12 : ℝ) := by norm_num [EL]
  constructor
  · refine lt_of_lt_of_le ?_ (pow_le_pow_left₀ h0 a 7)
    norm_num [rLo, EL]
  · refine lt_of_le_of_lt (pow_le_pow_left₀ (Real.exp_pos _).le b 7) ?_
    norm_num [rHi, EU]

/-- C05-58: p_rec/2 ≈ 1.39·10⁻²³. -/
theorem prec_half {η : ℝ} (h : ClosureStationary η) :
    1.38e-23 < Real.exp (-7 * gshare η) / 2 ∧ Real.exp (-7 * gshare η) / 2 < 1.39e-23 := by
  obtain ⟨a, b⟩ := r_bracket h; unfold rLo at a; unfold rHi at b
  constructor <;> linarith

/-- C05-72: dim_eff = e^{7g} = 3.60286052·10²², and (2/3)e^{7g} = 2.40190701·10²². -/
theorem dim_eff_values {η : ℝ} (h : ClosureStationary η) :
    3.602860520e22 < Real.exp (7 * gshare η) ∧ Real.exp (7 * gshare η) < 3.602860522e22 ∧
      2.401907013e22 < 2/3 * Real.exp (7 * gshare η) ∧
      2/3 * Real.exp (7 * gshare η) < 2.401907015e22 := by
  obtain ⟨a, b⟩ := r_bracket h
  have e : Real.exp (7 * gshare η) = (Real.exp (-7 * gshare η))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [e]
  have hr0 : 0 < Real.exp (-7 * gshare η) := Real.exp_pos _
  have i1 : (rHi)⁻¹ < (Real.exp (-7 * gshare η))⁻¹ := inv_strictAnti₀ hr0 b
  have i2 : (Real.exp (-7 * gshare η))⁻¹ < (rLo)⁻¹ := inv_strictAnti₀ (by norm_num [rLo]) a
  unfold rLo at i2; unfold rHi at i1
  refine ⟨lt_trans (by norm_num) i1, lt_trans i2 (by norm_num), ?_, ?_⟩
  · nlinarith [lt_trans (by norm_num : (3.602860520e22:ℝ) < (27755723381 / 10 ^ 33)⁻¹) i1]
  · nlinarith [lt_trans i2 (by norm_num : ((27755723378 / 10 ^ 33 : ℝ))⁻¹ < 3.602860522e22)]

/-- ζ_* ∈ (0.005123584484, 0.005123584486), hence Z_e = (1+ζ)(1+7ζ²) ∈ (1.0053082838, 1.0053082839). -/
theorem zeta_rat {η : ℝ} (h : ClosureStationary η) :
    0.005123584484 < zeta η ∧ zeta η < 0.005123584486 := by
  obtain ⟨z1, z2⟩ := zeta_bracket h
  constructor
  · refine lt_of_lt_of_le ?_ z1; norm_num [EL, sL, etaHi]
  · refine lt_of_le_of_lt z2 ?_; norm_num [EU, sU, etaLo]

def Ze (η : ℝ) : ℝ := (1 + zeta η) * (1 + 7 * zeta η ^ 2)

theorem Ze_bracket {η : ℝ} (h : ClosureStationary η) :
    1.0053082838 < Ze η ∧ Ze η < 1.0053082839 := by
  obtain ⟨a, b⟩ := zeta_rat h
  unfold Ze
  constructor <;> nlinarith [sq_nonneg (zeta η), mul_pos (by linarith : (0:ℝ) < zeta η) (by linarith : (0:ℝ) < zeta η)]

/-- u = −ln(1 − r). -/
def u (η : ℝ) : ℝ := -Real.log (1 - Real.exp (-7 * gshare η))

theorem u_bracket {η : ℝ} (h : ClosureStationary η) :
    rLo < u η ∧ u η < rHi * (1 + 10 ^ (-20 : ℤ)) := by
  obtain ⟨a, b⟩ := r_bracket h
  have hr0 : 0 ≤ Real.exp (-7 * gshare η) := (Real.exp_pos _).le
  unfold u
  generalize Real.exp (-7 * gshare η) = r at a b hr0 ⊢
  unfold rHi at b ⊢; unfold rLo at a
  have hr1 : r < 1 := by linarith
  obtain ⟨c1, c2⟩ := neglog_bounds hr0 hr1
  refine ⟨lt_of_lt_of_le a c1, lt_of_le_of_lt c2 ?_⟩
  have hp : 0 < 1 - r := by linarith
  rw [div_lt_iff₀ hp]
  norm_num
  nlinarith

def lamE : ℝ := 38615926744 / 10 ^ 23

/-- L_* = (3/2) Z_e λ_e u. -/
def Lstar (η : ℝ) : ℝ := 3/2 * Ze η * lamE * u η

/-- C05-63: L_* = 1.616253702·10⁻³⁵ m (to 10 significant digits). -/
theorem Lstar_value {η : ℝ} (h : ClosureStationary η) :
    1.6162537019e-35 < Lstar η ∧ Lstar η < 1.6162537029e-35 := by
  obtain ⟨z1, z2⟩ := Ze_bracket h
  obtain ⟨u1, u2⟩ := u_bracket h
  unfold Lstar lamE
  unfold rLo at u1; unfold rHi at u2; norm_num at u2
  have hz0 : 0 < Ze η := by linarith
  have hu0 : 0 < u η := by linarith
  constructor <;> nlinarith [mul_pos hz0 hu0]

/-- ħ = h/(2π). -/
def hbar : ℝ := 6.62607015e-34 / (2 * Real.pi)
def cLight : ℝ := 299792458
def meKg : ℝ := 9.1093837139e-31

/-- G_* = (9/4)(ħc/m_e²) Z_e² u². -/
def Gstar (η : ℝ) : ℝ := 9/4 * (hbar * cLight / meKg ^ 2) * Ze η ^ 2 * u η ^ 2

/-- C05-65: G_* ∈ (6.674289073, 6.674289090)·10⁻¹¹, i.e. −0.0729σ … −0.0727σ from
CODATA G = 6.67430(15)·10⁻¹¹ (the paper quotes −0.073σ). -/
theorem Gstar_value {η : ℝ} (h : ClosureStationary η) :
    6.674289073e-11 < Gstar η ∧ Gstar η < 6.674289090e-11 ∧
      -0.0729 < (Gstar η - 6.67430e-11) / 0.00015e-11 ∧
      (Gstar η - 6.67430e-11) / 0.00015e-11 < -0.0727 := by
  obtain ⟨z1, z2⟩ := Ze_bracket h
  obtain ⟨u1, u2⟩ := u_bracket h
  unfold rLo at u1; unfold rHi at u2; norm_num at u2
  have p1 := Real.pi_gt_d20; have p2 := Real.pi_lt_d20
  have hz0 : 0 < Ze η := by linarith
  have hu0 : 0 < u η := by linarith
  -- K = (9/4)(h c/m_e²)/(2π): bracket the π-dependent prefactor
  set P := 9/4 * (hbar * cLight / meKg ^ 2) with hP
  have hPv : 9/4 * (6.62607015e-34 * 299792458 / (9.1093837139e-31) ^ 2) / (2 * 3.14159265358979323847) < P ∧
      P < 9/4 * (6.62607015e-34 * 299792458 / (9.1093837139e-31) ^ 2) / (2 * 3.14159265358979323846) := by
    rw [hP]; unfold hbar cLight meKg
    have hpi : 0 < Real.pi := Real.pi_pos
    constructor
    · rw [show 9 / 4 * (6.62607015e-34 / (2 * Real.pi) * 299792458 / (9.1093837139e-31 : ℝ) ^ 2) =
          9 / 4 * (6.62607015e-34 * 299792458 / (9.1093837139e-31) ^ 2) / (2 * Real.pi) by ring]
      apply div_lt_div_of_pos_left (by norm_num) (by positivity) (by linarith)
    · rw [show 9 / 4 * (6.62607015e-34 / (2 * Real.pi) * 299792458 / (9.1093837139e-31 : ℝ) ^ 2) =
          9 / 4 * (6.62607015e-34 * 299792458 / (9.1093837139e-31) ^ 2) / (2 * Real.pi) by ring]
      apply div_lt_div_of_pos_left (by norm_num) (by norm_num) (by linarith)
  obtain ⟨P1, P2⟩ := hPv
  have hP0 : 0 < P := lt_trans (by norm_num) P1
  have hG : Gstar η = P * (Ze η * u η) ^ 2 := by unfold Gstar; rw [← hP]; ring
  have hzu1 : 1.0053082838 * (27755723378 / 10 ^ 33) < Ze η * u η := by nlinarith
  have hzu2 : Ze η * u η < 1.0053082839 * (27755723381 / 10 ^ 33 * (1 + 1 / 10 ^ 20)) := by
    have := mul_lt_mul'' z2 u2 hz0.le hu0.le
    norm_num at this ⊢; linarith
  have s1 := mul_lt_mul'' hzu1 hzu1 (by norm_num) (by norm_num)
  have s2 := mul_lt_mul'' hzu2 hzu2 (by positivity) (by positivity)
  rw [← sq, ← sq] at s1 s2
  have g1 : 6.674289073e-11 < Gstar η := by
    rw [hG]; refine lt_of_lt_of_le ?_ (mul_le_mul P1.le s1.le (by positivity) hP0.le)
    norm_num
  have g2 : Gstar η < 6.674289090e-11 := by
    rw [hG]; refine lt_of_le_of_lt (mul_le_mul P2.le s2.le (by positivity) (by norm_num)) ?_
    norm_num
  refine ⟨g1, g2, ?_, ?_⟩
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-- C05-63: L_*/ℓ_P − 1 ∈ (−8.25, −8.10)·10⁻⁷ with ℓ_P = √(ħG/c³), G = 6.67430e-11
(the paper quotes 8.2·10⁻⁷). -/
def lP : ℝ := Real.sqrt (hbar * 6.67430e-11 / cLight ^ 3)

theorem Lstar_planck {η : ℝ} (h : ClosureStationary η) :
    -8.25e-7 < Lstar η / lP - 1 ∧ Lstar η / lP - 1 < -8.10e-7 := by
  obtain ⟨L1, L2⟩ := Lstar_value h
  have p1 := Real.pi_gt_d20; have p2 := Real.pi_lt_d20
  have hpi : 0 < Real.pi := Real.pi_pos
  have harg : 0 < hbar * 6.67430e-11 / cLight ^ 3 := by unfold hbar cLight; positivity
  have hlP : 0 < lP := Real.sqrt_pos.mpr harg
  -- bracket lP² = h G/(2π c³)
  have hsq : lP ^ 2 = hbar * 6.67430e-11 / cLight ^ 3 := Real.sq_sqrt harg.le
  set A : ℝ := 6.62607015e-34 * 6.67430e-11 / (2 * 299792458 ^ 3) with hA
  have hl2 : lP ^ 2 = A / Real.pi := by rw [hsq, hA]; unfold hbar cLight; field_simp
  -- lP ∈ (1.6162550244e-35, 1.6162550245e-35)
  have lo : (1.6162550243e-35:ℝ) < lP := by
    rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.6162550243e-35)]
    apply Real.sqrt_lt_sqrt (by norm_num)
    rw [← hsq, hl2, lt_div_iff₀ hpi, hA]; nlinarith
  have hi : lP < 1.6162550245e-35 := by
    rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.6162550245e-35)]
    apply Real.sqrt_lt_sqrt (by positivity)
    rw [← hsq, hl2, div_lt_iff₀ hpi, hA]; nlinarith
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hlP]; nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hlP]; nlinarith

end Entropic.AppCDE

namespace Entropic.AppCDE
open Entropic.FiniteModel Entropic.ClosureRoot Entropic.Spine

/-- C01-06 baseline: L_*⁽⁰⁾ = (3/2)λ_e u ∈ (1.60771946, 1.60771948)·10⁻³⁵ m (before Z_e). -/
theorem L0_value {η : ℝ} (h : ClosureStationary η) :
    1.60771946e-35 < 3/2 * lamE * u η ∧ 3/2 * lamE * u η < 1.60771948e-35 := by
  obtain ⟨u1, u2⟩ := u_bracket h
  unfold rLo at u1; unfold rHi at u2; norm_num at u2
  unfold lamE; constructor <;> nlinarith

/-- C01-09: with m_P = √(ħc/G_*), m_e/m_P = (3/2)Z_e u = −(3/2)Z_e ln(1 − e^{−7g}) ≈ 4.18546·10⁻²³. -/
theorem electron_planck_ratio {η : ℝ} (h : ClosureStationary η) :
    meKg / Real.sqrt (hbar * cLight / Gstar η) = 3/2 * Ze η * u η ∧
      4.18545e-23 < 3/2 * Ze η * u η ∧ 3/2 * Ze η * u η < 4.18547e-23 := by
  obtain ⟨z1, z2⟩ := Ze_bracket h
  obtain ⟨u1, u2⟩ := u_bracket h
  unfold rLo at u1; unfold rHi at u2; norm_num at u2
  have hz : 0 < Ze η := by linarith
  have hu : 0 < u η := by linarith
  have hħ : 0 < hbar := by unfold hbar; have := Real.pi_pos; positivity
  have hc : 0 < cLight := by unfold cLight; norm_num
  have hm : 0 < meKg := by unfold meKg; norm_num
  refine ⟨?_, by nlinarith [mul_pos hz hu], by nlinarith [mul_pos hz hu]⟩
  have hx : hbar * cLight / Gstar η = (meKg / (3/2 * Ze η * u η)) ^ 2 := by
    unfold Gstar; field_simp; ring
  rw [hx, Real.sqrt_sq (by positivity)]
  field_simp

/-- C01-10: ln²(1 − x)/x² → 1 as x → 0⁺ (the e^{−14g} hierarchy is the leading factor). -/
theorem log_sq_ratio :
    Filter.Tendsto (fun x : ℝ => Real.log (1 - x) ^ 2 / x ^ 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have key : Filter.Tendsto (fun x : ℝ => -Real.log (1 - x) / x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    refine ⟨min (1/2) (ε / 2), by positivity, fun x hx hdx => ?_⟩
    have hx0 : 0 < x := hx
    rw [Real.dist_eq, sub_zero, abs_of_pos hx0] at hdx
    have hx1 : x ≤ 1/2 := le_trans hdx.le (min_le_left _ _)
    obtain ⟨a, b, -⟩ := anchor_expansion hx0 hx1
    rw [Real.dist_eq, abs_lt]
    constructor <;> nlinarith [min_le_right (1/2) (ε / 2)]
  have := key.pow 2
  simp only [one_pow] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [div_pow, neg_sq]

/-- C01-40: replacing Σ_ret = 65/9 by 7, 23/3 or 8 moves J_ren by +0.141%, −0.281%, −0.490%
(all below 0.5%). -/
theorem Jren_sensitivity {η : ℝ} (h : ClosureStationary η) :
    let J := 2 * η / 9
    let R := fun s' : ℝ => (J / (1 + J * s')) / (J / (1 + J * (65/9))) - 1
    0.00140 < R 7 ∧ R 7 < 0.00142 ∧ -0.00282 < R (23/3) ∧ R (23/3) < -0.00280 ∧
      -0.00491 < R 8 ∧ R 8 < -0.00489 := by
  intro J R
  obtain ⟨a, b⟩ := eta_bracket h
  have hJ : 0 < J := by simp only [J]; linarith
  have e : ∀ s' : ℝ, 0 < 1 + J * s' → R s' = (1 + J * (65/9)) / (1 + J * s') - 1 := by
    intro s' hs; simp only [R]; field_simp
  rw [e 7 (by positivity), e (23/3) (by positivity), e 8 (by positivity)]
  have hJl : 0.0066370764 < J := by simp only [J]; linarith
  have hJu : J < 0.0066370766 := by simp only [J]; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (rw [lt_sub_iff_add_lt, lt_div_iff₀ (by positivity)]; nlinarith)
    | (rw [sub_lt_iff_lt_add, div_lt_iff₀ (by positivity)]; nlinarith)

/-- C01-12 (muon and G parts): with Z_e = 1, G_*⁽⁰⁾ = G_*/Z_e² lies 1.0534% below CODATA G and the
length uplift √(G/G_*⁽⁰⁾) − 1 is 0.5309%; the shell value 1440/7 sits 0.51236% below
the CODATA muon ratio 206.7682827. -/
theorem residuals {η : ℝ} (h : ClosureStationary η) :
    -0.010536 < Gstar η / Ze η ^ 2 / 6.67430e-11 - 1 ∧ Gstar η / Ze η ^ 2 / 6.67430e-11 - 1 < -0.010532 ∧
      (0.0051235 : ℝ) < 206.7682827 / (1440 / 7) - 1 ∧ (206.7682827 : ℝ) / (1440 / 7) - 1 < 0.0051237 := by
  obtain ⟨g1, g2, -, -⟩ := Gstar_value h
  obtain ⟨z1, z2⟩ := Ze_bracket h
  have hz : 0 < Ze η ^ 2 := by positivity
  have hz1 : (1.0053082838:ℝ) ^ 2 < Ze η ^ 2 := pow_lt_pow_left₀ z1 (by norm_num) (by norm_num)
  have hz2 : Ze η ^ 2 < (1.0053082839:ℝ) ^ 2 := pow_lt_pow_left₀ z2 (by linarith) (by norm_num)
  refine ⟨?_, ?_, by norm_num, by norm_num⟩
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ (by norm_num), lt_div_iff₀ hz]; nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ (by norm_num), div_lt_iff₀ hz]; nlinarith

end Entropic.AppCDE

namespace Entropic.AppCDE
open Entropic.FiniteModel Entropic.ClosureRoot

/-- Abstract form: for 0 < r ≤ 10⁻²⁰ and 1 ≤ Z ≤ 2, with A = −ln(1 − rZ), B = −ln(1 − r),
A/(ZB) − 1 lies within 30r² of r(Z − 1)/2. -/
theorem event_additive_gap {r Z : ℝ} (hr : 0 < r) (hr1 : r ≤ 1e-20) (hZ1 : 1 ≤ Z) (hZ2 : Z ≤ 2) :
    |(-Real.log (1 - r * Z)) / (Z * (-Real.log (1 - r))) - 1 - r * (Z - 1) / 2| ≤ 30 * r ^ 2 := by
  have hx : 0 < r * Z := by positivity
  have hx1 : r * Z ≤ 1/2 := by nlinarith
  have hr2 : r ≤ 1/2 := by linarith
  have hA := neglog_second hx.le hx1
  have hBb := neglog_second hr.le hr2
  obtain ⟨b1, -⟩ := neglog_bounds hr.le (by linarith)
  set A := -Real.log (1 - r * Z)
  set B := -Real.log (1 - r)
  set α := A - r * Z - (r * Z) ^ 2 / 2 with hα
  set β := B - r - r ^ 2 / 2 with hβ
  have hB : 0 < B := lt_of_lt_of_le hr b1
  have hZB : 0 < Z * B := by positivity
  have hZBr : r ≤ Z * B := by nlinarith
  have key : A / (Z * B) - 1 - r * (Z - 1) / 2 =
      (α - Z * β - r ^ 3 * Z * (Z - 1) / 4 - r * Z * (Z - 1) * β / 2) / (Z * B) := by
    rw [hα, hβ]; field_simp; ring
  rw [key, abs_div, abs_of_pos hZB, div_le_iff₀ hZB]
  have r3 : 0 < r ^ 3 := by positivity
  have hα' : |α| ≤ 16 * r ^ 3 := by
    refine le_trans hA ?_
    have : (r * Z) ^ 3 ≤ r ^ 3 * 8 := by
      rw [mul_pow]
      have : Z ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (by linarith) hZ2 3
      exact mul_le_mul_of_nonneg_left (by norm_num at this ⊢; linarith) r3.le
    linarith
  have hβ' : |β| ≤ 2 * r ^ 3 := hBb
  have t1 : |Z * β| ≤ 4 * r ^ 3 := by
    rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < Z)]; nlinarith [abs_nonneg β]
  have t2 : |r ^ 3 * Z * (Z - 1) / 4| ≤ r ^ 3 := by
    rw [abs_of_nonneg (by have h1 : 0 ≤ Z - 1 := (by linarith); positivity)]
    nlinarith [mul_le_mul hZ2 (by linarith : Z - 1 ≤ 1) (by linarith) (by linarith)]
  have t3 : |r * Z * (Z - 1) * β / 2| ≤ r ^ 3 := by
    rw [abs_div, abs_mul, abs_of_nonneg (by have h1 : 0 ≤ Z - 1 := (by linarith); positivity),
      abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have hzz : r * Z * (Z - 1) ≤ 2 * r := by nlinarith
    have : r * Z * (Z - 1) * |β| ≤ 2 * r * (2 * r ^ 3) :=
      mul_le_mul hzz hβ' (abs_nonneg _) (by positivity)
    nlinarith
  calc |α - Z * β - r ^ 3 * Z * (Z - 1) / 4 - r * Z * (Z - 1) * β / 2|
      ≤ |α| + |Z * β| + |r ^ 3 * Z * (Z - 1) / 4| + |r * Z * (Z - 1) * β / 2| := by
        have := abs_sub (α - Z * β - r ^ 3 * Z * (Z - 1) / 4) (r * Z * (Z - 1) * β / 2)
        have := abs_sub (α - Z * β) (r ^ 3 * Z * (Z - 1) / 4)
        have := abs_sub α (Z * β)
        linarith
    _ ≤ 22 * r ^ 3 := by linarith
    _ ≤ 30 * r ^ 2 * (Z * B) := by nlinarith [mul_le_mul_of_nonneg_left hZBr (by positivity : (0:ℝ) ≤ 30 * r ^ 2)]

/-- C01-58: the event-level energy −(3ħ/2τ)ln(1 − rZ_e) and the additive form
−(3ħ/2τ)Z_e ln(1 − r) differ in relative terms by r(Z_e − 1)/2 = 7.367·10⁻²⁶. -/
theorem event_energy_difference {η : ℝ} (h : ClosureStationary η) :
    let r := Real.exp (-7 * gshare η)
    7.366e-26 < (-Real.log (1 - r * Ze η)) / (Ze η * (-Real.log (1 - r))) - 1 ∧
      (-Real.log (1 - r * Ze η)) / (Ze η * (-Real.log (1 - r))) - 1 < 7.368e-26 := by
  intro r
  obtain ⟨a, b⟩ := r_bracket h
  obtain ⟨z1, z2⟩ := Ze_bracket h
  unfold rLo at a; unfold rHi at b
  have hr : 0 < r := Real.exp_pos _
  have g := abs_le.mp (event_additive_gap hr (by linarith) (by linarith) (by linarith))
  obtain ⟨g1, g2⟩ := g
  have m1 : (27755723378 / 10 ^ 33 : ℝ) * (1.0053082838 - 1) / 2 < r * (Ze η - 1) / 2 := by
    have : (0:ℝ) < 1.0053082838 - 1 := by norm_num
    nlinarith
  have m2 : r * (Ze η - 1) / 2 < (27755723381 / 10 ^ 33 : ℝ) * (1.0053082839 - 1) / 2 := by
    nlinarith
  have s : r ^ 2 < 1e-44 := by nlinarith
  constructor
  · have : (7.366e-26 : ℝ) + 10 * 1e-44 < 27755723378 / 10 ^ 33 * (1.0053082838 - 1) / 2 := by norm_num
    linarith
  · have : (27755723381 / 10 ^ 33 : ℝ) * (1.0053082839 - 1) / 2 + 30 * 1e-44 < 7.368e-26 := by norm_num
    linarith

end Entropic.AppCDE
