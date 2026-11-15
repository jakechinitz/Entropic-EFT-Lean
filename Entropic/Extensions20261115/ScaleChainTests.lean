import Entropic.AppCDE.ElectronNumerics
import Entropic.Spine
import Mathlib.Tactic

/-!
# Scale-chain coefficients and forward tests (Sections 13.5 and 27)

At the closure root, with the certified brackets of `Entropic.Spine` and `Entropic.AppCDE`:

* treating the electron return coefficient as a continuous variable `n` in `1 + nζ_*²`, the measured `G`
  selects `n ∈ (7.02, 7.04)` and its one-standard-deviation interval is `(6.59…6.61, 7.45…7.47)`:
  `n = 7.03 ± 0.43` (`return_coefficient_fit`);
* every integer `n ≠ 7` with `n ≥ −200` lies more than two standard deviations of `G` away
  (`return_integer_unique`), the neighbours at `−2.4σ` and `+2.3σ` (`return_neighbours`) and the absent
  return at `−16.4σ` (`return_absent`);
* treating the second-shell coefficient as a continuous variable `q` in `1 + qζ_*`, the tau mass selects
  `q ∈ (0.286, 0.288)` with interval `(0.276…0.278, 0.296…0.298)`: `q = 0.287 ± 0.010`
  (`second_shell_fit`);
* among nonnegative rationals `a/b` with `b ≤ 11`, `2/7` alone lies within one standard deviation of
  the tau mass (`second_shell_rational_unique`), its neighbours at `−1.44σ` and `+1.32σ`
  (`second_shell_neighbours`);
* the present muon ratio lies `2.46…2.47 × 10⁻⁶` above the selected value, which is `5.35` standard
  deviations at a tenfold smaller uncertainty (`muon_forward`).

Measured inputs (literals): CODATA 2022 `G = 6.67430(15)·10⁻¹¹`, `m_μ/m_e = 206.7682827(46)`,
`m_e c² = 0.51099895069 MeV`; PDG `m_τ c² = 1776.93(9) MeV`. The forecast probabilities of Section 27
(Gaussian model) are not formalized.
-/

noncomputable section
namespace Entropic.Extensions20261115.ScaleChainTests
open Entropic.FiniteModel Entropic.Spine Entropic.AppCDE

/-- Bracket of `ζ_*²` from `AppCDE.zeta_rat`. -/
def wl : ℝ := 0.005123584484 ^ 2
def wu : ℝ := 0.005123584486 ^ 2

theorem zeta_sq_bracket {η : ℝ} (h : ClosureStationary η) : wl < zeta η ^ 2 ∧ zeta η ^ 2 < wu := by
  obtain ⟨a, b⟩ := zeta_rat h
  exact ⟨pow_lt_pow_left₀ a (by norm_num) (by norm_num), pow_lt_pow_left₀ b (by linarith) (by norm_num)⟩

/-! ### Electron return coefficient -/

/-- `G_*` with the electron return factor `1 + nζ_*²` in place of `1 + 7ζ_*²`. -/
def Gn (η n : ℝ) : ℝ := Gstar η * ((1 + n * zeta η ^ 2) / (1 + 7 * zeta η ^ 2)) ^ 2

theorem Gn_seven (η : ℝ) : Gn η 7 = Gstar η := by
  unfold Gn
  rw [div_self (by positivity), one_pow, mul_one]

theorem Gn_bracket {η : ℝ} (h : ClosureStationary η) {n : ℝ} (hn : 0 ≤ n) :
    6.674289073e-11 * ((1 + n * wl) / (1 + 7 * wu)) ^ 2 < Gn η n ∧
      Gn η n < 6.674289090e-11 * ((1 + n * wu) / (1 + 7 * wl)) ^ 2 := by
  obtain ⟨g1, g2, -, -⟩ := Gstar_value h
  obtain ⟨w1, w2⟩ := zeta_sq_bracket h
  have hwl0 : (0 : ℝ) < wl := by norm_num [wl]
  have hw0 : 0 < zeta η ^ 2 := lt_trans hwl0 w1
  have hr1 : (1 + n * wl) / (1 + 7 * wu) ≤ (1 + n * zeta η ^ 2) / (1 + 7 * zeta η ^ 2) := by
    rw [div_le_div_iff₀ (by norm_num [wu]) (by positivity)]
    nlinarith [mul_nonneg hn (sub_nonneg.mpr w1.le), mul_nonneg hn hwl0.le]
  have hr2 : (1 + n * zeta η ^ 2) / (1 + 7 * zeta η ^ 2) ≤ (1 + n * wu) / (1 + 7 * wl) := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num [wl])]
    nlinarith [mul_nonneg hn (sub_nonneg.mpr w2.le), mul_nonneg hn hw0.le]
  have hl0 : 0 < (1 + n * wl) / (1 + 7 * wu) := by
    have : (0 : ℝ) < 1 + 7 * wu := by norm_num [wu]
    have : (0 : ℝ) < 1 + n * wl := by nlinarith [mul_nonneg hn hwl0.le]
    positivity
  have hs1 := pow_le_pow_left₀ hl0.le hr1 2
  have hs2 := pow_le_pow_left₀ (le_trans hl0.le hr1) hr2 2
  have hG0 : 0 < Gstar η := lt_trans (by norm_num) g1
  unfold Gn
  constructor
  · exact mul_lt_mul g1 hs1 (by positivity) hG0.le
  · exact mul_lt_mul g2 hs2 (pow_pos (lt_of_lt_of_le hl0 hr1) 2) (by norm_num)

/-- Section 13.5: as a continuous variable the return coefficient selected by the measured `G` lies in
`(7.02, 7.04)`, and the values selected by `G ∓ σ_G` lie in `(6.59, 6.61)` and `(7.45, 7.47)`:
`n = 7.03 ± 0.43`. (`Gn` is increasing in `n`, `Gn_mono`.) -/
theorem return_coefficient_fit {η : ℝ} (h : ClosureStationary η) :
    Gn η 7.02 < 6.67430e-11 ∧ 6.67430e-11 < Gn η 7.04 ∧
      Gn η 6.59 < 6.67430e-11 - 0.00015e-11 ∧ 6.67430e-11 - 0.00015e-11 < Gn η 6.61 ∧
      Gn η 7.45 < 6.67430e-11 + 0.00015e-11 ∧ 6.67430e-11 + 0.00015e-11 < Gn η 7.47 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_trans (Gn_bracket h (by norm_num)).2 (by norm_num [wl, wu])
  · exact lt_trans (by norm_num [wl, wu]) (Gn_bracket h (by norm_num)).1
  · exact lt_trans (Gn_bracket h (by norm_num)).2 (by norm_num [wl, wu])
  · exact lt_trans (by norm_num [wl, wu]) (Gn_bracket h (by norm_num)).1
  · exact lt_trans (Gn_bracket h (by norm_num)).2 (by norm_num [wl, wu])
  · exact lt_trans (by norm_num [wl, wu]) (Gn_bracket h (by norm_num)).1

/-- `Gn` is nondecreasing in `n` while `1 + nζ_*² ≥ 0`. -/
theorem Gn_mono {η : ℝ} (h : ClosureStationary η) {n n' : ℝ} (h0 : 0 ≤ 1 + n * zeta η ^ 2)
    (hnn : n ≤ n') : Gn η n ≤ Gn η n' := by
  obtain ⟨g1, -, -, -⟩ := Gstar_value h
  have hG0 : 0 < Gstar η := lt_trans (by norm_num) g1
  have hw0 : 0 ≤ zeta η ^ 2 := sq_nonneg _
  have hden : 0 < 1 + 7 * zeta η ^ 2 := by positivity
  unfold Gn
  apply mul_le_mul_of_nonneg_left _ hG0.le
  apply pow_le_pow_left₀ (div_nonneg h0 hden.le)
  apply div_le_div_of_nonneg_right _ hden.le
  nlinarith [mul_le_mul_of_nonneg_right hnn hw0]

/-- Section 13.5: the integer neighbours of seven sit at `−2.4σ` and `+2.3σ` of the measured `G`. -/
theorem return_neighbours {η : ℝ} (h : ClosureStationary η) :
    Gn η 6 < 6.67430e-11 - 2.40 * 0.00015e-11 ∧ 6.67430e-11 - 2.42 * 0.00015e-11 < Gn η 6 ∧
      6.67430e-11 + 2.25 * 0.00015e-11 < Gn η 8 ∧ Gn η 8 < 6.67430e-11 + 2.27 * 0.00015e-11 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact lt_trans (Gn_bracket h (by norm_num)).2 (by norm_num [wl, wu])
  · exact lt_trans (by norm_num [wl, wu]) (Gn_bracket h (by norm_num)).1
  · exact lt_trans (by norm_num [wl, wu]) (Gn_bracket h (by norm_num)).1
  · exact lt_trans (Gn_bracket h (by norm_num)).2 (by norm_num [wl, wu])

/-- Section 13.5: with no electron return (`n = 0`) the induced coefficient sits at `−16.4σ`. -/
theorem return_absent {η : ℝ} (h : ClosureStationary η) :
    6.67430e-11 - 16.43 * 0.00015e-11 < Gn η 0 ∧ Gn η 0 < 6.67430e-11 - 16.41 * 0.00015e-11 := by
  constructor
  · exact lt_trans (by norm_num [wl, wu]) (Gn_bracket h (by norm_num)).1
  · exact lt_trans (Gn_bracket h (by norm_num)).2 (by norm_num [wl, wu])

/-- Section 13.5, Appendix L: among the integers `n ≥ −200`, seven is the only return coefficient within
two standard deviations of the measured `G`. -/
theorem return_integer_unique {η : ℝ} (h : ClosureStationary η) (n : ℤ) (hlo : -200 ≤ n) (hne : n ≠ 7) :
    2 * 0.00015e-11 < |Gn η n - 6.67430e-11| := by
  obtain ⟨a6, -, a8, -⟩ := return_neighbours h
  obtain ⟨w1, w2⟩ := zeta_sq_bracket h
  have hw0 : 0 ≤ zeta η ^ 2 := sq_nonneg _
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hn6 : (n : ℝ) ≤ 6 := by exact_mod_cast Int.lt_add_one_iff.mp (by omega : n < 6 + 1)
    have hnl : (-200 : ℝ) ≤ n := by exact_mod_cast hlo
    have h0 : 0 ≤ 1 + (n : ℝ) * zeta η ^ 2 := by
      have hwu : wu < 1 / 200 := by norm_num [wu]
      nlinarith [mul_le_mul_of_nonneg_right hnl hw0]
    have hm := Gn_mono h h0 hn6
    rw [abs_of_neg (by linarith)]; linarith
  · have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast (by omega : (8 : ℤ) ≤ n)
    have hm := Gn_mono h (n := 8) (n' := n) (by positivity) hn8
    rw [abs_of_pos (by linarith)]; linarith

/-! ### Second-shell coefficient -/

/-- `m_τ/m_e` with the second-shell factor `1 + qζ_*` in place of `1 + (2/7)ζ_*`. -/
def tauQ (η q : ℝ) : ℝ := 720 ^ 2 * (2/7) ^ 4 * (1 + zeta η) * (1 + q * zeta η)

theorem tauQ_two_sevenths (η : ℝ) : tauQ η (2/7) = tauRatio η := by
  unfold tauQ tauRatio; ring

theorem tauQ_bracket {η : ℝ} (h : ClosureStationary η) {q : ℝ} (hq : 0 ≤ q) :
    720 ^ 2 * (2/7) ^ 4 * (1 + 0.005123584484) * (1 + q * 0.005123584484) < tauQ η q ∧
      tauQ η q < 720 ^ 2 * (2/7) ^ 4 * (1 + 0.005123584486) * (1 + q * 0.005123584486) := by
  obtain ⟨a, b⟩ := zeta_rat h
  have hz0 : 0 < zeta η := lt_trans (by norm_num) a
  unfold tauQ
  constructor
  · have h1 : (1 + 0.005123584484) * (1 + q * 0.005123584484) < (1 + zeta η) * (1 + q * zeta η) := by
      apply mul_lt_mul (by linarith) (by nlinarith) (by positivity) (by positivity)
    nlinarith
  · have h1 : (1 + zeta η) * (1 + q * zeta η) < (1 + 0.005123584486) * (1 + q * 0.005123584486) := by
      apply mul_lt_mul (by linarith) (by nlinarith) (by positivity) (by positivity)
    nlinarith

/-- `tauQ` is increasing in `q`. -/
theorem tauQ_mono {η : ℝ} (h : ClosureStationary η) {q q' : ℝ} (hqq : q ≤ q') : tauQ η q ≤ tauQ η q' := by
  have hz0 := zeta_pos h
  unfold tauQ
  have : q * zeta η ≤ q' * zeta η := mul_le_mul_of_nonneg_right hqq hz0.le
  have hB : (0 : ℝ) < 720 ^ 2 * (2/7) ^ 4 * (1 + zeta η) := by positivity
  nlinarith

/-- Section 13.5: as a continuous variable the second-shell coefficient selected by the measured tau
mass lies in `(0.286, 0.288)`, and the values selected by `m_τ ∓ σ` lie in `(0.276, 0.278)` and
`(0.296, 0.298)`: `q = 0.287 ± 0.010`. -/
theorem second_shell_fit {η : ℝ} (h : ClosureStationary η) :
    tauQ η 0.286 < 1776.93 / 0.51099895069 ∧ 1776.93 / 0.51099895069 < tauQ η 0.288 ∧
      tauQ η 0.276 < (1776.93 - 0.09) / 0.51099895069 ∧ (1776.93 - 0.09) / 0.51099895069 < tauQ η 0.278 ∧
      tauQ η 0.296 < (1776.93 + 0.09) / 0.51099895069 ∧ (1776.93 + 0.09) / 0.51099895069 < tauQ η 0.298 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_trans (tauQ_bracket h (by norm_num)).2 (by norm_num)
  · exact lt_trans (by norm_num) (tauQ_bracket h (by norm_num)).1
  · exact lt_trans (tauQ_bracket h (by norm_num)).2 (by norm_num)
  · exact lt_trans (by norm_num) (tauQ_bracket h (by norm_num)).1
  · exact lt_trans (tauQ_bracket h (by norm_num)).2 (by norm_num)
  · exact lt_trans (by norm_num) (tauQ_bracket h (by norm_num)).1

/-- A nonnegative rational `a/b` with `b ≤ 11` other than `2/7` is at most `3/11` or at least `3/10`. -/
theorem farey_neighbours (a b : ℕ) (hb : 1 ≤ b) (hb11 : b ≤ 11) (hne : 7 * a ≠ 2 * b) :
    11 * a ≤ 3 * b ∨ 3 * b ≤ 10 * a := by omega

/-- Section 13.5: the two nearest rationals sit at `−1.44σ` (`3/11`) and `+1.32σ` (`3/10`) of the tau
mass, and `2/7` within `0.13σ`. -/
theorem second_shell_neighbours {η : ℝ} (h : ClosureStationary η) :
    tauQ η (3/11) < 1776.93 / 0.51099895069 - 1.43 * (0.09 / 0.51099895069) ∧
      1776.93 / 0.51099895069 - 1.44 * (0.09 / 0.51099895069) < tauQ η (3/11) ∧
      1776.93 / 0.51099895069 + 1.31 * (0.09 / 0.51099895069) < tauQ η (3/10) ∧
      tauQ η (3/10) < 1776.93 / 0.51099895069 + 1.32 * (0.09 / 0.51099895069) ∧
      |tauQ η (2/7) - 1776.93 / 0.51099895069| < 0.13 * (0.09 / 0.51099895069) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact lt_trans (tauQ_bracket h (by norm_num)).2 (by norm_num)
  · exact lt_trans (by norm_num) (tauQ_bracket h (by norm_num)).1
  · exact lt_trans (by norm_num) (tauQ_bracket h (by norm_num)).1
  · exact lt_trans (tauQ_bracket h (by norm_num)).2 (by norm_num)
  · obtain ⟨a, b⟩ := tauQ_bracket h (q := 2/7) (by norm_num)
    rw [abs_lt]
    constructor
    · exact lt_trans (by norm_num) (sub_lt_sub_right a _)
    · exact lt_trans (sub_lt_sub_right b _) (by norm_num)

/-- Section 13.5: among the nonnegative rationals `a/b` with denominator at most eleven (in particular
the forty-three in `[0,1]`), `2/7` alone lies within one standard deviation of the measured tau mass. -/
theorem second_shell_rational_unique {η : ℝ} (h : ClosureStationary η) (a b : ℕ) (hb : 1 ≤ b)
    (hb11 : b ≤ 11) (hne : 7 * a ≠ 2 * b) :
    0.09 / 0.51099895069 < |tauQ η ((a : ℝ) / b) - 1776.93 / 0.51099895069| := by
  obtain ⟨n1, -, n2, -, -⟩ := second_shell_neighbours h
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rcases farey_neighbours a b hb hb11 hne with hlo | hhi
  · have hq : (a : ℝ) / b ≤ 3 / 11 := by
      rw [div_le_div_iff₀ hbR (by norm_num)]; exact_mod_cast (by omega : a * 11 ≤ 3 * b)
    have hm := tauQ_mono h hq
    rw [abs_of_neg (by linarith)]; linarith
  · have hq : (3 : ℝ) / 10 ≤ (a : ℝ) / b := by
      rw [div_le_div_iff₀ (by norm_num) hbR]; exact_mod_cast (by omega : 3 * b ≤ a * 10)
    have hm := tauQ_mono h hq
    rw [abs_of_pos (by linarith)]; linarith

/-! ### Muon forward test -/

/-- Section 27: the present muon ratio `206.7682827` lies `2.46…2.47 × 10⁻⁶` above the selected value.
At a tenfold smaller uncertainty (`4.6 × 10⁻⁷`) an unchanged central value would lie `5.35` standard
deviations away. -/
theorem muon_forward {η : ℝ} (h : ClosureStationary η) :
    2.46e-6 < 206.7682827 - muRatio η ∧ 206.7682827 - muRatio η < 2.47e-6 ∧
      5.34 < (206.7682827 - muRatio η) / 0.00000046 ∧
      (206.7682827 - muRatio η) / 0.00000046 < 5.37 := by
  obtain ⟨a, b⟩ := muRatio_bracket h
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

end Entropic.Extensions20261115.ScaleChainTests
