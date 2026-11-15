import Entropic.AppCDE.Calibration
import Mathlib.Tactic

/-!
# The chain constant in the event-volume calibration (Appendix C.8)

`Entropic.AppCDE.Calibration` proves `G₀/G_* = C^{1/3} m₄^{8/3}` and locates the equality root in
`(2.3240, 2.3242)`. This file evaluates the calibration at the computed chain constants quoted in C.8:

* at the free-exponent fit `m₄ = 2.3219`: `v_ev = 3.8046`, `a_reg = 2.5273`, `A_ch = 2.7657`,
  `G₀/G_* = 0.9975` (`calibration_23219`);
* at the fixed-exponent fits `m₄ = 2.32163`, `2.32235`, `2.32103`: `G₀/G_* = 0.99719`, `0.99802`,
  `0.99651` (`calibration_fixed_exponent`);
* every `m₄ ≤ 2.3240` gives `G₀ < G_*` (`below_equality`).

The values of `m₄` themselves are results of the longest-chain growth runs recorded in
`02 Research/Forward tests 2026-11-09` and are inputs here.
-/

noncomputable section
namespace Entropic.Extensions20261115.ChainConstant
open Real Entropic.AppCDE.Calibration

private theorem cube_lt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ 3 < y ^ 3) : x < y :=
  (pow_lt_pow_iff_left₀ hx hy (by norm_num)).mp h

/-- C.8 at `m₄ = 2.3219`: `v_ev/L_*⁴ = 3.8046`, `a_reg/L_* = 2.5273`, `A_ch/L_*² = 2.7657`,
`G₀/G_* = 0.9975`. -/
theorem calibration_23219 :
    3.80463 < vev 2.3219 ∧ vev 2.3219 < 3.80464 ∧
      2.52725 < areg 2.3219 ∧ areg 2.3219 < 2.52727 ∧
      2.76566 < Ach 2.3219 ∧ Ach 2.3219 < 2.76568 ∧
      0.99750 < G0 2.3219 ∧ G0 2.3219 < 0.99751 := by
  have pl := Real.pi_gt_d20; have ph := Real.pi_lt_d20
  obtain ⟨s2l, s2h⟩ := sqrt2_bounds
  obtain ⟨s3l, s3h⟩ := sqrt3_bounds
  have v1 : 3.804632 < vev 2.3219 := by unfold vev; nlinarith
  have v2 : vev 2.3219 < 3.804633 := by unfold vev; nlinarith
  have ha := areg_cube (m := 2.3219) (by norm_num)
  have hap := areg_pos (m := 2.3219) (by norm_num)
  have a1 : 2.527258 < areg 2.3219 := by
    apply cube_lt (by norm_num) hap.le; rw [ha]; nlinarith
  have a2 : areg 2.3219 < 2.527259 := by
    apply cube_lt hap.le (by norm_num); rw [ha]; nlinarith
  have A1 : 2.765666 < Ach 2.3219 := by unfold Ach; nlinarith
  have A2 : Ach 2.3219 < 2.765669 := by unfold Ach; nlinarith
  have ll := Real.log_two_gt_d9; have lh := Real.log_two_lt_d9
  have hl : 0 < 4 * Real.log 2 := by positivity
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩
  · unfold G0; rw [lt_div_iff₀ hl]; nlinarith
  · unfold G0; rw [div_lt_iff₀ hl]; nlinarith

/-- `G₀/G_*` from the cube form, for a rational bracket check. -/
private theorem G0_between {m lo hi : ℝ} (hm : 0 < m) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (h1 : lo ^ 3 < 0.0011748840 * m ^ 8) (h2 : 0.0011748855 * m ^ 8 < hi ^ 3) :
    lo < G0 m ∧ G0 m < hi := by
  obtain ⟨c1, c2⟩ := C3_bounds
  have hm8 : 0 < m ^ 8 := by positivity
  have hG := (G0_pos hm).le
  constructor
  · apply cube_lt hlo hG; rw [G0_cube hm]; nlinarith
  · apply cube_lt hG hhi; rw [G0_cube hm]; nlinarith

/-- C.8, fixed correction exponent: at `m₄ = 2.32163` (`p = 1.373`), `2.32235` (`p = 1.25`) and
`2.32103` (`p = 1.50`), `G₀/G_*` is `0.9972`, `0.9980` and `0.9965`. -/
theorem calibration_fixed_exponent :
    0.99719 < G0 2.32163 ∧ G0 2.32163 < 0.99720 ∧
      0.99801 < G0 2.32235 ∧ G0 2.32235 < 0.99803 ∧
      0.99650 < G0 2.32103 ∧ G0 2.32103 < 0.99652 := by
  obtain ⟨a1, a2⟩ := G0_between (m := 2.32163) (lo := 0.99719) (hi := 0.99720) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨b1, b2⟩ := G0_between (m := 2.32235) (lo := 0.99801) (hi := 0.99803) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c1, c2⟩ := G0_between (m := 2.32103) (lo := 0.99650) (hi := 0.99652) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨a1, a2, b1, b2, c1, c2⟩

/-- C.8: every chain constant at or below `2.3240` gives a bare coefficient below the induced one. -/
theorem below_equality {m : ℝ} (hm : 0 < m) (h : m ≤ 2.3240) : G0 m < 1 := by
  obtain ⟨r1, -⟩ := calibration_root
  rcases eq_or_lt_of_le h with he | hlt
  · rw [he]; exact r1
  · exact lt_trans (G0_strictMono hm (by norm_num : (0 : ℝ) < 2.3240) hlt) r1

end Entropic.Extensions20261115.ChainConstant
