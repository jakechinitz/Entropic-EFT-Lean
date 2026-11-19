import Mathlib

/-!
# One or two tilt polarizations (Appendix N.8)

The three exact responses of a rigid frame compared in the manuscript of 19 November 2026, with
`n_B(x) = 1/(eˣ − 1)`:

* one angle: `1 + n_B(x) = 1/(1 − e^{−x})` (`one_ladder`);
* sphere, both polarizations: `1 + 2 n_B(x) = (eˣ + 1)/(eˣ − 1) = coth(x/2)` (`two_ladders`);
* sphere, zero angular momentum about the field: `1 + 2 n_B(2x) = coth x` (`zero_m`);
* `deep_scale`: `2/√(g/a) = 1/√(g/(4a))`, so the deep-regime law `coth(x/2) ≃ 2/x` has scale `4a`.

The SPARC fits that select the single ladder are numerical results, not formalized.
-/

noncomputable section
namespace Entropic.Extensions20261119.Polarizations
open Real

def nB (x : ℝ) : ℝ := 1 / (Real.exp x - 1)

private lemma exp_sub_one_pos {x : ℝ} (hx : 0 < x) : 0 < Real.exp x - 1 := by
  have := (by have := Real.add_one_lt_exp hx.ne'; linarith : 1 < Real.exp x); linarith

theorem one_ladder {x : ℝ} (hx : 0 < x) : 1 + nB x = 1 / (1 - Real.exp (-x)) := by
  have h := exp_sub_one_pos hx; have he := Real.exp_pos x
  have hm : 1 - Real.exp (-x) ≠ 0 := by
    rw [Real.exp_neg]; intro h'; field_simp at h'; linarith
  unfold nB; rw [Real.exp_neg]; field_simp; ring

theorem two_ladders {x : ℝ} (hx : 0 < x) : 1 + 2 * nB x = (Real.exp x + 1) / (Real.exp x - 1) := by
  have h := exp_sub_one_pos hx; unfold nB; field_simp; ring

theorem two_ladders_coth {x : ℝ} (hx : 0 < x) :
    1 + 2 * nB x = Real.cosh (x / 2) / Real.sinh (x / 2) := by
  rw [two_ladders hx]
  have hs : 0 < Real.sinh (x / 2) := Real.sinh_pos_iff.mpr (by linarith)
  have h := exp_sub_one_pos hx
  rw [div_eq_div_iff h.ne' hs.ne', Real.cosh_eq, Real.sinh_eq]
  have e2 : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by rw [← Real.exp_add]; ring_nf
  have en : Real.exp (-(x / 2)) * Real.exp (x / 2) = 1 := by rw [← Real.exp_add]; simp
  rw [e2]; linear_combination (-(Real.exp (x / 2))) * en

theorem zero_m {x : ℝ} (hx : 0 < x) : 1 + 2 * nB (2 * x) = Real.cosh x / Real.sinh x := by
  have := two_ladders_coth (show 0 < 2 * x by linarith)
  rw [this]; ring_nf

theorem deep_scale {g a : ℝ} (hg : 0 < g) (ha : 0 < a) : 2 / √(g / a) = 1 / √(g / (4 * a)) := by
  have h1 : √(g / (4 * a)) = √(g / a) / 2 := by
    rw [show g / (4 * a) = (g / a) / 2 ^ 2 by ring, Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 2 ^ 2),
      Real.sqrt_sq (by norm_num)]
  have hs : 0 < √(g / a) := Real.sqrt_pos.mpr (by positivity)
  rw [h1]; field_simp

end Entropic.Extensions20261119.Polarizations
