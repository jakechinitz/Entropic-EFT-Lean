import Mathlib

/-!
# Certified enclosure of Watson's fcc constant in AGM form (C05-22, C11-12)

Watson's fcc integral has the closed form
`W_fcc = 3 Γ(1/3)⁶ / (2^(14/3) π⁴) = (√3/π²) K(sin 15°)²`, where `K` is the complete elliptic
integral of the first kind and `sin 15°` is the singular modulus `k₃`. Gauss's formula
`K(k) = π / (2 agm(1, k'))` with `k' = cos 15°` turns this into

  `W_fcc = √3 / (4 agm(1, cos 15°)²)`.

This file encloses the right-hand side using mathlib's `NNReal.agm` and its two-sided
bounds `(agmSequences x y n).1 ≤ agm x y ≤ (agmSequences x y n).2`. Three AGM steps
bracket the value to about sixteen digits; the theorem states fourteen.
-/

open NNReal Real

namespace Entropic.DiamondGreen

/-- `cos 15° = cos(π/12)`, the complementary singular modulus `k₃'`. -/
noncomputable def cos15 : ℝ≥0 :=
  ⟨Real.cos (π / 12), Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩⟩

/-- Watson's fcc constant in Gauss's AGM form, `√3 / (4 agm(1, cos 15°)²)`. -/
noncomputable def watsonAGM : ℝ := √3 / (4 * ((NNReal.agm 1 cos15 : ℝ≥0) : ℝ) ^ 2)

theorem cos15_eq : (cos15 : ℝ) = √((1 + √3 / 2) / 2) := by
  change Real.cos (π / 12) = _
  rw [show π / 12 = (π / 6) / 2 by ring,
    Real.cos_half (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]), Real.cos_pi_div_six]

private theorem sqrt_between {l h X : ℝ} (hl : 0 ≤ l) (hh : 0 ≤ h) (h1 : l ^ 2 ≤ X) (h2 : X ≤ h ^ 2) :
    l ≤ √X ∧ √X ≤ h := by
  refine ⟨?_, ?_⟩
  · calc l = √(l ^ 2) := (Real.sqrt_sq hl).symm
      _ ≤ √X := Real.sqrt_le_sqrt h1
  · calc √X ≤ √(h ^ 2) := Real.sqrt_le_sqrt h2
      _ = h := Real.sqrt_sq hh

private theorem sqrt_mul_between {l1 h1 l2 h2 l h x y : ℝ} (hl1 : 0 ≤ l1) (hl2 : 0 ≤ l2)
    (hx : l1 ≤ x ∧ x ≤ h1) (hy : l2 ≤ y ∧ y ≤ h2) (hl : 0 ≤ l) (hh : 0 ≤ h)
    (c1 : l ^ 2 ≤ l1 * l2) (c2 : h1 * h2 ≤ h ^ 2) : l ≤ √(x * y) ∧ √(x * y) ≤ h :=
  sqrt_between hl hh (c1.trans (mul_le_mul hx.1 hy.1 hl2 (hl1.trans hx.1)))
    ((mul_le_mul hx.2 hy.2 (hl2.trans hy.1) ((hl1.trans hx.1).trans hx.2)).trans c2)

/-- `√3` to 22 decimals. -/
theorem sqrt3_bounds :
    (1.7320508075688772935274 : ℝ) ≤ √3 ∧ √3 ≤ 1.7320508075688772935275 :=
  sqrt_between (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `cos 15°` to 22 decimals. -/
theorem cos15_bounds :
    (0.9659258262890682867497 : ℝ) ≤ cos15 ∧ (cos15 : ℝ) ≤ 0.9659258262890682867498 := by
  rw [cos15_eq]
  obtain ⟨s1, s2⟩ := sqrt3_bounds
  exact sqrt_between (by norm_num) (by norm_num)
    (le_trans (by norm_num) (by linarith : (1 + 1.7320508075688772935274 / 2) / 2 ≤ (1 + √3 / 2) / 2))
    (le_trans (by linarith : (1 + √3 / 2) / 2 ≤ (1 + 1.7320508075688772935275 / 2) / 2) (by norm_num))

/-- Three AGM steps bracket `agm(1, cos 15°)` to 18 digits. -/
theorem agm_bounds :
    (0.9828890828965786352391 : ℝ) ≤ (NNReal.agm 1 cos15 : ℝ) ∧
      (NNReal.agm 1 cos15 : ℝ) ≤ 0.982889082896578636217125 := by
  obtain ⟨c1, c2⟩ := cos15_bounds
  set c : ℝ := (cos15 : ℝ)
  -- step 0
  have e0g : ((agmSequences 1 cos15 0).1 : ℝ) = √(1 * c) := by simp [c]
  have e0a : ((agmSequences 1 cos15 0).2 : ℝ) = (1 + c) / 2 := by simp [c]
  have g0 : (0.9828152554214186019996 : ℝ) ≤ (agmSequences 1 cos15 0).1 ∧
      ((agmSequences 1 cos15 0).1 : ℝ) ≤ 0.9828152554214186019998 := by
    rw [e0g]
    exact sqrt_mul_between (l1 := 1) (h1 := 1) (by norm_num) (by norm_num) ⟨le_rfl, le_rfl⟩
      ⟨c1, c2⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have a0 : (1 + 0.9659258262890682867497) / 2 ≤ ((agmSequences 1 cos15 0).2 : ℝ) ∧
      ((agmSequences 1 cos15 0).2 : ℝ) ≤ (1 + 0.9659258262890682867498) / 2 := by
    rw [e0a]; constructor <;> linarith
  -- step 1
  have e1g : ((agmSequences 1 cos15 1).1 : ℝ) =
      √(((agmSequences 1 cos15 0).1 : ℝ) * (agmSequences 1 cos15 0).2) := by
    rw [agmSequences_succ']; simp
  have e1a : ((agmSequences 1 cos15 1).2 : ℝ) =
      (((agmSequences 1 cos15 0).1 : ℝ) + (agmSequences 1 cos15 0).2) / 2 := by
    rw [agmSequences_succ']; simp
  have g1 : (0.9828890815101808997467 : ℝ) ≤ (agmSequences 1 cos15 1).1 ∧
      ((agmSequences 1 cos15 1).1 : ℝ) ≤ 0.9828890815101808997469 := by
    rw [e1g]
    exact sqrt_mul_between (by norm_num) (by norm_num) g0 a0 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have a1 : (0.9828152554214186019996 + (1 + 0.9659258262890682867497) / 2) / 2 ≤
        ((agmSequences 1 cos15 1).2 : ℝ) ∧
      ((agmSequences 1 cos15 1).2 : ℝ) ≤
        (0.9828152554214186019998 + (1 + 0.9659258262890682867498) / 2) / 2 := by
    rw [e1a]; constructor <;> linarith [g0.1, g0.2, a0.1, a0.2]
  -- step 2
  have e2g : ((agmSequences 1 cos15 2).1 : ℝ) =
      √(((agmSequences 1 cos15 1).1 : ℝ) * (agmSequences 1 cos15 1).2) := by
    rw [agmSequences_succ']; simp
  have e2a : ((agmSequences 1 cos15 2).2 : ℝ) =
      (((agmSequences 1 cos15 1).1 : ℝ) + (agmSequences 1 cos15 1).2) / 2 := by
    rw [agmSequences_succ']; simp
  have g2 : (0.9828890828965786352391 : ℝ) ≤ (agmSequences 1 cos15 2).1 := by
    rw [e2g]
    exact (sqrt_mul_between (h := 0.9828890828965786352394) (by norm_num) (by norm_num) g1 a1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
  have a2 : ((agmSequences 1 cos15 2).2 : ℝ) ≤ 0.982889082896578636217125 := by
    rw [e2a]; linarith [g1.2, a1.2]
  refine ⟨g2.trans (by exact_mod_cast agmSequences_fst_le_agm 2), ?_⟩
  exact (by exact_mod_cast agm_le_agmSequences_snd 2 : (NNReal.agm 1 cos15 : ℝ) ≤ _).trans a2

/-- **Watson's fcc constant to fourteen digits:**
`0.44822039438838 < √3 / (4 agm(1, cos 15°)²) < 0.44822039438839`. -/
theorem watsonAGM_bounds : (0.44822039438838 : ℝ) < watsonAGM ∧ watsonAGM < 0.44822039438839 := by
  obtain ⟨m1, m2⟩ := agm_bounds
  obtain ⟨s1, s2⟩ := sqrt3_bounds
  set m : ℝ := (NNReal.agm 1 cos15 : ℝ)
  have hm : 0 < m := by linarith
  unfold watsonAGM
  change (0.44822039438838 : ℝ) < √3 / (4 * m ^ 2) ∧ √3 / (4 * m ^ 2) < 0.44822039438839
  constructor
  · calc (0.44822039438838 : ℝ) < 1.7320508075688772935274 / (4 * 0.982889082896578636217125 ^ 2) := by
          norm_num
      _ ≤ √3 / (4 * m ^ 2) := by
          apply div_le_div₀ (by positivity) s1 (by positivity)
          gcongr
  · calc √3 / (4 * m ^ 2) ≤ 1.7320508075688772935275 / (4 * 0.9828890828965786352391 ^ 2) := by
          apply div_le_div₀ (by norm_num) s2 (by norm_num)
          gcongr
      _ < 0.44822039438839 := by norm_num

end Entropic.DiamondGreen
