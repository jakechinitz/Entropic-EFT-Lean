import Entropic.GalacticLaw

/-!
# The radial-acceleration law with `a₀(z) = ε c H(z)` (Sections 15 and 27.3)

Ledger kinds A (exact mathematics of the law of `Entropic.GalacticLaw`) and C (the premise
`a₀(z) = ε c H(z)`, which the paper states with the lag caveat of Section 15).

* `gObs_strictMono_a0`: at fixed baryonic acceleration, `GalacticLaw.gObs` grows strictly with `a₀`.
* `boost_rises_with_H`: with `a₀(z) = ε c H(z)`, the boost at fixed `g` rises wherever `H(z)` does.
* `excess_ratio_constant`: `c H(z) / a₀(z) = 1/ε` at every redshift.
* `btfr_mass_ratio`, `btfr_redshift`: in the deep regime `v⁴ = G M a₀` (`GalacticLaw.btfr_parameter_free`),
  so at fixed rotation speed the baryonic mass scales as `H(0)/H(z)`: the Tully–Fisher zero point moves by
  `−log₁₀ E(z)` dex in mass.

Ported from the held-out-test record of 2026-10-26 (`verification/heldout_bestfit_2026-10-26.md`), restated
on `Entropic.GalacticLaw.gObs`.
-/

noncomputable section

namespace Entropic.RAR

open Real Entropic.GalacticLaw

/-- `a₀(z) = ε c H(z)`. -/
def a0z (ε c : ℝ) (H : ℝ → ℝ) (z : ℝ) : ℝ := ε * c * H z

/-- At fixed baryonic acceleration the observed acceleration grows strictly with `a₀`. -/
theorem gObs_strictMono_a0 {g a₁ a₂ : ℝ} (hg : 0 < g) (h1 : 0 < a₁) (h12 : a₁ < a₂) :
    gObs a₁ g < gObs a₂ g := by
  unfold gObs
  have h2 : 0 < a₂ := lt_trans h1 h12
  have hq : g / a₂ < g / a₁ := div_lt_div_of_pos_left hg h1 h12
  have hs : Real.sqrt (g / a₂) < Real.sqrt (g / a₁) :=
    Real.sqrt_lt_sqrt (div_pos hg h2).le hq
  have he : exp (-Real.sqrt (g / a₁)) < exp (-Real.sqrt (g / a₂)) :=
    exp_lt_exp.mpr (by linarith)
  have hd1 := one_sub_exp_neg_pos (Real.sqrt_pos.mpr (div_pos hg h1))
  have hd2 := one_sub_exp_neg_pos (Real.sqrt_pos.mpr (div_pos hg h2))
  rw [div_lt_div_iff₀ hd1 hd2]
  nlinarith

/-- With `a₀(z) = ε c H(z)`, the boost at fixed `g` rises with the Hubble rate. -/
theorem boost_rises_with_H {ε c g : ℝ} {H : ℝ → ℝ} {z₁ z₂ : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (hg : 0 < g) (hH1 : 0 < H z₁) (hH : H z₁ < H z₂) :
    gObs (a0z ε c H z₁) g < gObs (a0z ε c H z₂) g := by
  apply gObs_strictMono_a0 hg
  · unfold a0z; positivity
  · unfold a0z
    have : 0 < ε * c := mul_pos hε hc
    nlinarith

/-- The ratio `c H(z) / a₀(z) = 1/ε` is the same at every redshift. -/
theorem excess_ratio_constant {ε c : ℝ} {H : ℝ → ℝ} (z : ℝ) (hε : ε ≠ 0) (hc : c ≠ 0)
    (hH : H z ≠ 0) : c * H z / a0z ε c H z = 1 / ε := by
  unfold a0z
  field_simp

/-- Deep-regime Tully–Fisher relation at two epochs: if `v⁴ = G M₁ a₁` and `v⁴ = G M₂ a₂` for the same
rotation speed, then `M₂ / M₁ = a₁ / a₂`. -/
theorem btfr_mass_ratio {G v M₁ M₂ a₁ a₂ : ℝ} (hG : 0 < G) (hM₁ : 0 < M₁) (ha₂ : 0 < a₂)
    (h₁ : v ^ 4 = G * M₁ * a₁) (h₂ : v ^ 4 = G * M₂ * a₂) : M₂ / M₁ = a₁ / a₂ := by
  rw [div_eq_div_iff hM₁.ne' ha₂.ne']
  have : G * (M₂ * a₂) = G * (a₁ * M₁) := by linarith
  have := mul_left_cancel₀ hG.ne' this
  linarith

/-- With `a₀(z) = ε c H(z)`: at fixed rotation speed, `M(z) / M(0) = H(0) / H(z)`. -/
theorem btfr_redshift {G v ε c M₀ M_z : ℝ} {H : ℝ → ℝ} {z : ℝ} (hG : 0 < G) (hε : 0 < ε)
    (hc : 0 < c) (hM₀ : 0 < M₀) (hHz : 0 < H z)
    (h₀ : v ^ 4 = G * M₀ * a0z ε c H 0) (hz : v ^ 4 = G * M_z * a0z ε c H z) :
    M_z / M₀ = H 0 / H z := by
  have hpos : 0 < a0z ε c H z := by unfold a0z; positivity
  rw [btfr_mass_ratio hG hM₀ hpos h₀ hz]
  unfold a0z
  have : ε * c ≠ 0 := (mul_pos hε hc).ne'
  field_simp

end Entropic.RAR
