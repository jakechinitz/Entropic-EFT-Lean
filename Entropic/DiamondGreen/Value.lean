import Entropic.DiamondGreen.Transience
import Entropic.DiamondGreen.AGM
import Entropic.EFT.Edge.SourceProjection
import Entropic.AppCDE.Defect

/-!
# `G_tet(0) = 0.44822039438838…` from Watson's fcc integral (C05-20, -21, -22, -25, -29, C11-12, -13)

Proved, unconditionally:

1. `Fourier.greenDiamond_eq_integral`: the manuscript's integral
   `(2π)⁻³ ∫_{[-π,π]³} 4 d³k / (16 − |1 + e^{ik₁} + e^{ik₂} + e^{ik₃}|²)` equals the Neumann series
   `greenDiamond = ∑_L (A^L)₀₀ / 4^(L+1)` of `[(4 − A)⁻¹]₀₀`.
2. `Walks.dWalks_even`: closed diamond walks of length `2n` are `∑ₖ C(n,k) 4^(n−k)` times closed fcc
   walks of length `k`.
3. `Series.greenDiamond_eq`: `G_tet(0) = P_fcc / 3`.
4. `Transience.greenDiamond_lt_top`: `G_tet(0) < ∞` (the diamond lattice is transient), and
   `Transience.returnFCC_eq_integral`: `P_fcc = (2π)⁻³ ∫ 12 / (12 − ∑_v cos(k·v))` in primitive
   coordinates of the fcc lattice.
5. `AGM.watsonAGM_bounds`: `0.44822039438838 < √3 / (4 agm(1, cos 15°)²) < 0.44822039438839`.

Cited (`WatsonFCC`, a hypothesis of the theorems that use it): the fcc lattice Green function
`(2π)⁻³ ∫ 1 / (1 − s(k))`, `s = (1/12) ∑_v cos(k·v)`, equals `3 · √3 / (4 agm(1, cos 15°)²)`. This
packages three classical facts: the change from primitive to Cartesian coordinates, which turns the
integral into `3 × Watson's triple integral (2π)⁻³ ∫ d³k / (3 − cos k₁ cos k₂ − cos k₂ cos k₃ − cos k₃ cos k₁)`;
Watson's evaluation (1939) of that integral as `3Γ(1/3)⁶ / (2^(14/3) π⁴)`; and Legendre's singular
value `K(sin 15°) = 3^(1/4) Γ(1/3)³ / (2^(7/3) π)` with Gauss's `K(k) = π / (2 agm(1, k'))`, which
rewrite the Γ form as the AGM form. The Γ form itself does not occur in the Lean statements.
-/

open scoped ENNReal

namespace Entropic.DiamondGreen

/-! ### Small cases: fcc return counts and the Domb numbers -/

theorem fWalks_small : fWalks 0 0 0 = 1 ∧ fWalks 1 0 0 = 0 ∧ fWalks 2 0 0 = 12 ∧
    fWalks 3 0 0 = 48 ∧ fWalks 4 0 0 = 540 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- Closed diamond walks of lengths 0, 2, 4, 6 by direct enumeration: 1, 4, 28, 256. -/
theorem dWalks_small : dWalks 0 (false, 0) (false, 0) = 1 ∧ dWalks 2 (false, 0) (false, 0) = 4 ∧
    dWalks 4 (false, 0) (false, 0) = 28 ∧ dWalks 6 (false, 0) (false, 0) = 256 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The fifth Domb number, 2716, from the reduction and the fcc counts up to length 4
(direct enumeration of the 4⁸ diamond walks exceeds the kernel budget). -/
theorem dWalks_eight : dWalks 8 (false, 0) (false, 0) = 2716 := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := fWalks_small
  rw [show 8 = 2 * 4 from rfl, dWalks_even]
  simp [Finset.sum_range_succ, f0, f1, f2, f3, f4]
  decide

/-! ### The value -/

/-- **Cited (Watson 1939, with Legendre and Gauss).** The fcc lattice Green function in primitive
coordinates, `(2π)⁻³ ∫_{[-π,π]³} 12 / (12 − ∑_v cos(k·v))`, equals `3 · √3 / (4 agm(1, cos 15°)²)`. -/
def WatsonFCC : Prop :=
  ENNReal.ofReal ((2 * Real.pi) ^ 3)⁻¹ * ∫⁻ k in cube, ENNReal.ofReal (12 / (12 - fccSum k)) =
    ENNReal.ofReal (3 * watsonAGM)

theorem watsonAGM_pos : 0 < watsonAGM := by linarith [watsonAGM_bounds.1]

theorem returnFCC_of_watson (h : WatsonFCC) : returnFCC = ENNReal.ofReal (3 * watsonAGM) := by
  rw [returnFCC_eq_integral]; exact h

theorem greenDiamond_of_watson (h : WatsonFCC) : greenDiamond = ENNReal.ofReal watsonAGM := by
  rw [greenDiamond_eq, returnFCC_of_watson h, ← ENNReal.ofReal_ofNat 3,
    ← ENNReal.ofReal_div_of_pos (by norm_num)]
  congr 1; ring

/-- The real number `G_tet(0)` (finite by `greenDiamond_lt_top`). -/
noncomputable def Gtet0 : ℝ := greenDiamond.toReal

theorem ofReal_Gtet0 : ENNReal.ofReal Gtet0 = greenDiamond :=
  ENNReal.ofReal_toReal greenDiamond_lt_top.ne

/-- Unconditional lower bound from the first term of the series: `G_tet(0) ≥ 1/4`. -/
theorem Gtet0_ge : (1 / 4 : ℝ) ≤ Gtet0 := by
  have h : (1 / 4 : ℝ≥0∞) ≤ greenDiamond := by
    have := ENNReal.le_tsum (f := fun L => (dWalks L (false, 0) (false, 0) : ℝ≥0∞) / 4 ^ (L + 1)) 0
    simpa [dWalks, greenDiamond] using this
  have := ENNReal.toReal_mono greenDiamond_lt_top.ne h
  simpa [Gtet0] using this

theorem Gtet0_eq (h : WatsonFCC) : Gtet0 = watsonAGM := by
  rw [Gtet0, greenDiamond_of_watson h, ENNReal.toReal_ofReal watsonAGM_pos.le]

/-- **C05-22 / C11-12.** `0.44822039438838 < G_tet(0) < 0.44822039438839`. -/
theorem Gtet0_bounds (h : WatsonFCC) : (0.44822039438838 : ℝ) < Gtet0 ∧ Gtet0 < 0.44822039438839 := by
  rw [Gtet0_eq h]; exact watsonAGM_bounds

/-- **C05-29.** The cell-normalized horizon entropy `S₀ = 3 ln 2 / (32 π G_tet(0)) = 0.04614825155…`. -/
theorem SInfCell_bounds (h : WatsonFCC) :
    (0.0461482515 : ℝ) < Entropic.EFT.Edge.SInfCell Gtet0 ∧
      Entropic.EFT.Edge.SInfCell Gtet0 < 0.0461482516 := by
  obtain ⟨g1, g2⟩ := Gtet0_bounds h
  have l1 := Real.log_two_gt_d9; have l2 := Real.log_two_lt_d9
  have p1 := Real.pi_gt_d20; have p2 := Real.pi_lt_d20
  unfold Entropic.EFT.Edge.SInfCell
  have hG : 0 < Gtet0 := by linarith
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    calc (0.0461482515 : ℝ) * (32 * Real.pi * Gtet0)
        < 0.0461482515 * (32 * 3.14159265358979323847 * 0.44822039438839) := by gcongr
      _ < 3 * 0.6931471803 := by norm_num
      _ < 3 * Real.log 2 := by linarith
  · rw [div_lt_iff₀ (by positivity)]
    calc 3 * Real.log 2 < 3 * 0.6931471808 := by linarith
      _ < 0.0461482516 * (32 * 3.14159265358979323846 * 0.44822039438838) := by norm_num
      _ < 0.0461482516 * (32 * Real.pi * Gtet0) := by gcongr

/-- **C05-25.** Dimensionless source amplitude `ln(7/6) / (π G_tet(0)) = 0.10947222…`. -/
theorem source_amplitude_bounds (h : WatsonFCC) :
    (0.1094722281 : ℝ) < Real.log (7 / 6) / (Real.pi * Gtet0) ∧
      Real.log (7 / 6) / (Real.pi * Gtet0) < 0.1094722285 := by
  obtain ⟨g1, g2⟩ := Gtet0_bounds h
  obtain ⟨l1, l2⟩ := Entropic.AppCDE.Defect.log_seven_sixths
  have p1 := Real.pi_gt_d20; have p2 := Real.pi_lt_d20
  have hG : 0 < Gtet0 := by linarith
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    calc (0.1094722281 : ℝ) * (Real.pi * Gtet0)
        < 0.1094722281 * (3.14159265358979323847 * 0.44822039438839) := by gcongr
      _ < 0.1541506798 := by norm_num
      _ < Real.log (7 / 6) := l1
  · rw [div_lt_iff₀ (by positivity)]
    calc Real.log (7 / 6) < 0.1541506799 := l2
      _ < 0.1094722285 * (3.14159265358979323846 * 0.44822039438838) := by norm_num
      _ < 0.1094722285 * (Real.pi * Gtet0) := by gcongr

/-- **Headline.** The manuscript's integral `(2π)⁻³ ∫ 4/(16 − |λ|²)` over `[-π,π]³` equals Watson's
fcc constant and lies in `(0.44822039438838, 0.44822039438839)`, given Watson's evaluation. -/
theorem manuscript_Gtet (h : WatsonFCC) :
    ENNReal.ofReal ((2 * Real.pi) ^ 3)⁻¹ *
        ∫⁻ k in cube, ENNReal.ofReal (4 / (16 - Complex.normSq (lam k))) = ENNReal.ofReal watsonAGM ∧
      (0.44822039438838 : ℝ) < (ENNReal.ofReal ((2 * Real.pi) ^ 3)⁻¹ *
        ∫⁻ k in cube, ENNReal.ofReal (4 / (16 - Complex.normSq (lam k)))).toReal ∧
      (ENNReal.ofReal ((2 * Real.pi) ^ 3)⁻¹ *
        ∫⁻ k in cube, ENNReal.ofReal (4 / (16 - Complex.normSq (lam k)))).toReal < 0.44822039438839 := by
  rw [← greenDiamond_eq_integral]
  exact ⟨greenDiamond_of_watson h, Gtet0_bounds h⟩

/-- The library's certificate slot for the diamond Green function. `G0` and `positive` are proved
unconditionally. The two `Prop` fields record statements: the integral representation (proved,
`diamondGreenMath_props`) and the closed form in its AGM version (proved given `WatsonFCC`). -/
noncomputable def diamondGreenMath : Entropic.EFT.Edge.DiamondGreenMath where
  G0 := Gtet0
  positive := by linarith [Gtet0_ge]
  integralRepresentation := greenDiamond = ENNReal.ofReal ((2 * Real.pi) ^ 3)⁻¹ *
      ∫⁻ k in cube, ENNReal.ofReal (4 / (16 - Complex.normSq (lam k))) ∧ greenDiamond = returnFCC / 3
  joyceClosedForm := Gtet0 = watsonAGM

theorem diamondGreenMath_props (h : WatsonFCC) :
    diamondGreenMath.integralRepresentation ∧ diamondGreenMath.joyceClosedForm :=
  ⟨⟨greenDiamond_eq_integral, greenDiamond_eq⟩, Gtet0_eq h⟩

end Entropic.DiamondGreen
