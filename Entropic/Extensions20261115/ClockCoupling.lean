import Entropic.AppCDE.Calibration
import Entropic.Spine
import Mathlib.Tactic

/-!
# Clock attachment and the strong coupling (Appendices I.8 and I.9)

Statements of the "Direction records", "Strong-coupling comparison" and clock paragraphs that admit proof.

* Bond length and record coefficient: with the C.8 volume identification (volume per site
  `8d³/(3√3) = v_ev/2`) at `m₄ = 2.3219`, `d/L_* = 1.07306…` (`bond_length_value`), the renewal rate in
  bond units is `λd/c = 0.5365…` and the complete-record coefficient is `γ_W = d/4L_* = 0.26826…`
  (`gammaW_value`), against the dispersion value `√(27/320) = 0.29047…` (`dispersion_value`).
* Relaxed field: an admissible change of the background by `B c` changes the minimizing response by
  `−c` and preserves the total field and the minimum (`relaxed_field_invariance`).
* The table of clock attachments: offsets and percentages of the two Poisson completions against the
  one- and two-loop references (`independent_row_offsets`, `renewal_triangle_offsets`,
  `reference_between`).
* Leading-log scale relation: one-loop running through fixed thresholds carries a shift of `α⁻¹(μ_*)`
  unchanged to every lower scale (`runChain_shift`), so `Δ ln Λ₃ = −(2π/9) Δα⁻¹(μ_*)`
  (`scale_sensitivity`), with ratios `4.1` and `0.51` for the two completions (`scale_ratios`).

Inputs, not derived here: the four matched values of `α⁻¹(μ_*)` (numerical stiffness and quark
calculations recorded in `02 Research/Native color running 2026-11-10`), the references `52.48` and
`53.02`, and the clock attachment itself.
-/

noncomputable section
namespace Entropic.Extensions20261115.ClockCoupling
open Real Entropic.AppCDE.Calibration

/-! ### Bond length and the record coefficient -/

/-- C.8 volume identification on the diamond complex: `d > 0` and the volume per site `8d³/(3√3)`
equals `v_ev/2` (units `L_* = 1`). -/
def BondLength (m d : ℝ) : Prop := 0 < d ∧ 8 * d ^ 3 / (3 * Real.sqrt 3) = vev m / 2

theorem bond_cube {m d : ℝ} (h : BondLength m d) : d ^ 3 = 3 * Real.sqrt 3 * vev m / 16 := by
  obtain ⟨-, h2⟩ := h
  have h3 : (0 : ℝ) < 3 * Real.sqrt 3 := by positivity
  field_simp at h2 ⊢
  linarith

/-- I.5, I.9: at `m₄ = 2.3219`, `d/L_* ∈ (1.07306, 1.07307)` (paper: `1.0731`). -/
theorem bond_length_value {d : ℝ} (h : BondLength 2.3219 d) : 1.07306 < d ∧ d < 1.07307 := by
  have hc := bond_cube h
  have hd := h.1
  have pl := Real.pi_gt_d20; have ph := Real.pi_lt_d20
  obtain ⟨s3l, s3h⟩ := sqrt3_bounds
  have hP1 : (1.73205080756 : ℝ) * 3.14159265358979323846 < Real.sqrt 3 * Real.pi := by
    apply mul_lt_mul s3l pl.le (by norm_num) (by positivity)
  have hP2 : Real.sqrt 3 * Real.pi < 1.73205080757 * 3.14159265358979323847 := by
    apply mul_lt_mul s3h ph.le Real.pi_pos (by norm_num)
  have hc' : d ^ 3 = 3 * (Real.sqrt 3 * Real.pi) * (2.3219 : ℝ) ^ 4 / 384 := by
    rw [hc]; unfold vev; ring
  constructor
  · by_contra hn; rw [not_lt] at hn
    have : d ^ 3 ≤ (1.07306 : ℝ) ^ 3 := pow_le_pow_left₀ hd.le hn 3
    nlinarith
  · by_contra hn; rw [not_lt] at hn
    have : (1.07307 : ℝ) ^ 3 ≤ d ^ 3 := pow_le_pow_left₀ (by norm_num) hn 3
    nlinarith

/-- I.9: complete-record coefficient `γ_W = d/(4L_*) ∈ (0.268265, 0.268268)` (paper: `0.2683`), and
the renewal rate in bond units `λd/c = d/(2L_*) ∈ (0.53653, 0.53654)`. -/
theorem gammaW_value {d : ℝ} (h : BondLength 2.3219 d) :
    0.268265 < d / 4 ∧ d / 4 < 0.268268 ∧ 0.53653 < d / 2 ∧ d / 2 < 0.53654 := by
  obtain ⟨a, b⟩ := bond_length_value h
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- I.9: the dispersion criterion `r_W = √(27/320) ∈ (0.29047, 0.29048)` (paper: `0.2905`). -/
theorem dispersion_value : 0.29047 < Real.sqrt (27/320) ∧ Real.sqrt (27/320) < 0.29048 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- The complete-record coefficient lies below the dispersion value, by 7 to 8 per cent. -/
theorem gammaW_below_dispersion {d : ℝ} (h : BondLength 2.3219 d) :
    0.92 * Real.sqrt (27/320) < d / 4 ∧ d / 4 < 0.93 * Real.sqrt (27/320) := by
  obtain ⟨a, b, -, -⟩ := gammaW_value h
  obtain ⟨c, e⟩ := dispersion_value
  constructor <;> linarith

/-! ### Relaxed link field -/

/-- I.9: let the gauge energy be a function `E` of the total link field `f + B a`, with background `f`
and response `a` entering through an additive map `B`. If `a` minimizes at background `f`, then
`a − c` minimizes at the background `f + B c`, the total field is unchanged, and so is the minimum.
Changing the background interpolation by an admissible field `B c` changes the minimizing response by
its negative. -/
theorem relaxed_field_invariance {V W : Type*} [AddCommGroup V] [AddCommGroup W] (B : V →+ W)
    (E : W → ℝ) (f : W) (c a : V) (hmin : ∀ a', E (f + B a) ≤ E (f + B a')) :
    (∀ a', E ((f + B c) + B (a - c)) ≤ E ((f + B c) + B a')) ∧
      (f + B c) + B (a - c) = f + B a := by
  have htot : (f + B c) + B (a - c) = f + B a := by rw [map_sub]; abel
  refine ⟨fun a' => ?_, htot⟩
  rw [htot, show (f + B c) + B a' = f + B (c + a') by rw [map_add]; abel]
  exact hmin _

/-! ### The table of clock attachments -/

/-- Reference inverse couplings at `μ_*` from `α_s(M_Z) = 0.1180` (one- and two-loop running). -/
def refOneLoop : ℝ := 52.48
def refTwoLoop : ℝ := 53.02
/-- Matched values of `α_s⁻¹(μ_*)` for the four clock attachments of I.9 (inputs). -/
def rowRenewalTriangle : ℝ := 50.99
def rowCommonLayers : ℝ := 51.04
def rowSpread : ℝ := 52.10
def rowIndependent : ℝ := 53.98

/-- I.9: the independent-reading value lies `1.50` and `0.96` above the references, `2.9%` and `1.8%`. -/
theorem independent_row_offsets :
    rowIndependent - refOneLoop = 1.50 ∧ rowIndependent - refTwoLoop = 0.96 ∧
      0.0285 < (rowIndependent - refOneLoop) / refOneLoop ∧
      (rowIndependent - refOneLoop) / refOneLoop < 0.0295 ∧
      0.0175 < (rowIndependent - refTwoLoop) / refTwoLoop ∧
      (rowIndependent - refTwoLoop) / refTwoLoop < 0.0185 := by
  unfold rowIndependent refOneLoop refTwoLoop; norm_num

/-- I.9: the renewal-triangle value lies `2.8%` and `3.8%` below the references. -/
theorem renewal_triangle_offsets :
    0.0275 < (refOneLoop - rowRenewalTriangle) / refOneLoop ∧
      (refOneLoop - rowRenewalTriangle) / refOneLoop < 0.0285 ∧
      0.0375 < (refTwoLoop - rowRenewalTriangle) / refTwoLoop ∧
      (refTwoLoop - rowRenewalTriangle) / refTwoLoop < 0.0385 := by
  unfold rowRenewalTriangle refOneLoop refTwoLoop; norm_num

/-- I.9: the four rows are ordered and the two Poisson completions place both references between them. -/
theorem reference_between :
    rowRenewalTriangle < rowCommonLayers ∧ rowCommonLayers < rowSpread ∧ rowSpread < refOneLoop ∧
      refOneLoop < refTwoLoop ∧ refTwoLoop < rowIndependent := by
  unfold rowRenewalTriangle rowCommonLayers rowSpread refOneLoop refTwoLoop rowIndependent; norm_num

/-! ### Leading-log scale relation -/

/-- One-loop coefficient `β₀ = 11 − (2/3)N_f` and two-loop coefficient `β₁ = 102 − (38/3)N_f`. -/
def beta0 (Nf : ℝ) : ℝ := 11 - 2 / 3 * Nf
def beta1 (Nf : ℝ) : ℝ := 102 - 38 / 3 * Nf

theorem beta_values : beta0 6 = 7 ∧ beta1 6 = 26 ∧ beta0 3 = 9 := by
  unfold beta0 beta1; norm_num

/-- One-loop running of the inverse coupling from `μ₀` to `μ`:
`α⁻¹(μ) = α⁻¹(μ₀) + (β₀/2π) ln(μ/μ₀)`. -/
def run1 (b0 a0 μ0 μ : ℝ) : ℝ := a0 + b0 / (2 * π) * Real.log (μ / μ0)

/-- Running through a list of segments `(β₀, next scale)` with fixed thresholds. Returns the inverse
coupling at the last scale. -/
def runChain : List (ℝ × ℝ) → ℝ → ℝ → ℝ
  | [], a, _ => a
  | (b0, μ) :: rest, a, μ0 => runChain rest (run1 b0 a μ0 μ) μ

/-- With fixed thresholds, a shift of the inverse coupling at the starting scale is carried unchanged
to every lower scale. -/
theorem runChain_shift (segs : List (ℝ × ℝ)) (a δ μ0 : ℝ) :
    runChain segs (a + δ) μ0 = runChain segs a μ0 + δ := by
  induction segs generalizing a μ0 with
  | nil => rfl
  | cons s rest ih =>
    obtain ⟨b0, μ⟩ := s
    simp only [runChain]
    rw [show run1 b0 (a + δ) μ0 μ = run1 b0 a μ0 μ + δ by unfold run1; ring]
    exact ih _ _

/-- Three-flavour scale at leading logarithm: `Λ₃ = μ exp(−2π α⁻¹(μ)/9)`. -/
def Lambda3 (μ a : ℝ) : ℝ := μ * Real.exp (-(2 * π / 9) * a)

/-- `Λ₃` does not depend on the scale at which it is evaluated along three-flavour one-loop running. -/
theorem Lambda3_invariant {μ0 μ : ℝ} (h0 : 0 < μ0) (h : 0 < μ) (a0 : ℝ) :
    Lambda3 μ (run1 9 a0 μ0 μ) = Lambda3 μ0 a0 := by
  unfold Lambda3 run1
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [show -(2 * π / 9) * (a0 + 9 / (2 * π) * Real.log (μ / μ0)) =
      -(2 * π / 9) * a0 + -Real.log (μ / μ0) by field_simp; ring]
  rw [Real.exp_add, Real.exp_neg, Real.exp_log (div_pos h h0)]
  field_simp

/-- I.9: `Δ ln Λ₃ = −(2π/9) Δα_s⁻¹(μ_*)`. A shift `δ` of the microscopic inverse coupling, carried
through fixed thresholds by `runChain`, multiplies the three-flavour scale by `exp(−(2π/9)δ)`. -/
theorem scale_sensitivity (segs : List (ℝ × ℝ)) (a δ μstar μ : ℝ) (hμ : 0 < μ) :
    Lambda3 μ (runChain segs (a + δ) μstar) =
        Lambda3 μ (runChain segs a μstar) * Real.exp (-(2 * π / 9) * δ) ∧
      Real.log (Lambda3 μ (runChain segs (a + δ) μstar) / Lambda3 μ (runChain segs a μstar)) =
        -(2 * π / 9) * δ := by
  have e : Lambda3 μ (runChain segs (a + δ) μstar) =
      Lambda3 μ (runChain segs a μstar) * Real.exp (-(2 * π / 9) * δ) := by
    rw [runChain_shift]; unfold Lambda3; rw [mul_add, Real.exp_add]; ring
  refine ⟨e, ?_⟩
  have hpos : 0 < Lambda3 μ (runChain segs a μstar) := by unfold Lambda3; positivity
  rw [e, mul_div_cancel_left₀ _ hpos.ne', Real.log_exp]

/-- I.9: applied around the two-loop reference, the sensitivity gives scale ratios `0.51` for the
independent-reading value (`δ = 53.98 − 53.02`) and `4.1` for the renewal-triangle value
(`δ = 50.99 − 53.02`). -/
theorem scale_ratios :
    0.51 < Real.exp (-(2 * π / 9) * (rowIndependent - refTwoLoop)) ∧
      Real.exp (-(2 * π / 9) * (rowIndependent - refTwoLoop)) < 0.52 ∧
      4.1 < Real.exp (-(2 * π / 9) * (rowRenewalTriangle - refTwoLoop)) ∧
      Real.exp (-(2 * π / 9) * (rowRenewalTriangle - refTwoLoop)) < 4.2 := by
  have pl := Real.pi_gt_d6; have ph := Real.pi_lt_d6
  unfold rowIndependent rowRenewalTriangle refTwoLoop
  -- first ratio: exponent −x with x ∈ (0.67020, 0.67021)
  have x1 : (0.67020 : ℝ) < 2 * π / 9 * (53.98 - 53.02) := by nlinarith
  have x2 : 2 * π / 9 * (53.98 - 53.02) < (0.67021 : ℝ) := by nlinarith
  have e1 := (Entropic.Spine.exp_neg_encl 10 (by norm_num) (a := 0.67021) (by norm_num) (by norm_num)).1
  have e2 := (Entropic.Spine.exp_neg_encl 10 (by norm_num) (a := 0.67020) (by norm_num) (by norm_num)).2
  have r1 : (0.51 : ℝ) < Real.exp (-(2 * π / 9) * (53.98 - 53.02)) := by
    have hmono : Real.exp (-(0.67021 : ℝ)) ≤ Real.exp (-(2 * π / 9) * (53.98 - 53.02)) :=
      Real.exp_le_exp.mpr (by linarith)
    refine lt_of_lt_of_le (lt_of_lt_of_le ?_ e1) hmono
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have r2 : Real.exp (-(2 * π / 9) * (53.98 - 53.02)) < (0.52 : ℝ) := by
    have hmono : Real.exp (-(2 * π / 9) * (53.98 - 53.02)) ≤ Real.exp (-(0.67020 : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith)
    refine lt_of_le_of_lt (le_trans hmono e2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  -- second ratio: exp(y) = (exp(−y/2))⁻², y/2 ∈ (0.70860, 0.70861)
  have y1 : (0.70860 : ℝ) < π / 9 * (53.02 - 50.99) := by nlinarith
  have y2 : π / 9 * (53.02 - 50.99) < (0.70861 : ℝ) := by nlinarith
  have f1 := (Entropic.Spine.exp_neg_encl 10 (by norm_num) (a := 0.70861) (by norm_num) (by norm_num)).1
  have f2 := (Entropic.Spine.exp_neg_encl 10 (by norm_num) (a := 0.70860) (by norm_num) (by norm_num)).2
  set E := Real.exp (-(π / 9 * (53.02 - 50.99))) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hEl : (0.4923 : ℝ) < E := by
    have hmono : Real.exp (-(0.70861 : ℝ)) ≤ E := Real.exp_le_exp.mpr (by linarith)
    refine lt_of_lt_of_le (lt_of_lt_of_le ?_ f1) hmono
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hEu : E < (0.4924 : ℝ) := by
    have hmono : E ≤ Real.exp (-(0.70860 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    refine lt_of_le_of_lt (le_trans hmono f2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hy : Real.exp (-(2 * π / 9) * (50.99 - 53.02)) = (E ^ 2)⁻¹ := by
    rw [hE, ← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; push_cast; ring
  have hE2 : 0 < E ^ 2 := by positivity
  refine ⟨r1, r2, ?_, ?_⟩
  · rw [hy, lt_inv_comm₀ (by norm_num) hE2]; nlinarith
  · rw [hy, inv_lt_comm₀ hE2 (by norm_num)]; nlinarith

end Entropic.Extensions20261115.ClockCoupling
