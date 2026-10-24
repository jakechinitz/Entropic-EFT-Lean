import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Premises of the isentropic halo envelope (research note 2026-10-24).

The envelope uses `P = ζ ρ²`, an outer plateau of constant `ζ`, and a matching radius
`a` fixed by the inner relation. This module separates what is forced from what is
assumed.

1. Exponent. For `ε = m n + z n^γ` with `m, z > 0` and `γ > 1`, the pressure is
   `P = (γ - 1) z n^γ` and the sound speed obeys `c_s² < γ - 1` at every density, with
   `γ - 1` approached at high density (`cs2_lt`, `cs2_formula`). The sound speed stays
   below light speed at every density exactly when `γ ≤ 2` (`causal_iff`). At `γ = 2`,
   `P / ε → 1` (`stiff_limit`). The exponent of the envelope is therefore the stiffest
   causal member of the warm family `1 < γ ≤ 2`; choosing that endpoint is a premise.
2. Coefficient. A pair coefficient `∑ p_a p_b κ_ab` built from a fixed kernel lies
   between the kernel's least and greatest entries for every composition `p`
   (`pair_coefficient_bounds`), so its range across halos is at most `κ_max / κ_min`
   (`pair_coefficient_ratio`). The matched coefficient `ζ = π G (1 + η) a²` grows in
   proportion to the baryonic mass at fixed stock ratio, so a universal pair kernel
   cannot supply it across the galaxy mass range; `ζ` has to be a state label.
3. Matching. With `G A² = M a₀` and `η = M / (2 A a)`, the acceleration at the matching
   radius is `2 η (1 + η) a₀` (`matching_acceleration`). The envelope solution
   `ρ = D sin (k r - φ) / r` solves the constant-`ζ` hydrostatic equation (`envelope_ode`),
   and its stock is given in closed form (`envelope_mass`).
4. Extent. Since `R ≤ 2 a` and `a = r_M / (2 η)`, a stock that extends to radius `L`
   requires a stock-to-baryon ratio of at least `(L / r_M - 1) / 2`
   (`stock_ratio_lower_bound`).
5. Stock ratio bookkeeping. A deep-RAR stock out to a supplied radius `R` has ratio
   `R / r_M - 1/2` (`isothermal_stock_ratio`). With full stock retention, the retained
   fraction of ancestral baryons is `k / S` (`retained_fraction`); the detected baryon
   fraction is `(1 + k)/(1 + S)` (`detected_fraction_formula`), which is larger whenever
   `k < S` (`retained_lt_detected`). -/

noncomputable section
namespace Entropic.EnvelopePremises

open Real Filter

/-! ## 1. The exponent: the stiffest causal power -/

/-- Squared sound speed of `ε = m n + z n^γ`, written through `x = γ z n^(γ-1) / m`. -/
def cs2 (γ m z n : ℝ) : ℝ :=
  (γ * (γ - 1) * z * n ^ (γ - 1)) / (m + γ * z * n ^ (γ - 1))

theorem energy_hasDerivAt (γ m z n : ℝ) (hn : 0 < n) :
    HasDerivAt (fun n => m * n + z * n ^ γ) (m + z * (γ * n ^ (γ - 1))) n := by
  have h := ((hasDerivAt_id n).const_mul m).fun_add
    ((Real.hasDerivAt_rpow_const (p := γ) (Or.inl hn.ne')).const_mul z)
  simpa using h

theorem pressure_hasDerivAt (γ z n : ℝ) (hn : 0 < n) :
    HasDerivAt (fun n => (γ - 1) * z * n ^ γ) ((γ - 1) * z * (γ * n ^ (γ - 1))) n :=
  (Real.hasDerivAt_rpow_const (p := γ) (Or.inl hn.ne')).const_mul _

/-- Thermodynamic pressure `n ε' - ε` of the warm energy. -/
theorem pressure_identity (γ m z n : ℝ) (hn : 0 < n) :
    n * (m + z * (γ * n ^ (γ - 1))) - (m * n + z * n ^ γ) = (γ - 1) * z * n ^ γ := by
  have h : n * n ^ (γ - 1) = n ^ γ := by
    have := Real.rpow_add hn 1 (γ - 1)
    rw [Real.rpow_one] at this
    rw [← this]; congr 1; ring
  have : n * (m + z * (γ * n ^ (γ - 1))) = m * n + γ * z * (n * n ^ (γ - 1)) := by ring
  rw [this, h]; ring

theorem cs2_formula (γ m z n : ℝ) :
    cs2 γ m z n = ((γ * (γ - 1) * z * n ^ (γ - 1))) / (m + γ * z * n ^ (γ - 1)) := rfl

theorem cs2_nonneg {γ m z n : ℝ} (hγ : 1 < γ) (hm : 0 < m) (hz : 0 < z) (hn : 0 < n) :
    0 ≤ cs2 γ m z n := by
  unfold cs2
  have hp : 0 < n ^ (γ - 1) := Real.rpow_pos_of_pos hn _
  apply div_nonneg
  · have : 0 < γ * (γ - 1) * z * n ^ (γ - 1) := by
      have : 0 < γ - 1 := by linarith
      positivity
    exact this.le
  · have : 0 < γ * z * n ^ (γ - 1) := by positivity
    linarith

/-- At every density the squared sound speed is below `γ - 1`. -/
theorem cs2_lt {γ m z n : ℝ} (hγ : 1 < γ) (hm : 0 < m) (hz : 0 < z) (hn : 0 < n) :
    cs2 γ m z n < γ - 1 := by
  unfold cs2
  have hp : 0 < n ^ (γ - 1) := Real.rpow_pos_of_pos hn _
  have hx : 0 < γ * z * n ^ (γ - 1) := by positivity
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- The warm energy is causal at every density exactly when `γ ≤ 2`. -/
theorem causal_iff {γ m z : ℝ} (hγ : 1 < γ) (hm : 0 < m) (hz : 0 < z) :
    (∀ n : ℝ, 0 < n → cs2 γ m z n < 1) ↔ γ ≤ 2 := by
  constructor
  · intro h
    by_contra hg
    push Not at hg
    -- the density at which the sound speed reaches light speed
    set c : ℝ := m / ((γ - 2) * γ * z) with hc
    have hcpos : 0 < c := by
      have : 0 < γ - 2 := by linarith
      positivity
    set n0 : ℝ := c ^ (γ - 1)⁻¹
    have hn0 : 0 < n0 := Real.rpow_pos_of_pos hcpos _
    have hpow : n0 ^ (γ - 1) = c := Real.rpow_inv_rpow hcpos.le (by linarith)
    have hlt := h n0 hn0
    unfold cs2 at hlt
    rw [hpow, div_lt_one (by positivity)] at hlt
    have h2 : 0 < γ - 2 := by linarith
    have hce : (γ - 2) * γ * z * c = m := by
      rw [hc]; field_simp
    nlinarith
  · intro h n hn
    exact lt_of_lt_of_le (cs2_lt hγ hm hz hn) (by linarith)

/-- At `γ = 2` the pressure approaches the energy density: the stiff limit. -/
theorem stiff_limit {m z : ℝ} (hm : 0 < m) (hz : 0 < z) :
    Tendsto (fun n : ℝ => (z * n ^ 2) / (m * n + z * n ^ 2)) atTop (nhds 1) := by
  have h : ∀ᶠ n : ℝ in atTop, (z * n ^ 2) / (m * n + z * n ^ 2) = 1 / (1 + m / z * n⁻¹) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    field_simp
    ring
  rw [tendsto_congr' h]
  have h0 : Tendsto (fun n : ℝ => m / z * n⁻¹) atTop (nhds 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul (m / z)
  have := ((tendsto_const_nhds (x := (1:ℝ))).add h0).inv₀ (by norm_num)
  simpa using this

/-! ## 2. A universal pair kernel has bounded range -/

/-- For any composition, the pair coefficient lies between the kernel bounds. -/
theorem pair_coefficient_bounds {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (κ : ι → ι → ℝ) (lo hi : ℝ) (hlo : ∀ i j, lo ≤ κ i j)
    (hhi : ∀ i j, κ i j ≤ hi) :
    lo ≤ ∑ i, ∑ j, p i * p j * κ i j ∧ ∑ i, ∑ j, p i * p j * κ i j ≤ hi := by
  have hsum : ∑ i, ∑ j, p i * p j = 1 := by
    simp only [← Finset.mul_sum, hs, mul_one]
  constructor
  · calc lo = ∑ i, ∑ j, p i * p j * lo := by
          simp only [← Finset.sum_mul, hsum, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hlo i j) (mul_nonneg (hp i) (hp j))
  · calc _ ≤ ∑ i, ∑ j, p i * p j * hi := Finset.sum_le_sum fun i _ => Finset.sum_le_sum
          fun j _ => mul_le_mul_of_nonneg_left (hhi i j) (mul_nonneg (hp i) (hp j))
      _ = hi := by simp only [← Finset.sum_mul, hsum, one_mul]

/-- The ratio of pair coefficients for two compositions is at most `hi / lo`. -/
theorem pair_coefficient_ratio {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1)
    (κ : ι → ι → ℝ) (lo hi : ℝ) (hlo0 : 0 < lo) (hlo : ∀ i j, lo ≤ κ i j)
    (hhi : ∀ i j, κ i j ≤ hi) :
    (∑ i, ∑ j, p i * p j * κ i j) / (∑ i, ∑ j, q i * q j * κ i j) ≤ hi / lo := by
  obtain ⟨_, hp2⟩ := pair_coefficient_bounds p hp hps κ lo hi hlo hhi
  obtain ⟨hq1, _⟩ := pair_coefficient_bounds q hq hqs κ lo hi hlo hhi
  exact div_le_div₀ (le_trans hlo0.le (le_trans hq1 (by
    obtain ⟨h1, h2⟩ := pair_coefficient_bounds q hq hqs κ lo hi hlo hhi; linarith)) |>.trans
    (by obtain ⟨h1, h2⟩ := pair_coefficient_bounds q hq hqs κ lo hi hlo hhi; exact h2)) hp2
    hlo0 hq1

/-! ## 3. Matching and the envelope solution -/

/-- Acceleration at the matching radius: `G (M/2 + A a) / a² = 2 η (1 + η) a₀`. -/
theorem matching_acceleration {G M A a a0 : ℝ} (hG : 0 < G) (hA : 0 < A) (ha : 0 < a)
    (hM : 0 < M) (hdeep : G * A ^ 2 = M * a0) :
    G * (M / 2 + A * a) / a ^ 2 =
      2 * (M / (2 * A * a)) * (1 + M / (2 * A * a)) * a0 := by
  have ha0 : a0 = G * A ^ 2 / M := by field_simp; linarith
  rw [ha0]; field_simp; ring

/-- The matching radius sits at acceleration `a₀` exactly when `η = (√3 - 1)/2`. -/
theorem matching_at_a0_iff (η : ℝ) (hη : 0 ≤ η) :
    2 * η * (1 + η) = 1 ↔ η = (Real.sqrt 3 - 1) / 2 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  constructor
  · intro h
    have h2 : (2 * η + 1) ^ 2 = 3 := by nlinarith
    have : Real.sqrt 3 = 2 * η + 1 := by
      rw [← h2, Real.sqrt_sq (by linarith)]
    linarith
  · intro h; rw [h]; nlinarith

/-- `y = D sin (k r - φ)` solves `y'' = -k² y`; with `ρ = y / r` this is the constant-`ζ`
hydrostatic envelope equation `ρ'' + 2 ρ' / r + k² ρ = 0` outside the sources. -/
theorem envelope_ode (D k φ r : ℝ) :
    HasDerivAt (fun r => D * Real.sin (k * r - φ)) (D * (Real.cos (k * r - φ) * k)) r ∧
    HasDerivAt (fun r => D * (Real.cos (k * r - φ) * k))
      (-(k ^ 2) * (D * Real.sin (k * r - φ))) r := by
  have hlin : HasDerivAt (fun r => k * r - φ) k r := by
    simpa using ((hasDerivAt_id r).const_mul k).sub_const φ
  refine ⟨(hlin.sin).const_mul D, ?_⟩
  have := ((hlin.cos).mul_const k).const_mul D
  convert this using 1; ring

/-- Antiderivative used for the envelope stock. -/
def stockPrimitive (k φ r : ℝ) : ℝ :=
  -r * Real.cos (k * r - φ) / k + Real.sin (k * r - φ) / k ^ 2

theorem stockPrimitive_deriv {k φ : ℝ} (hk : k ≠ 0) (r : ℝ) :
    HasDerivAt (stockPrimitive k φ) (r * Real.sin (k * r - φ)) r := by
  have hlin : HasDerivAt (fun r => k * r - φ) k r := by
    simpa using ((hasDerivAt_id r).const_mul k).sub_const φ
  have h1 := (((hasDerivAt_id r).neg).mul hlin.cos).div_const k
  have h2 := hlin.sin.div_const (k ^ 2)
  convert h1.add h2 using 1
  · funext x; simp [stockPrimitive]
  · simp; field_simp; ring

/-- Envelope stock `4π D ∫_a^R r sin (k r - φ) dr`, in closed form. -/
theorem envelope_mass {k φ a R : ℝ} (hk : k ≠ 0) :
    ∫ r in a..R, r * Real.sin (k * r - φ) = stockPrimitive k φ R - stockPrimitive k φ a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro r _; exact stockPrimitive_deriv hk r
  · apply Continuous.intervalIntegrable; fun_prop

/-- At the outer zero `k R - φ = π` and the matched inner phase `k a - φ = π - arctan q`
with `q = k a`, the stock integral is `(arctan q + q - 2 q / √(1+q²)) / k²`. -/
theorem envelope_mass_matched {k φ a R : ℝ} (hk : 0 < k) (ha : 0 < a)
    (hR : k * R - φ = Real.pi) (hA : k * a - φ = Real.pi - Real.arctan (k * a)) :
    stockPrimitive k φ R - stockPrimitive k φ a =
      (Real.arctan (k * a) + k * a - 2 * (k * a) / Real.sqrt (1 + (k * a) ^ 2)) / k ^ 2 := by
  have hRφ : R = (Real.pi + φ) / k := by field_simp; linarith
  have hq : 0 < k * a := mul_pos hk ha
  set q := k * a with hqdef
  have hφ : φ = q - (Real.pi - Real.arctan q) := by linarith
  have hs : 0 < Real.sqrt (1 + q ^ 2) := Real.sqrt_pos.mpr (by positivity)
  unfold stockPrimitive
  rw [hR, hA, Real.cos_pi, Real.sin_pi, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_arctan,
    Real.sin_arctan]
  have ha' : a = q / k := by rw [hqdef]; field_simp
  rw [hRφ, ha', hφ]
  field_simp
  ring

/-! ## 4. Extent: a lower bound on the stock ratio -/

/-- If the envelope edge satisfies `R ≤ 2 a` with `a = r_M / (2 η)`, `0 < η < 1`, and the
stock ratio is at least the inner value `(1 - η) / (2 η)`, then a stock that reaches
radius `L` needs `S ≥ (L / r_M - 1) / 2`. -/
theorem stock_ratio_lower_bound {rM η R L S : ℝ} (hr : 0 < rM) (hη : 0 < η)
    (hR : R ≤ 2 * (rM / (2 * η))) (hL : L ≤ R) (hS : (1 - η) / (2 * η) ≤ S) :
    (L / rM - 1) / 2 ≤ S := by
  have hLe : L / rM ≤ 1 / η := by
    rw [div_le_iff₀ hr]
    have : 2 * (rM / (2 * η)) = rM / η := by field_simp
    calc L ≤ R := hL
      _ ≤ rM / η := by linarith
      _ = 1 / η * rM := by ring
  have hS' : (1 - η) / (2 * η) = (1 / η - 1) / 2 := by field_simp
  linarith

/-! ## 5. Stock ratio bookkeeping -/

/-- Deep-RAR stock out to radius `R`: with enclosed stock `A R - M/2` and `A = M / r_M`,
the stock-to-baryon ratio is `R / r_M - 1/2`. -/
theorem isothermal_stock_ratio {M rM R : ℝ} (hM : 0 < M) (hr : 0 < rM) :
    ((M / rM) * R - M / 2) / M = R / rM - 1 / 2 := by
  field_simp

/-- Detected baryon fraction `M_b / (f_b M_tot)` with cosmic fraction `f_b = 1 / (1 + k)`
and total mass `M_b (1 + S)`: it equals `(1 + k) / (1 + S)`. -/
theorem detected_fraction_formula {k S Mb : ℝ} (hk : 0 < 1 + k) (hS : 0 < 1 + S)
    (hM : 0 < Mb) :
    Mb / ((1 / (1 + k)) * (Mb + S * Mb)) = (1 + k) / (1 + S) := by
  field_simp

/-- Retained fraction of ancestral baryons. If a galaxy keeps all of its cohort stock
`k B₀` and a fraction `f` of its ancestral baryons `B₀`, its stock ratio is `S = k / f`,
so `f = k / S`. -/
theorem retained_fraction {k S f B0 : ℝ} (hB : 0 < B0) (hS0 : 0 < S)
    (hS : S * (f * B0) = k * B0) : f = k / S := by
  have h1 : S * f = k := mul_right_cancel₀ hB.ne' (by rw [← hS]; ring)
  rw [eq_div_iff hS0.ne', mul_comm, h1]

/-- The detected fraction exceeds the retained fraction exactly when `k < S`:
`k / S < (1 + k) / (1 + S)` for `0 < k < S`. -/
theorem retained_lt_detected {k S : ℝ} (hk : 0 < k) (hkS : k < S) :
    k / S < (1 + k) / (1 + S) := by
  have hS : 0 < S := lt_trans hk hkS
  rw [div_lt_div_iff₀ hS (by linarith)]
  nlinarith

end Entropic.EnvelopePremises
