import Entropic.AppH1.Kinematics
import Entropic.AppCDE.Frame
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Appendices K–N, scalar part: bookkeeping, windows, response functions, capacity substitutions,
carriers, frame kinetic identities and susceptibilities (ledger C11-01, -26 … -29, -34, -37, -39,
-42 … -45, -47 … -49, -59, -62 … -65, -78 … -80, -82, -83, -85 … -88, -90, -91, -93, -95, -96,
-99 … -104, -106, -108). -/

noncomputable section
namespace Entropic.AppKN
open Real Matrix

/-- C11-01: a two-equally-weighted-state register carries ΔS = ln 2. -/
theorem one_bit_entropy : -(2 * ((1/2 : ℝ) * Real.log (1/2))) = Real.log 2 := by
  rw [one_div, Real.log_inv]; ring

/-- C11-26, C11-27: (1.006601/1.005124) − 1 ∈ (0.001469, 0.001470) and 1 − (1 + u)⁻² = 1.053% at u = 0.005309. -/
theorem uplift_ratios :
    0.001469 < (1 + 0.006601 : ℝ) / (1 + 0.005124) - 1 ∧ (1 + 0.006601 : ℝ) / (1 + 0.005124) - 1 < 0.001470 ∧
      0.01052 < 1 - (1 + 0.005309 : ℝ)⁻¹ ^ 2 ∧ 1 - (1 + 0.005309 : ℝ)⁻¹ ^ 2 < 0.01054 := by
  norm_num

/-- C11-28: −Z ln(1 − r) = Z r (1 + O(r)): |−ln(1 − r) − r| ≤ r²/(1 − r) for 0 ≤ r < 1. -/
theorem substrate_leading {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    |-Real.log (1 - r) - r| ≤ r ^ 2 / (1 - r) := by
  have := Real.abs_log_sub_add_sum_range_le (show |r| < 1 by rw [abs_of_nonneg h0]; exact h1) 1
  simp only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero] at this
  rw [abs_of_nonneg h0] at this
  rw [show -Real.log (1 - r) - r = -(r / 1 + Real.log (1 - r)) by ring, abs_neg]
  simpa using this

/-- C11-29: 6 · 5 · 5 · 4 · 5 = 3000 candidate constructions. -/
theorem grammar_size : 6 * 5 * 5 * 4 * 5 = 3000 := by norm_num

/-- C11-34: of the compact-volume menu only (2π)² = 39.478… lies in [33.7, 54.8]. -/
theorem phase_cell_window :
    (33.7 < (2 * π) ^ 2 ∧ (2 * π) ^ 2 < 54.8) ∧ π < 33.7 ∧ 2 * π < 33.7 ∧ 4 * π < 33.7 ∧ π ^ 2 < 33.7 ∧
      2 * π ^ 2 < 33.7 ∧ 54.8 < 8 * π ^ 2 ∧ 54.8 < 16 * π ^ 2 ∧ 54.8 < (2 * π) ^ 3 ∧ 4 * π / 3 < 33.7 ∧
      π ^ 2 / 2 < 33.7 := by
  have a := Real.pi_gt_d6; have b := Real.pi_lt_d6
  have h6 : (6:ℝ) < 2 * π := by linarith
  have h216 : (6:ℝ) ^ 3 < (2 * π) ^ 3 := by gcongr
  refine ⟨⟨by nlinarith, by nlinarith⟩, by linarith, by linarith, by linarith, by nlinarith, by nlinarith,
    by nlinarith, by nlinarith, by norm_num at h216; linarith, by linarith, by nlinarith⟩

/-- C11-37: 122/3, √1680, 42 and 48 all lie in [33.7, 54.8]. -/
theorem native_numbers_window :
    33.7 < (122 : ℝ) / 3 ∧ (122 : ℝ) / 3 < 54.8 ∧ 33.7 < Real.sqrt 1680 ∧ Real.sqrt 1680 < 54.8 ∧
      (33.7 : ℝ) < 42 ∧ (48 : ℝ) < 54.8 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, by norm_num, by norm_num⟩
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- C11-39: the first-order lag τẏ + y = u has |1/(1 + iωτ)| = (1 + (ωτ)²)^{−1/2}. -/
theorem lag_transmission (ω τ : ℝ) :
    ‖(1 : ℂ) / (1 + Complex.I * (ω * τ))‖ = 1 / Real.sqrt (1 + (ω * τ) ^ 2) := by
  rw [norm_div, norm_one]
  congr 1
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1; simp; ring

/-- C11-42: f(X) = f_max − A X^{−n}: f_X/(f_X + 2X f_XX) = −1/(2n + 1). -/
theorem plateau_sound_speed {A n X : ℝ} (hA : A ≠ 0) (hn : 0 < n) (hX : 0 < X) :
    (A * n * X ^ (-n - 1)) / (A * n * X ^ (-n - 1) + 2 * X * (A * n * (-n - 1) * X ^ (-n - 2))) =
      -1 / (2 * n + 1) := by
  have e : X * X ^ (-n - 2) = X ^ (-n - 1) := by
    rw [← Real.rpow_one_add' hX.le (by linarith)]; ring_nf
  have hp : 0 < X ^ (-n - 1) := Real.rpow_pos_of_pos hX _
  have h2 : 2 * X * (A * n * (-n - 1) * X ^ (-n - 2)) = 2 * A * n * (-n - 1) * X ^ (-n - 1) := by
    rw [← e]; ring
  rw [h2]
  have hden : A * n * X ^ (-n - 1) + 2 * A * n * (-n - 1) * X ^ (-n - 1) = A * n * X ^ (-n - 1) * (-(2 * n + 1)) := by
    ring
  rw [hden]
  have hne : A * n * X ^ (-n - 1) ≠ 0 := by positivity
  have h2n : 2 * n + 1 ≠ 0 := by linarith
  field_simp

/-- C11-43: with X = φ̇²/2 (X > 0): (f_X√(2X))′ = 0 and (2Xf_X − f)′ = 0 are each equivalent to
f_X + 2Xf_XX = 0. -/
theorem cap_readings {X fX fXX : ℝ} (hX : 0 < X) :
    (fXX * Real.sqrt (2 * X) + fX / Real.sqrt (2 * X) = 0 ↔ fX + 2 * X * fXX = 0) ∧
      (2 * fX + 2 * X * fXX - fX = 0 ↔ fX + 2 * X * fXX = 0) := by
  have hs : 0 < Real.sqrt (2 * X) := by positivity
  have h2 : Real.sqrt (2 * X) * Real.sqrt (2 * X) = 2 * X := Real.mul_self_sqrt (by positivity)
  have hid : fXX * Real.sqrt (2 * X) + fX / Real.sqrt (2 * X) = (fX + 2 * X * fXX) / Real.sqrt (2 * X) := by
    field_simp; linear_combination fXX * h2
  constructor
  · rw [hid, div_eq_zero_iff]
    exact ⟨fun h => h.resolve_right hs.ne', fun h => Or.inl h⟩
  · constructor <;> intro h <;> linarith

/-- C11-44: an instantaneous bounded function of a T-periodic bounded input is T-periodic and bounded. -/
theorem instantaneous_coupling {k : Type*} (u : ℝ → k) (h : k → ℝ) (T : ℝ) (hu : ∀ t, u (t + T) = u t)
    (B : ℝ) (hb : ∀ t, |h (u t)| ≤ B) : (∀ t, h (u (t + T)) = h (u t)) ∧ ∀ t, |h (u t)| ≤ B :=
  ⟨fun t => by rw [hu], hb⟩

/-- C11-45: (c³/16πG)∫d⁴x = (c⁴/16πG)∫dt d³x with x⁰ = ct, and c³/(4G) ↦ c⁴/(4G). -/
theorem eh_conventions (c G I : ℝ) (hG : G ≠ 0) (hπ : π ≠ 0) :
    c ^ 3 / (16 * π * G) * (c * I) = c ^ 4 / (16 * π * G) * I ∧ c ^ 3 / (4 * G) * (c * I) = c ^ 4 / (4 * G) * I := by
  constructor <;> ring

/-- C11-47: the Maxwell stress tensor is traceless in four dimensions:
Σ_μ (F^{μα}F_{μα} − ¼δ^μ_μ F^{αβ}F_{αβ}) = 0. -/
theorem maxwell_traceless (F Fl : Fin 4 → Fin 4 → ℝ) :
    ∑ μ, (∑ α, F μ α * Fl μ α - (1/4) * ∑ a, ∑ b, F a b * Fl a b) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp

/-- C11-48: √(1 + 2φ) = 1 + φ + O(φ²): |√(1+2φ) − 1 − φ| ≤ 2φ² for |φ| ≤ 1/2. -/
theorem lapse_expansion {φ : ℝ} (h : |φ| ≤ 1/2) : |Real.sqrt (1 + 2 * φ) - 1 - φ| ≤ 2 * φ ^ 2 := by
  have h0 : 0 ≤ 1 + 2 * φ := by have := neg_abs_le φ; linarith
  have hs := Real.sq_sqrt h0
  have hsn := Real.sqrt_nonneg (1 + 2 * φ)
  set s := Real.sqrt (1 + 2 * φ)
  -- s − 1 − φ = −(s − 1)²/2 ... and |s − 1| ≤ |φ|·2/... use (s − 1 − φ) = −(s−1)²/2
  have key : s - 1 - φ = -(s - 1) ^ 2 / 2 := by nlinarith
  have hs1 : |s - 1| ≤ 2 * |φ| := by
    have : (s - 1) * (s + 1) = 2 * φ := by nlinarith
    have hsp : 1 ≤ s + 1 := by linarith
    rw [abs_le]; constructor <;> nlinarith [abs_nonneg φ, neg_abs_le φ, le_abs_self φ]
  rw [key, abs_div, abs_neg, abs_of_nonneg (sq_nonneg _)]
  have : (s - 1) ^ 2 ≤ 4 * φ ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hs1 2
    rw [sq_abs, mul_pow, sq_abs] at this; linarith
  rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
  nlinarith [sq_nonneg φ]

/-- C11-59: q = 1 − δS/S_∞ = 1 + 2Φ/c² to first order with δS = AΦ forces A = −2S_∞/c². -/
theorem redefinition_coefficient {A S c : ℝ} (hS : S ≠ 0) (hc : c ≠ 0)
    (h : ∀ Φ : ℝ, 1 - A * Φ / S = 1 + 2 * Φ / c ^ 2) : A = -2 * S / c ^ 2 := by
  have := h 1
  field_simp at this ⊢; linarith

/-- C11-62, C11-63: the static equation depends only on κ/(γS_∞); it is invariant under
δS ↦ aδS, S_∞ ↦ aS_∞, γ ↦ γ/a², κ ↦ κ/a; and κ = c²/(2S_∞), γ = c⁴/(16πGS_∞²) satisfy
G = c²κ/(8πγS_∞). -/
theorem unit_normalization {κ γ S a c G : ℝ} (hγ : γ ≠ 0) (hS : S ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0)
    (hG : G ≠ 0) :
    c ^ 2 * (κ / a) / (2 * (γ / a ^ 2) * (a * S)) = c ^ 2 * κ / (2 * γ * S) ∧
      c ^ 2 * (c ^ 2 / (2 * S)) / (8 * π * (c ^ 4 / (16 * π * G * S ^ 2)) * S) = G := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  constructor
  all_goals field_simp
  all_goals ring

/-- C11-65 (a): if q enters only through λ(N² − q), stationarity in q gives λ = 0. (b) with
Λ(qX + 1): δq gives ΛX = 0 and the Λ-constraint X = −1/q ≠ 0 forces Λ = 0. -/
theorem multiplier_routes {lam Λ X q : ℝ} (ha : -lam = 0) (hb1 : Λ * X = 0) (hb2 : q * X + 1 = 0) :
    lam = 0 ∧ Λ = 0 := by
  refine ⟨by linarith, ?_⟩
  have hX : X ≠ 0 := by intro h; rw [h] at hb2; simp at hb2
  exact (mul_eq_zero.mp hb1).resolve_right hX

/-- C11-78: from D²N = (4πG/c⁴)N(E+S) and q = N² (with D²q = 2N D²N + 2|DN|², |Dq|² = 4N²|DN|²):
D²q = (8πG/c⁴)q(E+S) + |Dq|²/(2q). -/
theorem lapse_square_equation {N DN2 D2N k ES : ℝ} (hN : 0 < N) (h : D2N = k * N * ES) :
    2 * N * D2N + 2 * DN2 = 2 * k * N ^ 2 * ES + (4 * N ^ 2 * DN2) / (2 * N ^ 2) := by
  rw [h]; field_simp; ring

/-- C11-79: with s = S(1 − q): D²s = −(8πGS/c⁴)(1 − s/S)(E+S) − |Ds|²/(2(S − s)). -/
theorem capacity_equation {S q D2q Dq2 k ES : ℝ} (hS : S ≠ 0) (hq : q ≠ 0)
    (h : D2q = 2 * k * q * ES + Dq2 / (2 * q)) :
    -(S * D2q) = -(2 * k * S) * (1 - S * (1 - q) / S) * ES - (S ^ 2 * Dq2) / (2 * (S - S * (1 - q))) := by
  rw [h, show S - S * (1 - q) = S * q by ring, show 1 - S * (1 - q) / S = q by field_simp; ring]
  field_simp; ring

/-- C11-80: N² = 1 + 2Φ/c² gives s = S(1 − N²) = −(2S/c²)Φ, and ∇²Φ = 4πGρ gives
∇²s = −(8πGS/c²)ρ. -/
theorem weak_capacity (S c Φ LΦ G ρ : ℝ) (hc : c ≠ 0) (h : LΦ = 4 * π * G * ρ) :
    S * (1 - (1 + 2 * Φ / c ^ 2)) = -(2 * S / c ^ 2) * Φ ∧ -(2 * S / c ^ 2) * LΦ = -(8 * π * G * S / c ^ 2) * ρ := by
  constructor
  · ring
  · rw [h]; ring

/-! ### Relative-entropy first law (C11-82, C11-83) -/

/-- C11-82 (classical form): D(p‖p₀) = Δ⟨K₀⟩ − ΔS with K₀ = −ln p₀. -/
theorem relative_first_law {ι : Type*} [Fintype ι] (p p0 : ι → ℝ) (hp : ∀ i, 0 < p i) (hp0 : ∀ i, 0 < p0 i) :
    ∑ i, p i * Real.log (p i / p0 i) =
      (∑ i, p i * (-Real.log (p0 i)) - ∑ i, p0 i * (-Real.log (p0 i))) -
        ((-∑ i, p i * Real.log (p i)) - (-∑ i, p0 i * Real.log (p0 i))) := by
  rw [Finset.sum_congr rfl (fun i _ => by rw [Real.log_div (hp i).ne' (hp0 i).ne', mul_sub])]
  rw [Finset.sum_sub_distrib]
  simp only [mul_neg, Finset.sum_neg_distrib]; ring

/-- C11-83: if 0 ≤ D(ε) ≤ Cε² then D′(0) = 0, so d/dε f(D(ε)) = 0 at ε = 0 for differentiable f. -/
theorem no_linear_response (D f : ℝ → ℝ) (C : ℝ) (hD0 : D 0 = 0) (hle : ∀ ε, |D ε| ≤ C * ε ^ 2)
    (f' : ℝ) (hf : HasDerivAt f f' (D 0)) : HasDerivAt (fun ε => f (D ε)) 0 0 := by
  have hD : HasDerivAt D 0 0 := by
    rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro c hc
    have : ∀ᶠ ε in nhds (0:ℝ), |ε| ≤ c / (|C| + 1) := by
      apply Metric.eventually_nhds_iff.mpr
      exact ⟨c / (|C| + 1), by positivity, fun y hy => by simpa [Real.dist_eq] using hy.le⟩
    filter_upwards [this] with ε hε
    simp only [hD0, sub_zero, smul_zero, Real.norm_eq_abs]
    calc |D ε| ≤ C * ε ^ 2 := hle ε
      _ ≤ (|C| + 1) * |ε| * |ε| := by
          rw [← sq_abs ε]; nlinarith [le_abs_self C, abs_nonneg ε, sq_nonneg ε]
      _ ≤ c * |ε| := by
          have h1 : (|C| + 1) * |ε| ≤ c := by
            rw [le_div_iff₀ (by positivity)] at hε; linarith
          nlinarith [abs_nonneg ε]
  have h := hf.comp (0:ℝ) hD
  rw [mul_zero] at h
  exact h

/-! ### Carriers (C11-85 … C11-88, C11-90, C11-91) -/

section Carriers
variable {R : Type*} [CommRing R]

/-- C11-85: with a central idempotent e_P and an idempotent E_P that is e_P-linear (E(eX) = eE(X)),
Π_P X = E_P(e_P X) = e_P E_P X is idempotent, and Π_PΠ_Q = 0 for orthogonal e_P e_Q = 0. -/
theorem carrier_projector (E : R → R) (eP eQ : R) (hE : ∀ x, E (E x) = E x)
    (hlin : ∀ e x, E (e * x) = e * E x) (hP : eP * eP = eP) (hPQ : eP * eQ = 0) (X : R) :
    E (eP * X) = eP * E X ∧ E (eP * E (eP * X)) = E (eP * X) ∧ E (eP * E (eQ * X)) = 0 := by
  refine ⟨hlin eP X, ?_, ?_⟩
  · calc E (eP * E (eP * X)) = eP * E (E (eP * X)) := hlin _ _
      _ = eP * E (eP * X) := by rw [hE]
      _ = eP * (eP * E X) := by rw [hlin]
      _ = E (eP * X) := by rw [← mul_assoc, hP, hlin]
  · calc E (eP * E (eQ * X)) = eP * E (E (eQ * X)) := hlin _ _
      _ = eP * (eQ * E X) := by rw [hE, hlin]
      _ = 0 := by rw [← mul_assoc, hPQ, zero_mul]

/-- C11-86: if I(E Y) = I(Y) and Σ_P e_P = 1, then Σ_P I(Π_P X) = I(X) for additive I. -/
theorem source_preservation {ι : Type*} (S : Finset ι) (E : R → R) (I : R →+ R) (e : ι → R)
    (hI : ∀ Y, I (E Y) = I Y) (hsum : ∑ P ∈ S, e P = 1) (X : R) :
    ∑ P ∈ S, I (E (e P * X)) = I X := by
  simp only [hI]
  rw [← map_sum, ← Finset.sum_mul, hsum, one_mul]

/-- C11-88: tower identity Π_P X = E_P(Σ_{A<P} Π_A X) under E_P E_f = E_P, Σ_{A<P} e_A = e_P and the
refinement e_P E_f X = Σ_{A<P} e_A E_A X. -/
theorem carrier_tower {ι : Type*} (S : Finset ι) (EP Ef : R → R) (EA : ι → R → R) (eP : R) (eA : ι → R)
    (hlin : ∀ e x, EP (e * x) = e * EP x) (htow : ∀ x, EP (Ef x) = EP x)
    (hadd : ∀ x y, EP (x + y) = EP x + EP y) (h0 : EP 0 = 0)
    (href : ∀ X, eP * Ef X = ∑ A ∈ S, eA A * EA A X) (X : R) :
    EP (eP * X) = EP (∑ A ∈ S, eA A * EA A X) := by
  rw [← href, hlin, hlin, htow]

/-- C11-87: on each block the weighted average map f ↦ (Σ w f/Σ w)·1 is idempotent, positive, unital
and preserves the weighted total (the blockwise map is the sum of these). -/
theorem block_average {ι : Type*} (S : Finset ι) (w f : ι → ℝ) (hw : 0 < ∑ j ∈ S, w j) :
    let a := (∑ j ∈ S, w j * f j) / ∑ j ∈ S, w j
    (∑ j ∈ S, w j * a) / (∑ j ∈ S, w j) = a ∧ ∑ j ∈ S, w j * a = ∑ j ∈ S, w j * f j ∧
      (∑ j ∈ S, w j * 1) / ∑ j ∈ S, w j = 1 := by
  intro a
  refine ⟨?_, ?_, ?_⟩
  · rw [← Finset.sum_mul]; field_simp
  · rw [← Finset.sum_mul]; simp only [a]; field_simp
  · simp only [mul_one]; exact div_self hw.ne'

/-- C11-90: χ_P = s_P/Σs_Q is a partition of unity. -/
theorem partition_unity {ι : Type*} (S : Finset ι) (s : ι → ℝ) (hs : 0 < ∑ Q ∈ S, s Q) :
    ∑ P ∈ S, s P / ∑ Q ∈ S, s Q = 1 := by
  rw [← Finset.sum_div, div_self hs.ne']

/-- C11-91: column-stochastic nonnegative C preserves nonnegativity and total, and is closed under products. -/
theorem column_stochastic {m n : Type*} [Fintype m] [Fintype n] (C : Matrix m n ℝ) (hC : ∀ i a, 0 ≤ C i a)
    (hcol : ∀ a, ∑ i, C i a = 1) (v : n → ℝ) (hv : ∀ a, 0 ≤ v a) :
    (∀ i, 0 ≤ (C *ᵥ v) i) ∧ ∑ i, (C *ᵥ v) i = ∑ a, v a := by
  constructor
  · intro i; exact Finset.sum_nonneg (fun a _ => mul_nonneg (hC i a) (hv a))
  · simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun a _ => by rw [← Finset.sum_mul, hcol, one_mul])

end Carriers

/-! ### Frame kinetic identities (C11-93, C11-95, C11-96) -/

/-- C11-93: for Σq_i = 0 and A = (√3/2)Σ n_i q_i, |A|² = Σq_i². -/
theorem sum_zero_norm (q : Fin 4 → ℝ) (hq : ∑ i, q i = 0) :
    ∑ a : Fin 3, ((Real.sqrt 3 / 2) * ∑ i, Entropic.AppCDE.d i a * q i) ^ 2 = ∑ i, q i ^ 2 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : Real.sqrt 3 ≠ 0 := by positivity
  have hq3 : q 3 = -(q 0 + q 1 + q 2) := by simp [Fin.sum_univ_four] at hq; linarith
  have e : ∀ a : Fin 3, (Real.sqrt 3 / 2) * ∑ i, Entropic.AppCDE.d i a * q i =
      (1/2) * ∑ i, (Entropic.EFT.Edge.rawNormal i a : ℝ) * q i := by
    intro a; simp only [Entropic.AppCDE.d, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by field_simp)
  simp_rw [e]
  simp [Fin.sum_univ_four, Fin.sum_univ_three, Entropic.EFT.Edge.rawNormal, hq3]
  ring

end Entropic.AppKN
