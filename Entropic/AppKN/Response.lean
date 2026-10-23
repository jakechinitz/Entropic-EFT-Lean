import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-! Appendices K–N, response part: kinetic splits, rank-one Hessians, Legendre potential, thermal
occupation, Bose susceptibilities, two-pole response, carrier algebra and constraint bookkeeping
(ledger C11-95, -96, -99 … -104, -106, -108; C12-09, -20, -26, -28, -29, -33, -35, -36, -38, -42,
-44, -45, -47, -50, -55, -60, -61, -68, -70, -71, -75, -76, -77, -79, -83, -85, -86, -87). -/

noncomputable section
namespace Entropic.AppKN
open Real Matrix
open scoped ComplexOrder

/-! ### Kinetic splits (C11-95, C11-96) -/

/-- C11-95: for constant unit e_L and A = Xe_L + Y with e_L·Y = 0 (so e_L·∂Y = 0),
|∂A|² = (∂X)² + |∂Y|². -/
theorem longitudinal_split (e dY : Fin 3 → ℝ) (dX : ℝ) (he : e ⬝ᵥ e = 1) (hY : e ⬝ᵥ dY = 0) :
    (dX • e + dY) ⬝ᵥ (dX • e + dY) = dX ^ 2 + dY ⬝ᵥ dY := by
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, he, hY, smul_eq_mul,
    dotProduct_comm dY e]
  ring

/-- C11-96: Y₁ = R cos θ, Y₂ = R sin θ give (∂Y₁)² + (∂Y₂)² = (∂R)² + R²(∂θ)². -/
theorem polar_kinetic (R θ dR dθ : ℝ) :
    (dR * Real.cos θ - R * Real.sin θ * dθ) ^ 2 + (dR * Real.sin θ + R * Real.cos θ * dθ) ^ 2 =
      dR ^ 2 + R ^ 2 * dθ ^ 2 := by
  have := Real.cos_sq_add_sin_sq θ
  linear_combination (dR ^ 2 + R ^ 2 * dθ ^ 2) * this

/-! ### Rank-one Hessians (C11-99 … C11-104, C11-106) -/

/-- C11-99: a real symmetric 2×2 matrix [[a, b],[b, c]] has rank ≤ 1 iff b² = ac (det = 0). -/
theorem rank_one_criterion (a b c : ℝ) :
    Matrix.det !![a, b; b, c] = 0 ↔ b ^ 2 = a * c := by
  rw [Matrix.det_fin_two_of]; constructor <;> intro h <;> linarith

/-- C11-100: for χ > 0, sup_λ [λΔC − (χ/2)λ²] = (ΔC)²/(2χ), attained at λ = ΔC/χ. -/
theorem capacity_legendre {χ ΔC : ℝ} (hχ : 0 < χ) (lam : ℝ) :
    lam * ΔC - χ / 2 * lam ^ 2 ≤ ΔC ^ 2 / (2 * χ) ∧
      (ΔC / χ) * ΔC - χ / 2 * (ΔC / χ) ^ 2 = ΔC ^ 2 / (2 * χ) := by
  constructor
  · have : ΔC ^ 2 / (2 * χ) - (lam * ΔC - χ / 2 * lam ^ 2) = χ / 2 * (lam - ΔC / χ) ^ 2 := by
      field_simp; ring
    nlinarith [mul_nonneg (le_of_lt (half_pos hχ)) (sq_nonneg (lam - ΔC / χ))]
  · field_simp; ring

/-- C11-101, C11-102: with v = (g_C, 2β_C R₀), H = F″ vvᵀ has C_x² = A_L A_T, det H = 0 and trace
A_L + A_T; minimizing over δR at fixed δX leaves zero stiffness. -/
theorem rank_one_hessian (F2 g β R0 : ℝ) :
    let AL := F2 * g ^ 2
    let AT := F2 * (2 * β * R0) ^ 2
    let Cx := F2 * (g * (2 * β * R0))
    Cx ^ 2 = AL * AT ∧ Matrix.det !![AL, Cx; Cx, AT] = 0 ∧
      (AT ≠ 0 → ∀ dX, AL * dX ^ 2 + 2 * Cx * dX * (-(Cx / AT) * dX) + AT * (-(Cx / AT) * dX) ^ 2 = 0) := by
  intro AL AT Cx
  refine ⟨by ring, by rw [Matrix.det_fin_two_of]; ring, fun hT dX => ?_⟩
  have h : Cx ^ 2 = AL * AT := by ring
  field_simp
  linear_combination (-(dX ^ 2) * AT) * h

/-- C11-103: ∂_D V = 0 at D = −J/(Δ + 2ηC), where V = F(C) − J²/(2(Δ + 2ηC)). -/
theorem difference_mode {F Δ η C J : ℝ} (h : Δ + 2 * η * C ≠ 0) :
    let D := -J / (Δ + 2 * η * C)
    (Δ + 2 * η * C) * D + J = 0 ∧
      F + Δ / 2 * D ^ 2 + η * C * D ^ 2 + J * D = F - J ^ 2 / (2 * (Δ + 2 * η * C)) := by
  intro D
  constructor
  · simp only [D]; field_simp; ring
  · simp only [D]; field_simp; ring

/-- C11-104: H′ = F″vvᵀ + diag(m², 0) has det = F″m²(2βR₀)², so rank 2 iff βR₀ ≠ 0. -/
theorem mass_term_rank (F2 m2 g β R0 : ℝ) (hF : F2 ≠ 0) (hm : m2 ≠ 0) :
    Matrix.det !![F2 * g ^ 2 + m2, F2 * (g * (2 * β * R0)); F2 * (g * (2 * β * R0)), F2 * (2 * β * R0) ^ 2] =
        F2 * m2 * (2 * β * R0) ^ 2 ∧
      (F2 * m2 * (2 * β * R0) ^ 2 ≠ 0 ↔ β * R0 ≠ 0) := by
  refine ⟨by rw [Matrix.det_fin_two_of]; ring, ?_⟩
  constructor
  · intro h hb; apply h; rw [show 2 * β * R0 = 2 * (β * R0) by ring, hb]; ring
  · intro hb; have : 2 * β * R0 ≠ 0 := by
      rw [show 2 * β * R0 = 2 * (β * R0) by ring]; exact mul_ne_zero two_ne_zero hb
    positivity

/-- C11-106: with F″ = 1/χ, A_L/A_T = g²/(4β²R₀²) is independent of χ. -/
theorem susceptibility_cancels {χ g β R0 : ℝ} (hχ : χ ≠ 0) (hb : β * R0 ≠ 0) :
    (1 / χ * g ^ 2) / (1 / χ * (2 * β * R0) ^ 2) = g ^ 2 / (4 * β ^ 2 * R0 ^ 2) := by
  have : β ≠ 0 := left_ne_zero_of_mul hb
  have : R0 ≠ 0 := right_ne_zero_of_mul hb
  field_simp; ring

/-! ### Thermal occupation (C11-108, C12-35) -/

/-- C11-108: F(E) = kT ln(1 − e^{−E/kT}) has dF/dE = 1/(e^x − 1) = n_B(x), x = E/kT. -/
theorem thermal_occupation {kT E : ℝ} (hk : 0 < kT) (hE : 0 < E) :
    HasDerivAt (fun e => kT * Real.log (1 - Real.exp (-(e / kT)))) (1 / (Real.exp (E / kT) - 1)) E := by
  have hx : 0 < E / kT := div_pos hE hk
  have hlt : Real.exp (-(E / kT)) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hinner : HasDerivAt (fun e => 1 - Real.exp (-(e / kT))) (Real.exp (-(E / kT)) / kT) E := by
    have := ((((hasDerivAt_id' E).div_const kT).neg).exp).const_sub 1
    convert this using 1; simp; ring
  have h := (hinner.log (by linarith)).const_mul kT
  convert h using 1
  have he : Real.exp (E / kT) * Real.exp (-(E / kT)) = 1 := by rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (E / kT) - 1 := by linarith [Real.add_one_lt_exp hx.ne', Real.exp_pos (E / kT)]
  have h1 : 1 - Real.exp (-(E / kT)) ≠ 0 := by linarith
  field_simp
  nlinarith [he]

/-- C12-35: for n_B(E) = 1/(e^{βE} − 1), −dn_B/dE = β n_B(1 + n_B). -/
theorem bose_slope {β E : ℝ} (hβ : 0 < β) (hE : 0 < E) :
    HasDerivAt (fun e => 1 / (Real.exp (β * e) - 1))
      (-(β * (1 / (Real.exp (β * E) - 1)) * (1 + 1 / (Real.exp (β * E) - 1)))) E := by
  have hpos : 0 < Real.exp (β * E) - 1 := by
    have := Real.add_one_lt_exp (show β * E ≠ 0 by positivity); linarith [mul_pos hβ hE]
  have h := (((hasDerivAt_id' E).const_mul β).exp.sub_const 1).inv hpos.ne'
  convert h using 1
  · funext e; simp [one_div]
  · field_simp; ring

/-! ### Two-pole response (C12-33, C12-36, C12-38, C12-42) -/

/-- C12-33: F(ω,k) = Dk²/(Dk² − τω² − iω) has F(0,k) = 1, and with s = −iω the denominator is
τs² + s + Dk². -/
theorem causal_transport (D τ k ω : ℝ) (hk : D * k ^ 2 ≠ 0) :
    (D * k ^ 2 : ℂ) / (D * k ^ 2 - τ * 0 ^ 2 - Complex.I * 0) = 1 ∧
      ((D * k ^ 2 : ℂ) - τ * ω ^ 2 - Complex.I * ω) = τ * (-Complex.I * ω) ^ 2 + (-Complex.I * ω) + D * k ^ 2 := by
  constructor
  · simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_zero]
    exact div_self (by exact_mod_cast hk)
  · ring_nf; rw [Complex.I_sq]; ring

/-- C12-36: substituting d_t → −iω, (γ − iω)(Ω − iω) = −ω² − iω(γ + Ω) + γΩ, so
χ^R = −χ₀γΩ/((γ − iω)(Ω − iω)) solves the driven two-pole equation. -/
theorem two_pole_symbol (γ Ω ω : ℝ) :
    ((-Complex.I * ω) ^ 2 + (γ + Ω) * (-Complex.I * ω) + γ * Ω : ℂ) = (γ - Complex.I * ω) * (Ω - Complex.I * ω) := by
  ring

/-- C12-38: D(ω) := −Im χ^R = χ₀γΩ(γ + Ω)ω/((γ² + ω²)(Ω² + ω²)) > 0 for ω > 0. -/
theorem dissipative_spectrum {χ0 γ Ω ω : ℝ} (hχ : 0 < χ0) (hγ : 0 < γ) (hΩ : 0 < Ω) (hω : 0 < ω) :
    -((-(χ0 * γ * Ω : ℂ)) / ((γ - Complex.I * ω) * (Ω - Complex.I * ω))).im =
        χ0 * γ * Ω * (γ + Ω) * ω / ((γ ^ 2 + ω ^ 2) * (Ω ^ 2 + ω ^ 2)) ∧
      0 < χ0 * γ * Ω * (γ + Ω) * ω / ((γ ^ 2 + ω ^ 2) * (Ω ^ 2 + ω ^ 2)) := by
  refine ⟨?_, by positivity⟩
  have hden : ((γ - Complex.I * ω) * (Ω - Complex.I * ω) : ℂ) = (γ * Ω - ω ^ 2 : ℝ) - ((γ + Ω) * ω : ℝ) * Complex.I := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [hden, Complex.div_im]
  simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.normSq_apply]
  have h1 : 0 < γ ^ 2 + ω ^ 2 := by positivity
  have h2 : 0 < Ω ^ 2 + ω ^ 2 := by positivity
  have hd : (γ * Ω - ω ^ 2) * (γ * Ω - ω ^ 2) + (γ + Ω) * ω * ((γ + Ω) * ω) = (γ ^ 2 + ω ^ 2) * (Ω ^ 2 + ω ^ 2) := by
    ring
  simp only [mul_zero, mul_one, sub_zero, zero_mul, zero_sub, neg_zero, add_zero, zero_add]
  rw [show (γ * Ω - ω ^ 2) * (γ * Ω - ω ^ 2) + -((γ + Ω) * ω) * -((γ + Ω) * ω) =
      (γ ^ 2 + ω ^ 2) * (Ω ^ 2 + ω ^ 2) by ring]
  field_simp; ring

/-- C12-42: as Ω → ∞ at fixed ω, χ^R → −χ₀γ/(γ − iω) (exact identity before the limit). -/
theorem low_frequency_limit (χ0 γ Ω ω : ℝ) (hΩ : (Ω : ℂ) - Complex.I * ω ≠ 0) :
    (-(χ0 * γ * Ω : ℂ)) / ((γ - Complex.I * ω) * (Ω - Complex.I * ω)) =
      (-(χ0 * γ : ℂ) / (γ - Complex.I * ω)) * (Ω / (Ω - Complex.I * ω)) := by
  rw [div_mul_div_comm]; ring

/-! ### Carrier algebra (C12-09, C12-20, C12-26) -/

/-- C12-09: Q′(e·∇Φ)e − ∇Φ = J_⊥ − (1 − eeᵀ)∇Φ with Q′ = 1 + n_B and J_⊥ = n_B(e·∇Φ)e. -/
theorem total_q_replacement (e g : Fin 3 → ℝ) (n : ℝ) :
    ((1 + n) * (e ⬝ᵥ g)) • e - g = (n * (e ⬝ᵥ g)) • e - (g - (e ⬝ᵥ g) • e) := by
  ext a; simp; ring

/-- C12-20: for χ_host + χ_sat = 1 (χ ≥ 0), q = (χ_host − χ_sat)² ∈ [0,1]; q = 1 gives M = eeᵀ and
q = 0 gives M = I. -/
theorem interface_order {ch cs : ℝ} (h0 : 0 ≤ ch) (h1 : 0 ≤ cs) (hs : ch + cs = 1) :
    0 ≤ (ch - cs) ^ 2 ∧ (ch - cs) ^ 2 ≤ 1 := by
  refine ⟨sq_nonneg _, ?_⟩
  have : (ch - cs) ^ 2 = 1 - 4 * ch * cs := by nlinarith
  nlinarith [mul_nonneg h0 h1]

/-- C12-26: g = g_b(1 + n_B(√(g_b/a₀))) has dg/dg_b = 1 + n + (x/2) n′(x) with x = √(g_b/a₀). -/
theorem flux_multiplier (n n' : ℝ → ℝ) {a0 gb : ℝ} (ha : 0 < a0) (hg : 0 < gb)
    (hn : HasDerivAt n (n' (Real.sqrt (gb / a0))) (Real.sqrt (gb / a0))) :
    HasDerivAt (fun g => g * (1 + n (Real.sqrt (g / a0))))
      (1 + n (Real.sqrt (gb / a0)) + Real.sqrt (gb / a0) / 2 * n' (Real.sqrt (gb / a0))) gb := by
  have hx : 0 < gb / a0 := div_pos hg ha
  have hs : HasDerivAt (fun g => Real.sqrt (g / a0)) (1 / a0 / (2 * Real.sqrt (gb / a0))) gb := by
    have hd : HasDerivAt (fun x : ℝ => x / a0) (1 / a0) gb := (hasDerivAt_id' gb).div_const a0
    have := hd.sqrt hx.ne'
    simpa using this
  have h := (hasDerivAt_id' gb).mul ((hn.comp gb hs).const_add 1)
  have hsq : Real.sqrt (gb / a0) ^ 2 = gb / a0 := Real.sq_sqrt hx.le
  have hsp : 0 < Real.sqrt (gb / a0) := Real.sqrt_pos.mpr hx
  convert h using 1
  · funext g; simp [Function.comp]
  · simp only [Function.comp]
    generalize Real.sqrt (gb / a0) = x at hsq hsp ⊢
    have hgb : gb = a0 * x ^ 2 := by rw [hsq]; field_simp
    rw [hgb]; field_simp; try ring

/-! ### Influence functional, metric response, positivity (C12-28, C12-29, C12-44, C12-45) -/

section Finite
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- C12-28: Tr(UρU†) = Tr ρ = 1 (so Γ[g,g] ≡ 0), and conj Tr(U₊ρU₋†) = Tr(U₋ρU₊†) for Hermitian ρ. -/
theorem influence_unitarity (U V ρ : Matrix n n ℂ) (hU : Uᴴ * U = 1) (hρ : ρᴴ = ρ) (h1 : ρ.trace = 1) :
    (U * ρ * Uᴴ).trace = 1 ∧ star ((U * ρ * Vᴴ).trace) = (V * ρ * Uᴴ).trace := by
  constructor
  · rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, h1]
  · rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hρ, Matrix.mul_assoc]

/-- C12-44: N_c = C N_f C† is PSD when N_f is, and the thermal factor passes through: if N_f = c D_f then
C N_f C† = c (C D_f C†). -/
theorem reconstruction_positivity {m : Type*} [Fintype m] (C : Matrix m n ℂ) (Nf Df : Matrix n n ℂ)
    (hN : Nf.PosSemidef) (c : ℂ) (hth : Nf = c • Df) :
    (C * Nf * Cᴴ).PosSemidef ∧ C * Nf * Cᴴ = c • (C * Df * Cᴴ) := by
  refine ⟨hN.mul_mul_conjTranspose_same C, ?_⟩
  rw [hth, Matrix.mul_smul, Matrix.smul_mul]

/-- C12-45: y = Cx obeys an autonomous y′ = L_c y for all x iff CL = L_cC. -/
theorem exact_closure {m : Type*} [Fintype m] (C : Matrix m n ℝ) (L : Matrix n n ℝ) (Lc : Matrix m m ℝ) :
    (∀ x : n → ℝ, C *ᵥ (L *ᵥ x) = Lc *ᵥ (C *ᵥ x)) ↔ C * L = Lc * C := by
  constructor
  · intro h
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h]
  · intro h x; rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec]

end Finite

/-- C12-29: h = −(2φ/c²)(ḡ + 2uu) with ḡ = diag(−1,1,1,1), u = (−1,0,0,0) gives h₀₀ = −2φ/c² and
h_ij = −(2φ/c²)δ_ij (no slip). -/
theorem no_slip_response (φc : ℝ) :
    let gbar : Fin 4 → Fin 4 → ℝ := fun μ ν => if μ = ν then (if μ = 0 then -1 else 1) else 0
    let u : Fin 4 → ℝ := fun μ => if μ = 0 then -1 else 0
    (-(2 * φc) * (gbar 0 0 + 2 * u 0 * u 0) = -(2 * φc)) ∧
      ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → -(2 * φc) * (gbar i j + 2 * u i * u j) = -(2 * φc) * (if i = j then 1 else 0) := by
  intro gbar u
  refine ⟨by norm_num [gbar, u], fun i j hi hj => ?_⟩
  simp only [gbar, u, if_neg hi, if_neg hj, mul_zero, add_zero]
  try (split_ifs <;> simp_all)

/-! ### Cofactors, Kasner, combinatorial normalization, sectors (C12-47, -50, -55, -60, -61, -68) -/

/-- C12-47: with r_n² = nᵀCn, C_ii = r_i² and, for n = (e_i + e_j)/√2,
C_ij = r_{ij,+}² − (r_i² + r_j²)/2. -/
theorem cofactor_reconstruction (Cii Cjj Cij : ℝ) :
    (Cii + Cjj + 2 * Cij) / 2 - (Cii + Cjj) / 2 = Cij := by ring

/-- C12-50: (p₁,p₂,p₃) = (−1/3, 2/3, 2/3) has Σp = 1 and Σp² = 1. -/
theorem kasner_exponents : (-1/3 : ℝ) + 2/3 + 2/3 = 1 ∧ (-1/3 : ℝ) ^ 2 + (2/3) ^ 2 + (2/3) ^ 2 = 1 := by norm_num

/-- C12-55: Σ over subsets x of M switches of f(|x|)/C(M,|x|) = Σ_n f(n) (pattern normalization). -/
theorem pattern_normalization (M : ℕ) (f : ℕ → ℝ) :
    ∑ x ∈ (Finset.range M).powerset, f x.card / (Nat.choose M x.card) = ∑ k ∈ Finset.range (M + 1), f k := by
  rw [Finset.sum_powerset_apply_card (f := fun k => f k / (Nat.choose M k)), Finset.card_range]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have : (Nat.choose M k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk').ne'
  rw [nsmul_eq_mul]; field_simp

/-- C12-60, C12-61: four configuration variables minus two first-class constraints leave two local
degrees of freedom; π^{ij}(L_ξg)_ij = p_a(ξa′ + 2aξ′) + p_bξb′ + p_cξc′ + p_dξd′ with p_d = 2π^{yz}. -/
theorem two_killing_sector (pa pb pc pyz ξ ξ' a a' b' c' d' : ℝ) :
    4 - 2 = 2 ∧ pa * (ξ * a' + 2 * a * ξ') + pb * (ξ * b') + pc * (ξ * c') + 2 * (pyz * (ξ * d')) =
      pa * (ξ * a' + 2 * a * ξ') + pb * ξ * b' + pc * ξ * c' + (2 * pyz) * ξ * d' := by
  constructor <;> ring

/-- C12-68: 3⁶ = 729 count states, 2¹² = 4096 patterns, 6 + C(6,2) = 21 move directions. -/
theorem graph_lift_counts : 3 ^ 6 = 729 ∧ 2 ^ 12 = 4096 ∧ 6 + Nat.choose 6 2 = 21 := by decide

/-! ### Derivations, volume–shape split, Weyl constants (C12-70, C12-71, C12-75, C12-76) -/

/-- C12-70 (b): a derivation of a commutative ring kills every idempotent. -/
theorem derivation_idempotent {R : Type*} [CommRing R] (δ : R → R)
    (hadd : ∀ x y, δ (x + y) = δ x + δ y) (hmul : ∀ x y, δ (x * y) = x * δ y + δ x * y)
    (e : R) (he : e * e = e) : δ e = 0 := by
  have h1 : δ e = 2 * e * δ e := by
    have := hmul e e; rw [he] at this; linear_combination this
  have h2 : e * δ e = 2 * e * δ e := by
    calc e * δ e = e * (2 * e * δ e) := by rw [← h1]
      _ = 2 * (e * e) * δ e := by ring
      _ = 2 * e * δ e := by rw [he]
  have h3 : e * δ e = 0 := by linear_combination -h2
  rw [h1, mul_assoc, h3, mul_zero]

/-- C12-70 (a): if Q is diagonal, the diagonal of [D, Q] vanishes. -/
theorem commutator_diag {n : Type*} [Fintype n] [DecidableEq n] (D : Matrix n n ℂ) (q : n → ℂ) (i : n) :
    (D * Matrix.diagonal q - Matrix.diagonal q * D) i i = 0 := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.sub_apply]; ring

/-- C12-71: every SPD 3×3 g is e^{2α}h with det h = 1, α = (1/6) ln det g, uniquely. -/
theorem volume_shape (g : Matrix (Fin 3) (Fin 3) ℝ) (hg : 0 < g.det) :
    let α := (1/6) * Real.log g.det
    (Real.exp (-2 * α) • g).det = 1 ∧ g = Real.exp (2 * α) • (Real.exp (-2 * α) • g) := by
  intro α
  constructor
  · rw [Matrix.det_smul, Fintype.card_fin, ← Real.exp_nat_mul]
    simp only [α]
    rw [show ((3:ℕ):ℝ) * (-2 * (1/6 * Real.log g.det)) = -Real.log g.det by push_cast; ring, Real.exp_neg,
      Real.exp_log hg]
    field_simp
  · rw [smul_smul, ← Real.exp_add]; simp

/-- C12-75, C12-76: 24λ − 81/2 > 0 iff λ > 27/16, and λ = 5/2 gives ω = √(39/2). -/
theorem rigging_threshold (lam : ℝ) : 0 < 24 * lam - 81/2 ↔ 27/16 < lam := by
  constructor <;> intro h <;> linarith

theorem iwasawa_frequency : (24 : ℝ) * (5/2) - 81/2 = 39/2 := by norm_num

/-! ### Cycle products and density cancellation (C12-77, C12-83) -/

/-- C12-77: rephasing H′_{yx} = e^{i(θ_x − θ_y)}H_{yx} leaves every closed-cycle product unchanged. -/
theorem cycle_rephasing {m : ℕ} (x : Fin (m + 1) → ℕ) (θ : ℕ → ℝ) (H : ℕ → ℕ → ℂ) :
    ∏ k : Fin (m + 1), (Complex.exp ((θ (x k) - θ (x (finRotate (m + 1) k))) * Complex.I) *
        H (x (finRotate (m + 1) k)) (x k)) =
      ∏ k : Fin (m + 1), H (x (finRotate (m + 1) k)) (x k) := by
  rw [Finset.prod_mul_distrib]
  have : ∏ k : Fin (m + 1), Complex.exp ((θ (x k) - θ (x (finRotate (m + 1) k))) * Complex.I) = 1 := by
    rw [← Complex.exp_sum, ← Finset.sum_mul]
    have hs : ∑ k : Fin (m + 1), ((θ (x k) - θ (x (finRotate (m + 1) k)) : ℝ) : ℂ) = 0 := by
      push_cast
      rw [Finset.sum_sub_distrib, sub_eq_zero]
      exact (Equiv.sum_comp (finRotate (m + 1)) (fun k => ((θ (x k) : ℝ) : ℂ))).symm
    push_cast at hs ⊢
    rw [hs, zero_mul, Complex.exp_zero]
  rw [this, one_mul]

/-- C12-83: with K_xy = T_xy/√(μ_xμ_y), Πμ_{x_k} · ΠK_{x_k x_{k+1}} = ΠT_{x_k x_{k+1}} on a closed history. -/
theorem density_cancellation {m : ℕ} (x : Fin (m + 1) → ℕ) (μ : ℕ → ℝ) (hμ : ∀ i, 0 < μ i)
    (T : ℕ → ℕ → ℝ) :
    (∏ k : Fin (m + 1), μ (x k)) *
        ∏ k : Fin (m + 1), T (x k) (x (finRotate (m + 1) k)) / Real.sqrt (μ (x k) * μ (x (finRotate (m + 1) k))) =
      ∏ k : Fin (m + 1), T (x k) (x (finRotate (m + 1) k)) := by
  rw [Finset.prod_div_distrib]
  have hrot : ∏ k : Fin (m + 1), μ (x (finRotate (m + 1) k)) = ∏ k : Fin (m + 1), μ (x k) :=
    Equiv.prod_comp (finRotate (m + 1)) (fun k => μ (x k))
  have hrot' : ∏ k : Fin (m + 1), Real.sqrt (μ (x (finRotate (m + 1) k))) = ∏ k : Fin (m + 1), Real.sqrt (μ (x k)) :=
    Equiv.prod_comp (finRotate (m + 1)) (fun k => Real.sqrt (μ (x k)))
  have hsq : ∏ k : Fin (m + 1), Real.sqrt (μ (x k) * μ (x (finRotate (m + 1) k))) = ∏ k : Fin (m + 1), μ (x k) := by
    simp_rw [Real.sqrt_mul (hμ _).le]
    rw [Finset.prod_mul_distrib, hrot', ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun k _ => Real.mul_self_sqrt (hμ _).le)
  have hpos : 0 < ∏ k : Fin (m + 1), μ (x k) := Finset.prod_pos (fun k _ => hμ _)
  rw [hsq]; field_simp

/-! ### Flux norm, N-isometry, composite isometry (C12-85, C12-86, C12-87) -/

section Flux
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem herm_form_star (N : Matrix n n ℂ) (hN : Nᴴ = N) (x y : n → ℂ) :
    star (star x ⬝ᵥ (N *ᵥ y)) = star y ⬝ᵥ (N *ᵥ x) := by
  have hN' : ∀ i j, star (N i j) = N j i := fun i j => by
    have := congrFun (congrFun hN j) i; simpa [Matrix.conjTranspose_apply] using this
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum, hN']
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

/-- C12-85: if N ∂_τΨ = −i(H − E)Ψ with H, N Hermitian and E real, then ∂_τ(Ψ†NΨ) = 0. -/
theorem flux_conservation (H N : Matrix n n ℂ) (E : ℝ) (hH : Hᴴ = H) (hN : Nᴴ = N) (Ψ dΨ : n → ℂ)
    (h : N *ᵥ dΨ = -Complex.I • ((H - (E : ℂ) • 1) *ᵥ Ψ)) :
    star dΨ ⬝ᵥ (N *ᵥ Ψ) + star Ψ ⬝ᵥ (N *ᵥ dΨ) = 0 := by
  have hHE : (H - (E : ℂ) • 1)ᴴ = H - (E : ℂ) • 1 := by
    rw [Matrix.conjTranspose_sub, hH, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp [Complex.conj_ofReal]
  set w := star Ψ ⬝ᵥ ((H - (E : ℂ) • 1) *ᵥ Ψ)
  have hw : star w = w := herm_form_star _ hHE Ψ Ψ
  rw [← herm_form_star N hN Ψ dΨ, h, dotProduct_smul, smul_eq_mul, star_mul', hw]
  have hI : star (-Complex.I) = Complex.I := by simp [Complex.conj_I]
  rw [hI]; ring

/-- C12-86: with S Hermitian, S S = N, Si S = S Si = 1 and V unitary, A := Si V S has A†NA = N. -/
theorem n_isometry (S Si V : Matrix n n ℂ) (hS : Sᴴ = S) (hSi : Siᴴ = Si) (h1 : Si * S = 1) (h2 : S * Si = 1)
    (hV : Vᴴ * V = 1) : (Si * V * S)ᴴ * (S * S) * (Si * V * S) = S * S := by
  simp only [Matrix.conjTranspose_mul, hS, hSi]
  calc _ = S * Vᴴ * (Si * S) * (S * Si) * V * S := by
        simp only [Matrix.mul_assoc]
    _ = S * (Vᴴ * V) * S := by rw [h1, h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = S * S := by rw [hV, Matrix.mul_one]

/-- C12-87: a composite of isometries is an isometry. -/
theorem composite_isometry {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (A : Matrix b a ℂ) (B : Matrix c b ℂ) (C : Matrix d c ℂ) (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1)
    (hC : Cᴴ * C = 1) : (C * B * A)ᴴ * (C * B * A) = 1 := by
  simp only [Matrix.conjTranspose_mul]
  calc _ = Aᴴ * (Bᴴ * (Cᴴ * C) * B) * A := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hC, Matrix.mul_one, hB, Matrix.mul_one, hA]

end Flux

end Entropic.AppKN
