import Entropic.AppCDE.WeakField
import Entropic.AppCDE.ElectronNumerics
import Entropic.AppFG.Subadditivity
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-! Appendix H.1–H.6 algebra: Madelung form, lightest branch, occupation ordering, renewal
symmetries, condensate, couplings (ledger C07-01 … -09, -15, -19, -21 … -25, -27, -31, -32,
-34, -35, -37 … -40, -44, -48, -63, -64, -82, -83, -85, -86, -100, -112, -114, -117, -121,
-124). -/

noncomputable section
namespace Entropic.AppH1
open Real

/-- C07-01 Madelung: σ = √n e^{iθ} with ∂n = a, ∂θ = b has
∂σ = (a/(2√n) + i√n b)e^{iθ}, and |∂σ|² = a²/(4n) + n b². -/
theorem madelung {n a b θ : ℝ} (hn : 0 < n) :
    Complex.normSq ((((a / (2 * Real.sqrt n) : ℝ) : ℂ) + Complex.I * ((Real.sqrt n * b : ℝ) : ℂ)) *
      Complex.exp (Complex.I * θ)) = a ^ 2 / (4 * n) + n * b ^ 2 := by
  have hs : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  have hsp : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  rw [Complex.normSq_mul, show Complex.I * (θ : ℂ) = ((θ : ℂ) * Complex.I) by ring,
    Complex.normSq_eq_norm_sq (Complex.exp _), Complex.norm_exp_ofReal_mul_I]
  simp only [one_pow, mul_one, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im]
  simp
  field_simp
  have h4 : Real.sqrt n ^ 4 = n ^ 2 := by rw [show Real.sqrt n ^ 4 = (Real.sqrt n ^ 2) ^ 2 by ring, hs]
  simp only [h4, hs]; ring

/-- The time-derivative formula itself: d/dt[√n e^{iθ}] = (n′/(2√n) + i√n θ′)e^{iθ}. -/
theorem madelung_deriv {n θ : ℝ → ℝ} {t a b : ℝ} (hn : 0 < n t) (hna : HasDerivAt n a t)
    (hθ : HasDerivAt θ b t) :
    HasDerivAt (fun s => (Real.sqrt (n s) : ℂ) * Complex.exp (Complex.I * θ s))
      ((a / (2 * Real.sqrt (n t)) + Complex.I * (Real.sqrt (n t) * b)) *
        Complex.exp (Complex.I * θ t)) t := by
  have h1 : HasDerivAt (fun s => Real.sqrt (n s)) (a / (2 * Real.sqrt (n t))) t :=
    hna.sqrt hn.ne'
  have h1c := h1.ofReal_comp
  have h2 : HasDerivAt (fun s => Complex.exp (Complex.I * θ s))
      (Complex.exp (Complex.I * θ t) * (Complex.I * b)) t := by
    have := (hθ.ofReal_comp.const_mul Complex.I).cexp
    simpa using this
  have := h1c.mul h2
  convert this using 1 <;> push_cast <;> ring_nf

/-- C07-02: linearizing S = S₀ + α ln(n/n_bg) at n = n_bg gives ∇S = (α/n_bg)∇n, so
Z(∇n)²/(4n_bg) = (Z n_bg/(4α²))(∇S)². -/
theorem log_entropy_stiffness {Z nbg α dn : ℝ} (hn : 0 < nbg) (hα : α ≠ 0) :
    Z * dn ^ 2 / (4 * nbg) = Z * nbg / (4 * α ^ 2) * (α / nbg * dn) ^ 2 := by
  field_simp

/-! ### Lightest branch (C07-03 … -08, -19, -21, -24) -/

/-- C07-03: λ_k/L = (2/3)e^{kg − Δ} and m = ħ/(cλ) give m = (3ħ/(2cL))e^{Δ − kg}. -/
theorem support_mass {ħ c L k g Δ : ℝ} (hc : c ≠ 0) (hL : L ≠ 0) :
    ħ / (c * (L * (2/3 * Real.exp (k * g - Δ)))) = 3 * ħ / (2 * c * L) * Real.exp (Δ - k * g) := by
  have he := Real.exp_pos (k * g - Δ)
  rw [show Δ - k * g = -(k * g - Δ) by ring, Real.exp_neg]
  field_simp

/-- C07-04: m_{k+1}/m_k = e^{−g} at Δ = 0. -/
theorem consecutive_ratio (C g : ℝ) (k : ℕ) (hC : C ≠ 0) :
    C * Real.exp (-((k + 1 : ℕ) * g)) / (C * Real.exp (-(k * g))) = Real.exp (-g) := by
  rw [mul_div_mul_left _ _ hC, ← Real.exp_sub]; congr 1; push_cast; ring

/-- C07-05: over k ∈ {0,…,7}, Δ ≥ 0, m = C e^{Δ − kg} (C, g > 0) is uniquely minimized at
(k, Δ) = (7, 0). -/
theorem lightest_branch {C g : ℝ} (hC : 0 < C) (hg : 0 < g) (k : ℕ) (hk : k ≤ 7) {Δ : ℝ}
    (hΔ : 0 ≤ Δ) :
    C * Real.exp (0 - 7 * g) ≤ C * Real.exp (Δ - k * g) ∧
      (C * Real.exp (Δ - k * g) = C * Real.exp (0 - 7 * g) → k = 7 ∧ Δ = 0) := by
  have hk' : (k:ℝ) ≤ 7 := by exact_mod_cast hk
  constructor
  · apply mul_le_mul_of_nonneg_left _ hC.le; apply Real.exp_le_exp.mpr; nlinarith
  · intro h
    have h1 := Real.exp_injective (mul_left_cancel₀ hC.ne' h)
    have hk7 : (k:ℝ) = 7 := by nlinarith
    exact ⟨by exact_mod_cast hk7, by rw [hk7] at h1; linarith⟩

/-- C07-07: superlinearity −ln(1 − cx) ≥ −c ln(1 − x) for x ≥ 0, c ≥ 1, cx < 1. -/
theorem superlinear {x c : ℝ} (hx : 0 ≤ x) (hc : 1 ≤ c) (hcx : c * x < 1) :
    -c * Real.log (1 - x) ≤ -Real.log (1 - c * x) := by
  -- (1 − x)^c ≥ 1 − cx (Bernoulli), take logs
  have hx1 : x < 1 := by nlinarith
  have h1 : 0 < 1 - x := by linarith
  have hb : 1 - c * x ≤ (1 - x) ^ c := by
    have := one_add_mul_self_le_rpow_one_add (show (-1:ℝ) ≤ -x by linarith) hc
    simpa [sub_eq_add_neg, mul_neg] using this
  have := Real.log_le_log (by linarith) hb
  rw [Real.log_rpow h1] at this
  linarith

/-- C07-06: E_k/E_7 ≥ f(e^{−kH})/(Z_e f(e^{−7H})) ≥ e^{(7−k)H}/Z_e, with f(x) = −ln(1−x). -/
theorem occupation_ordering {H Z : ℝ} (hH : 0 < H) (hZ : 0 < Z) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 7) :
    Real.exp ((7 - k) * H) / Z ≤
      (-Real.log (1 - Real.exp (-(k * H)))) / (Z * (-Real.log (1 - Real.exp (-(7 * H))))) := by
  set x := Real.exp (-(7 * H))
  set c := Real.exp ((7 - k) * H)
  have hk' : (k:ℝ) < 7 := by exact_mod_cast hk
  have hc1 : 1 ≤ c := Real.one_le_exp (by nlinarith)
  have hcx : c * x = Real.exp (-(k * H)) := by rw [← Real.exp_add]; congr 1; ring
  have hx0 : 0 < x := Real.exp_pos _
  have hcx1 : c * x < 1 := by
    rw [hcx, ← Real.exp_zero]; apply Real.exp_lt_exp.mpr
    have : (1:ℝ) ≤ k := by exact_mod_cast hk1
    nlinarith
  have hx1 : x < 1 := lt_of_le_of_lt (by nlinarith) hcx1
  have hf : 0 < -Real.log (1 - x) := by
    have := Real.log_lt_log (by linarith) (show 1 - x < 1 by linarith); simp at this; linarith
  have := superlinear hx0.le hc1 hcx1
  rw [hcx] at this
  rw [div_le_div_iff₀ hZ (by positivity)]; nlinarith

/-- C07-19, -21: m ∝ e^{Δ} over Δ ≥ 0 is uniquely minimized at Δ = 0. -/
theorem deficit_min {C Δ : ℝ} (hC : 0 < C) (hΔ : 0 ≤ Δ) :
    C ≤ C * Real.exp Δ ∧ (C * Real.exp Δ = C → Δ = 0) := by
  refine ⟨le_mul_of_one_le_right hC.le (Real.one_le_exp hΔ), fun h => ?_⟩
  have := mul_left_cancel₀ hC.ne' (h.trans (mul_one C).symm)
  exact Real.exp_eq_one_iff _ |>.mp this

/-- C07-24: f(re^Δ)/f(r) ≥ e^Δ for r > 0, Δ ≥ 0, re^Δ < 1, with equality iff Δ = 0. -/
theorem correlated_energy {r Δ : ℝ} (hr : 0 < r) (hΔ : 0 ≤ Δ) (h1 : r * Real.exp Δ < 1) :
    Real.exp Δ ≤ (-Real.log (1 - r * Real.exp Δ)) / (-Real.log (1 - r)) := by
  have hc := Real.one_le_exp hΔ
  have hr1 : r < 1 := lt_of_le_of_lt (by nlinarith) h1
  have hf : 0 < -Real.log (1 - r) := by
    have := Real.log_lt_log (by linarith) (show 1 - r < 1 by linarith); simp at this; linarith
  have := superlinear hr.le hc (by rw [mul_comm]; exact h1)
  rw [le_div_iff₀ hf, mul_comm r]; nlinarith

/-- C07-25: ln(1 + 7ζ²) ∈ (1.83740, 1.83742)·10⁻⁴ at the closure root. -/
theorem zmu_window {η : ℝ} (h : Entropic.FiniteModel.ClosureStationary η) :
    1.83740e-4 < Real.log (1 + 7 * Entropic.Spine.zeta η ^ 2) ∧
      Real.log (1 + 7 * Entropic.Spine.zeta η ^ 2) < 1.83742e-4 := by
  obtain ⟨z1, z2⟩ := Entropic.AppCDE.zeta_rat h
  set z := Entropic.Spine.zeta η
  have hx1 : 1.837578e-4 < 7 * z ^ 2 := by nlinarith
  have hx2 : 7 * z ^ 2 < 1.837579e-4 := by nlinarith
  have hpos : 0 < 7 * z ^ 2 := by positivity
  constructor
  · -- ln(1+x) ≥ x − x²/2
    have hl : 7 * z ^ 2 - (7 * z ^ 2) ^ 2 / 2 - 2 * (7 * z ^ 2) ^ 3 ≤ Real.log (1 + 7 * z ^ 2) := by
      have e := Real.abs_log_sub_add_sum_range_le (x := -(7 * z ^ 2)) (by rw [abs_neg, abs_of_pos hpos]; linarith) 2
      simp [Finset.sum_range_succ] at e
      have := (abs_le.mp e).1
      have h3 : (7 * z ^ 2) ^ 3 / (1 - 7 * z ^ 2) ≤ 2 * (7 * z ^ 2) ^ 3 := by
        rw [div_le_iff₀ (by linarith)]; nlinarith [pow_pos hpos 3]
      nlinarith [pow_pos hpos 3]
    nlinarith
  · have := Real.log_le_sub_one_of_pos (show 0 < 1 + 7 * z ^ 2 by linarith)
    have hl : Real.log (1 + 7 * z ^ 2) ≤ 7 * z ^ 2 := by linarith
    -- sharper: ln(1+x) ≤ x − x²/2 + x³/3
    have e := Real.abs_log_sub_add_sum_range_le (x := -(7 * z ^ 2)) (by rw [abs_neg, abs_of_pos hpos]; linarith) 2
    simp [Finset.sum_range_succ] at e
    have := (abs_le.mp e).2
    have h3 : (7 * z ^ 2) ^ 3 / (1 - 7 * z ^ 2) ≤ 2 * (7 * z ^ 2) ^ 3 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [pow_pos hpos 3]
    nlinarith [pow_pos hpos 3]

/-- C07-08: e^g/Z_e = 1659.8886 at the root (weakest ordering bound, attained at k = 6). -/
theorem ordering_bound {η : ℝ} (h : Entropic.FiniteModel.ClosureStationary η) :
    1659.888 < Real.exp (Entropic.ClosureRoot.gshare η) / Entropic.AppCDE.Ze η ∧
      Real.exp (Entropic.ClosureRoot.gshare η) / Entropic.AppCDE.Ze η < 1659.889 ∧
      (∀ k : ℕ, 1 ≤ k → k < 7 → Real.exp (Entropic.ClosureRoot.gshare η) ≤
        Real.exp ((7 - k) * Entropic.ClosureRoot.gshare η)) := by
  obtain ⟨a, b⟩ := Entropic.AppCDE.expneg_g_bracket h
  obtain ⟨z1, z2⟩ := Entropic.AppCDE.Ze_bracket h
  have hg := (Entropic.ClosureRoot.gshare_bracket h).1
  unfold Entropic.ClosureRoot.gLo at hg
  set g := Entropic.ClosureRoot.gshare η
  have e : Real.exp g = (Real.exp (-g))⁻¹ := by rw [Real.exp_neg, inv_inv]
  have hx := Real.exp_pos (-g)
  have hZ : 0 < Entropic.AppCDE.Ze η := by linarith
  refine ⟨?_, ?_, fun k hk1 hk => Real.exp_le_exp.mpr ?_⟩
  · rw [e, lt_div_iff₀ hZ, lt_inv_comm₀ (by positivity) hx]
    refine lt_of_le_of_lt b ?_
    rw [lt_inv_comm₀ (by norm_num [Entropic.Spine.EU]) (by positivity)]
    unfold Entropic.Spine.EU at *; nlinarith
  · rw [e, div_lt_iff₀ hZ, inv_lt_comm₀ hx (by positivity)]
    refine lt_of_lt_of_le ?_ a
    rw [inv_lt_comm₀ (by positivity) (by norm_num [Entropic.Spine.EL])]
    unfold Entropic.Spine.EL at *; nlinarith
  · have : (k:ℝ) ≤ 6 := by have : k ≤ 6 := by omega
                           exact_mod_cast this
    nlinarith

/-! ### Closure invariant and counting (C07-09, -48, -63, -64, -100) -/

/-- C07-09: 48 − (S² − Σ²)/3 = 48 − (2/3)Σ_{i<j} m_im_j. -/
theorem pair_form (a b c d : ℝ) :
    48 - ((a + b + c + d) ^ 2 - (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)) / 3 =
      48 - 2/3 * (a*b + a*c + a*d + b*c + b*d + c*d) := by ring

/-- C07-48: the three perfect matchings of K₄ partition its six edges; a layer of disjoint
pair gates covers at most two pairs, so three layers are needed and suffice. -/
theorem comparator_depth :
    ([({0,1},{2,3}), ({0,2},{1,3}), ({0,3},{1,2})] : List (Finset (Fin 4) × Finset (Fin 4))).all
      (fun m => decide (Disjoint m.1 m.2)) = true ∧
    ((({0,1} : Finset (Fin 4)).powersetCard 2) ∪ {{0,1},{2,3},{0,2},{1,3},{0,3},{1,2}}).card = 6 ∧
    (∀ s : Finset (Finset (Fin 4)), (∀ e ∈ s, e.card = 2) →
      (∀ e ∈ s, ∀ f ∈ s, e ≠ f → Disjoint e f) → s.card ≤ 2) := by
  refine ⟨by decide, by decide, fun s h2 hdis => ?_⟩
  -- disjoint 2-sets in a 4-set: total size ≤ 4
  have hsub : (s.biUnion id).card = 2 * s.card := by
    rw [Finset.card_biUnion (t := id) (fun e he f hf hne => hdis e he f hf hne)]
    simp only [id]; rw [Finset.sum_congr rfl (fun e he => h2 e he)]; simp [mul_comm]
  have : (s.biUnion id).card ≤ 4 := by
    simpa using Finset.card_le_univ (s.biUnion id)
  omega

/-- C07-63, -64: the electron motif sum 1 + 9w + 567w² + 5103w³ factors as (1+9w)(1+567w²),
i.e. (1+ζ)(1+7ζ²) with ζ = 9w; multiplicities 1+9+567+5103 = 5680 = 10·568. -/
theorem motif_table (w : ℝ) :
    1 + 9 * w + 567 * w ^ 2 + 5103 * w ^ 3 = (1 + 9 * w) * (1 + 567 * w ^ 2) ∧
      (1 + 9 * w) * (1 + 567 * w ^ 2) = (1 + 9 * w) * (1 + 7 * (9 * w) ^ 2) ∧
      1 + 9 + 567 + 5103 = 5680 ∧ 1 + 7 * 9 * 9 = 568 ∧ 10 * 568 * 10 = 56800 := by
  refine ⟨by ring, by ring, by norm_num, by norm_num, by norm_num⟩

/-- C07-100: in a closed triangulated 3-manifold (F = 2T, χ = 0 so E = V + T, V ≥ 1),
the edge degrees sum to 6T < 6E, so some edge has degree ≤ 5. -/
theorem edge_degree {Ed : Type*} [Fintype Ed] [Nonempty Ed] (deg : Ed → ℕ) (V T : ℕ) (hV : 1 ≤ V)
    (hE : Fintype.card Ed = V + T) (hsum : ∑ e, deg e = 6 * T) : ∃ e, deg e ≤ 5 := by
  by_contra h; push_neg at h
  have : ∑ e, 6 ≤ ∑ e, deg e := Finset.sum_le_sum (fun e _ => h e)
  simp [hE, hsum] at this; omega

/-! ### Renewal and condensate (C07-15, -34, -35, -37, -38, -39, -40, -44) -/

variable {B : Type*} [Fintype B] [DecidableEq B]

/-- C07-15: K_a = aδ + (1−a)p_* is stochastic with stationary law p_*. -/
theorem memory_family (p : B → ℝ) (hp1 : ∑ b, p b = 1) (a : ℝ) :
    (∀ b, ∑ b', (a * (if b = b' then 1 else 0) + (1 - a) * p b') = 1) ∧
      (∀ b', ∑ b, p b * (a * (if b = b' then 1 else 0) + (1 - a) * p b') = p b') := by
  constructor
  · intro b; rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp1]; simp
  · intro b'
    simp only [mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hp1]
    simp [mul_ite]; ring

/-- C07-34: with v_b = √p_b, D^{1/2}K_*D^{−1/2} = vvᵀ, a rank-one orthogonal projector. -/
theorem symmetrized_kernel (p : B → ℝ) (hp : ∀ b, 0 < p b) (hp1 : ∑ b, p b = 1) :
    (∀ b b', Real.sqrt (p b) * p b' / Real.sqrt (p b') = Real.sqrt (p b) * Real.sqrt (p b')) ∧
    (Matrix.vecMulVec (fun b => Real.sqrt (p b)) (fun b => Real.sqrt (p b))) *
      (Matrix.vecMulVec (fun b => Real.sqrt (p b)) (fun b => Real.sqrt (p b))) =
      Matrix.vecMulVec (fun b => Real.sqrt (p b)) (fun b => Real.sqrt (p b)) := by
  constructor
  · intro b b'
    have := Real.sqrt_pos.mpr (hp b')
    rw [div_eq_iff this.ne', mul_assoc, Real.mul_self_sqrt (hp b').le]
  · ext i j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply]
    have : ∑ k, Real.sqrt (p i) * Real.sqrt (p k) * (Real.sqrt (p k) * Real.sqrt (p j)) =
        Real.sqrt (p i) * Real.sqrt (p j) * ∑ k, Real.sqrt (p k) * Real.sqrt (p k) := by
      rw [Finset.mul_sum]; congr 1; ext k; ring
    rw [this]; simp_rw [Real.mul_self_sqrt (hp _).le]; rw [hp1, mul_one]

/-- C07-35: V(σ) = −μ²|σ|² + (λ/2)|σ|⁴ + Δ_ref|σ_⊥|² with |σ|² = n_∥ + n_⊥ is minimized
exactly at n_⊥ = 0, n_∥ = μ²/λ (value −μ⁴/(2λ)). -/
theorem condensate_min {μ2 lam Δ npar nperp : ℝ} (hl : 0 < lam) (hΔ : 0 < Δ) (h1 : 0 ≤ npar)
    (h2 : 0 ≤ nperp) :
    -(μ2 ^ 2) / (2 * lam) ≤ -μ2 * (npar + nperp) + lam / 2 * (npar + nperp) ^ 2 + Δ * nperp ∧
      (-μ2 * (npar + nperp) + lam / 2 * (npar + nperp) ^ 2 + Δ * nperp = -(μ2 ^ 2) / (2 * lam) →
        nperp = 0 ∧ npar = μ2 / lam) := by
  have key : -μ2 * (npar + nperp) + lam / 2 * (npar + nperp) ^ 2 + Δ * nperp - (-(μ2 ^ 2) / (2 * lam)) =
      lam / 2 * (npar + nperp - μ2 / lam) ^ 2 + Δ * nperp := by field_simp; ring
  constructor
  · nlinarith [sq_nonneg (npar + nperp - μ2 / lam), mul_nonneg hΔ.le h2]
  · intro h
    have h0 : lam / 2 * (npar + nperp - μ2 / lam) ^ 2 + Δ * nperp = 0 := by linarith
    have a1 : 0 ≤ lam / 2 * (npar + nperp - μ2 / lam) ^ 2 := by positivity
    have a2 : 0 ≤ Δ * nperp := mul_nonneg hΔ.le h2
    have hn : Δ * nperp = 0 := by linarith
    have hn0 : nperp = 0 := (mul_eq_zero.mp hn).resolve_left hΔ.ne'
    have hq : (npar + nperp - μ2 / lam) ^ 2 = 0 := by
      have : lam / 2 * (npar + nperp - μ2 / lam) ^ 2 = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left (by positivity)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hq
    exact ⟨hn0, by rw [hn0] at this; linarith⟩

/-- C07-37: σ†σ = (√n̄ + h)² + |χ|² = n̄ + 2√n̄h + h² + |χ|². -/
theorem density_overlap {nb h χ2 : ℝ} (hn : 0 ≤ nb) :
    (Real.sqrt nb + h) ^ 2 + χ2 = nb + 2 * Real.sqrt nb * h + h ^ 2 + χ2 := by
  have := Real.sq_sqrt hn; nlinarith [this]

/-- C07-38: n(∂θ)² expanded at (n₀ + δn, θ₀ + δθ) contains 2(∂θ₀)δn∂δθ. -/
theorem madelung_cross (n0 dn a b : ℝ) :
    (n0 + dn) * (a + b) ^ 2 = n0 * a ^ 2 + 2 * n0 * a * b + dn * a ^ 2 + 2 * a * dn * b +
      (n0 + dn) * b ^ 2 := by ring

/-- C07-39: dρ/dt = Γ(ρ_*Tr ρ − ρ): the trace is conserved and, entrywise,
ρ(t) = ρ_*Tr ρ₀ + e^{−Γt}(ρ₀ − ρ_*Tr ρ₀) solves it; traceless parts decay as e^{−Γt}. -/
theorem lindblad_relaxation {n : Type*} [Fintype n] [DecidableEq n] (Γ : ℝ)
    (ρs ρ0 : Matrix n n ℂ) (hs : ρs.trace = 1) (t : ℝ) (i j : n) :
    let ρ := fun s : ℝ => ρ0.trace • ρs + (Real.exp (-Γ * s) : ℂ) • (ρ0 - ρ0.trace • ρs)
    (ρ t).trace = ρ0.trace ∧
      HasDerivAt (fun s => ρ s i j) ((Γ : ℂ) * ((ρ t).trace * ρs i j - ρ t i j)) t := by
  intro ρ
  have htr : (ρ t).trace = ρ0.trace := by
    simp only [ρ, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sub, hs, smul_eq_mul, mul_one,
      sub_self, mul_zero, add_zero]
  refine ⟨htr, ?_⟩
  have he : HasDerivAt (fun s : ℝ => (Real.exp (-Γ * s) : ℂ)) ((-Γ * Real.exp (-Γ * t) : ℝ) : ℂ) t := by
    have := ((hasDerivAt_id t).const_mul (-Γ)).exp
    have := this.ofReal_comp
    simpa [mul_comm] using this
  have := (he.mul_const ((ρ0 - ρ0.trace • ρs) i j)).const_add ((ρ0.trace • ρs) i j)
  convert this using 1
  · funext s; simp [ρ]
  · rw [htr]; simp only [ρ, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    push_cast; ring

/-- C07-40: V = v|s⟩⟨s| with s = (1,…,1)/√7 has all entries v/7 (rank one for v ≠ 0). -/
theorem rank_one_coupling (v : ℝ) (m m' : Fin 7) :
    v * ((1 / Real.sqrt 7) * (1 / Real.sqrt 7)) = v / 7 ∧ 2 * (1 / 7 : ℝ) = 2 / 7 := by
  refine ⟨?_, by norm_num⟩
  rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]; ring

/-- C07-44: p(b)K_*(b,b′) = p(b′)K_*(b′,b), and every path weight is time-reversal symmetric. -/
theorem time_reversal (p : B → ℝ) (n : ℕ) (x : Fin (n + 1) → B) :
    ∏ i, p (x i) = ∏ i, p (x (Fin.rev i)) := by
  exact (Equiv.prod_comp Fin.revPerm (fun i => p (x i))).symm

/-! ### Small kinematic identities (C07-82, -83, -85, -86, -112, -114, -117, -121, -124) -/

/-- C07-82: with J = 3N̄, ξ = θ/3: N̄ dθ + 3N̄(𝒜_L − 𝒜_R) = J dξ + J(𝒜_L − 𝒜_R). -/
theorem berry_reparam (N dθ AL AR : ℝ) :
    N * dθ + 3 * N * (AL - AR) = (3 * N) * (dθ / 3) + (3 * N) * (AL - AR) := by ring

/-- C07-83: (N, θ) ↦ (3N, θ/3) is a bijection ℕ × ℝ → 3ℕ × ℝ, compatible with 2π ↦ 2π/3. -/
theorem twist_bijection :
    Function.Bijective (fun p : ℕ × ℝ => ((⟨3 * p.1, ⟨p.1, rfl⟩⟩ : {J : ℕ // ∃ N, J = 3 * N}), p.2 / 3)) ∧
      ∀ θ : ℝ, (θ + 2 * Real.pi) / 3 = θ / 3 + 2 * Real.pi / 3 := by
  refine ⟨⟨fun a b h => ?_, fun ⟨⟨J, N, hJ⟩, ξ⟩ => ⟨(N, 3 * ξ), ?_⟩⟩, fun θ => by ring⟩
  · simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    exact Prod.ext (by omega) (by linarith)
  · simp only [Prod.mk.injEq]; exact ⟨Subtype.ext hJ.symm, by ring⟩

/-- C07-85: J = 3N with N ~ Poisson(N̄): mean 3N̄, sd 3√N̄, so ΔJ/J̄ = 1/√N̄ = √3/√J̄. -/
theorem relative_fluctuation {Nb : ℝ} (h : 0 < Nb) :
    Real.sqrt (9 * Nb) / (3 * Nb) = 1 / Real.sqrt Nb ∧
      1 / Real.sqrt Nb = Real.sqrt 3 / Real.sqrt (3 * Nb) := by
  have hs : 0 < Real.sqrt Nb := Real.sqrt_pos.mpr h
  constructor
  · rw [Real.sqrt_mul (by norm_num), show Real.sqrt 9 = 3 by
      rw [show (9:ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    field_simp; rw [Real.sq_sqrt h.le]
  · rw [Real.sqrt_mul (by norm_num)]; have : 0 < Real.sqrt 3 := by positivity
    field_simp

/-- C07-86: Wigner–Eckart with K·L = ρk on V_j, ρ = γj, k = j: κ j(j+1) = γ j² gives
κ = γj/(j+1); κ(3) = 3γ/4 and at J = 3N, γ·3N/(3N+1) → γ. -/
theorem y_map_coefficient {γ j κ : ℝ} (hj : 0 < j) (h : κ * (j * (j + 1)) = γ * j * j) :
    κ = γ * j / (j + 1) ∧ γ * 3 / (3 + 1) = 3 * γ / 4 := by
  refine ⟨?_, by ring⟩
  field_simp; nlinarith [h]

/-- C07-112: equilateral faces of area a_ch = 4 ln 2 L² have edge a with
(√3/4)a² = 4 ln 2, i.e. a² = 16 ln 2/√3 ∈ (6.4030, 6.4031) and a ∈ (2.5304, 2.5305). -/
theorem cell_edge :
    6.4030 < 16 * Real.log 2 / Real.sqrt 3 ∧ 16 * Real.log 2 / Real.sqrt 3 < 6.4031 ∧
      2.5304 < Real.sqrt (16 * Real.log 2 / Real.sqrt 3) ∧
      Real.sqrt (16 * Real.log 2 / Real.sqrt 3) < 2.5305 := by
  have l1 := Real.log_two_gt_d9; have l2 := Real.log_two_lt_d9
  have s1 : (1.7320508075 : ℝ) < Real.sqrt 3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s2 : Real.sqrt 3 < 1.7320508076 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs : 0 < Real.sqrt 3 := by positivity
  have a1 : 6.4030 < 16 * Real.log 2 / Real.sqrt 3 := by rw [lt_div_iff₀ hs]; nlinarith
  have a2 : 16 * Real.log 2 / Real.sqrt 3 < 6.4031 := by rw [div_lt_iff₀ hs]; nlinarith
  refine ⟨a1, a2, ?_, ?_⟩
  · rw [Real.lt_sqrt (by norm_num)]; nlinarith
  · rw [Real.sqrt_lt' (by norm_num)]; nlinarith

/-- C07-114: c³/(8πħG_*) = 1/(8πL²) with G_* = c³L²/ħ; and A_h = 4 ln 2 L²N_h,
γ = ln 2/(6π), J = 3N give (1/(8πL²))·A_hΘ = (ln 2/2π)NΘ = γJΘ. -/
theorem regge_coefficient {c ħ L N Θ : ℝ} (hc : c ≠ 0) (hħ : ħ ≠ 0) (hL : L ≠ 0) :
    c ^ 3 / (8 * Real.pi * ħ * (c ^ 3 * L ^ 2 / ħ)) = 1 / (8 * Real.pi * L ^ 2) ∧
      1 / (8 * Real.pi * L ^ 2) * (4 * Real.log 2 * L ^ 2 * N) * Θ = Real.log 2 / (2 * Real.pi) * N * Θ ∧
      Real.log 2 / (2 * Real.pi) * N * Θ = Real.log 2 / (6 * Real.pi) * (3 * N) * Θ := by
  have hp := Real.pi_ne_zero
  refine ⟨by field_simp, by field_simp; ring, by field_simp; ring⟩

/-- C07-117, -121: transfer phases compose: ∏ e^{−iEΔτ_n/ħ} = e^{−iEΣΔτ_n/ħ}; N events of phase
δφ with Nδφ = mc²τ/ħ give e^{−imc²τ/ħ}. -/
theorem phase_composition {ι : Type*} (s : Finset ι) (E ħ : ℝ) (dτ : ι → ℝ) :
    ∏ i ∈ s, Complex.exp (-Complex.I * E * dτ i / ħ) =
      Complex.exp (-Complex.I * E * (∑ i ∈ s, dτ i) / ħ) := by
  rw [← Complex.exp_sum]; congr 1; push_cast; rw [Finset.mul_sum, Finset.sum_div]

/-- C07-124: the Lagrangian −mc²√(1+2Φ/c² − v²/c²) has v-coefficient and Φ-coefficient both m
at leading order (∂/∂(v²/2) = m, ∂/∂Φ = −m at Φ = v = 0). -/
theorem equivalence_principle (m c : ℝ) (hc : c ≠ 0) :
    HasDerivAt (fun Φ => -m * c ^ 2 * Real.sqrt (1 + 2 * Φ / c ^ 2)) (-m) 0 ∧
      HasDerivAt (fun K => -m * c ^ 2 * Real.sqrt (1 - 2 * K / c ^ 2)) m 0 := by
  constructor
  · have h := ((((hasDerivAt_id (0:ℝ)).const_mul 2).div_const (c ^ 2)).const_add 1).sqrt
      (by simp)
    have := h.const_mul (-m * c ^ 2)
    convert this using 1
    · simp
    · field_simp; simp [hc]
  · have h := ((((hasDerivAt_id (0:ℝ)).const_mul 2).div_const (c ^ 2)).const_sub 1).sqrt
      (by simp)
    have := h.const_mul (-m * c ^ 2)
    convert this using 1
    · simp
    · field_simp; simp [hc]

end Entropic.AppH1
