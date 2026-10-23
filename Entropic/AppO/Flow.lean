import Entropic.AppO.Release
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Tactic

/-! Appendix O, flow and information items: positivity of both release components (C13-15), the
reallocated fraction stays in [0,1] (C13-16), the contact-target ratio formula (C13-22), the
integrated stock balance (C13-39), local capacity algebra and density-floor bound (C13-40, C13-41),
no-flux diffusion conservation (C13-51, C13-52), the finite spatial-average estimator (C13-06),
mixing fraction (C13-69), absorbing first entry (C13-76), resolved-kernel monotonicity (C13-78),
hazard cancellation (C13-89) and the formation isometry (C13-95). -/

noncomputable section
namespace Entropic.AppO
open Real Matrix

/-- Integrating-factor positivity with a continuous rate (the primitive is constructed). -/
theorem linear_positivity' (f k s : ℝ → ℝ) (t0 : ℝ) (hk : Continuous k)
    (hf : ∀ t, HasDerivAt f (-k t * f t + s t) t) (hs : ∀ t, t0 ≤ t → 0 ≤ s t) (h0 : 0 ≤ f t0) :
    ∀ t, t0 ≤ t → 0 ≤ f t :=
  linear_positivity f (fun u => ∫ x in t0..u, k x) k s t0 hf
    (fun t => (hk.integral_hasStrictDerivAt t0 t).hasDerivAt) hs h0

/-- C13-15: for ρ̇_u = −θρ_u − Γρ_u − ρ_uQ/C and Ṙ = −θR + Γρ_u − RQ/C with continuous rates
and Γ ≥ 0, nonnegative initial data stay nonnegative. -/
theorem release_positivity (ρu R θ Γ κ : ℝ → ℝ) (t0 : ℝ) (hθ : Continuous θ) (hΓ : Continuous Γ)
    (hκ : Continuous κ) (hΓ0 : ∀ t, 0 ≤ Γ t)
    (hu : ∀ t, HasDerivAt ρu (-θ t * ρu t - Γ t * ρu t - ρu t * κ t) t)
    (hR : ∀ t, HasDerivAt R (-θ t * R t + Γ t * ρu t - R t * κ t) t)
    (hu0 : 0 ≤ ρu t0) (hR0 : 0 ≤ R t0) :
    ∀ t, t0 ≤ t → 0 ≤ ρu t ∧ 0 ≤ R t := by
  have h1 := linear_positivity' ρu (fun t => θ t + Γ t + κ t) (fun _ => 0) t0 (by fun_prop)
    (fun t => by convert hu t using 1; ring) (fun _ _ => le_rfl) hu0
  have h2 := linear_positivity' R (fun t => θ t + κ t) (fun t => Γ t * ρu t) t0 (by fun_prop)
    (fun t => by convert hR t using 1; ring) (fun t ht => mul_nonneg (hΓ0 t) (h1 t ht)) hR0
  exact fun t ht => ⟨h1 t ht, h2 t ht⟩

/-- C13-16: if Ḟ = Γ(1 − F) with continuous Γ ≥ 0 and F(t₀) ∈ [0,1], then F(t) ∈ [0,1] for t ≥ t₀. -/
theorem fraction_in_unit (F Γ : ℝ → ℝ) (t0 : ℝ) (hΓ : Continuous Γ) (hΓ0 : ∀ t, 0 ≤ Γ t)
    (hF : ∀ t, HasDerivAt F (Γ t * (1 - F t)) t) (h0 : 0 ≤ F t0) (h1 : F t0 ≤ 1) :
    ∀ t, t0 ≤ t → 0 ≤ F t ∧ F t ≤ 1 := by
  have a := linear_positivity' F Γ Γ t0 hΓ (fun t => by convert hF t using 1; ring)
    (fun t _ => hΓ0 t) h0
  have b := linear_positivity' (fun t => 1 - F t) Γ (fun _ => 0) t0 hΓ
    (fun t => by convert (hF t).const_sub 1 using 1; ring) (fun _ _ => le_rfl) (by linarith)
  exact fun t ht => ⟨a t ht, by have := b t ht; simp at this; linarith⟩

/-- C13-22 (logarithmic slope of x): from x² = GM/(a₀r²), 2xx′ = GM′/(a₀r²) − 2GM/(a₀r³);
with M′ = sM/r this gives x′ = x(s − 2)/(2r). -/
theorem x_slope {x x' M M' r s c : ℝ} (hx : 0 < x) (hr : 0 < r) (hsq : x ^ 2 = c * M / r ^ 2)
    (hd : 2 * x * x' = c * M' / r ^ 2 - 2 * c * M / r ^ 3) (hM : M' = s * M / r) :
    x' = x * (s - 2) / (2 * r) := by
  have hcM : c * M = x ^ 2 * r ^ 2 := by field_simp at hsq; linarith
  rw [hM] at hd
  have : 2 * x * x' = x ^ 2 * (s - 2) / r := by
    rw [hd]; field_simp; rw [hcM]; ring
  have hx0 : 2 * x ≠ 0 := by positivity
  apply mul_left_cancel₀ hx0
  rw [this]; field_simp

/-- C13-22: with m_tar = M/(eˣ − 1), M′ = sM/r and x′ = x(s − 2)/(2r),
m_tar′/M′ = (1/(eˣ − 1))[1 − ((s − 2)/(2s)) x/(1 − e^{−x})]. -/
theorem target_ratio {M r s x : ℝ} (hM : 0 < M) (hr : 0 < r) (hs : s ≠ 0) (hx : 0 < x) :
    (s * M / r / (Real.exp x - 1) - M * Real.exp x * (x * (s - 2) / (2 * r)) / (Real.exp x - 1) ^ 2) /
      (s * M / r) = ratio s x := by
  have he : 1 < Real.exp x := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hx
  have he1 : Real.exp x - 1 ≠ 0 := by linarith
  have hem : 1 - Real.exp (-x) = (Real.exp x - 1) / Real.exp x := by
    rw [Real.exp_neg]; field_simp
  unfold ratio; rw [hem]
  have := Real.exp_pos x
  field_simp; try ring

/-- C13-22 (chain rule): d/dr [M(r)/(e^{x(r)} − 1)] = M′/(eˣ − 1) − M eˣ x′/(eˣ − 1)². -/
theorem target_mass_deriv {M x : ℝ → ℝ} {M' x' r : ℝ} (hM : HasDerivAt M M' r) (hx : HasDerivAt x x' r)
    (hpos : 0 < x r) :
    HasDerivAt (fun r => M r / (Real.exp (x r) - 1))
      (M' / (Real.exp (x r) - 1) - M r * Real.exp (x r) * x' / (Real.exp (x r) - 1) ^ 2) r := by
  have he : Real.exp (x r) - 1 ≠ 0 := by
    have : 1 < Real.exp (x r) := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hpos
    linarith
  have := hM.div (hx.exp.sub_const 1) he
  convert this using 1; field_simp; try ring

/-- C13-39 (integrated form): if (JC)′ = −JQ with JQ continuous, then
J(t)C(t) = J(tᵢ)C(tᵢ) − ∫_{tᵢ}^t JQ. -/
theorem stock_integrated (J C Q : ℝ → ℝ) (Jd Cd θ : ℝ → ℝ) (ti t : ℝ)
    (hJ : ∀ s, HasDerivAt J (θ s * J s) s) (hC : ∀ s, HasDerivAt C (-θ s * C s - Q s) s)
    (hcont : Continuous fun s => J s * Q s) :
    J t * C t = J ti * C ti - ∫ s in ti..t, J s * Q s := by
  have hd : ∀ s, HasDerivAt (fun s => J s * C s) (-(J s * Q s)) s := by
    intro s; convert (hJ s).mul (hC s) using 1; ring
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := ti) (b := t) (fun s _ => hd s)
    (hcont.neg.intervalIntegrable _ _)
  rw [intervalIntegral.integral_neg] at this
  linarith

/-- C13-40 (algebra): with ρ_bJ = ρ_{b,i}J_i, C_i = κρ_{b,i} and JC = J_iC_i − X,
C = κρ_b(1 − X/(J_iC_i)); with C̄ = κρ̄_b e^{−ηF}, Δ_C = C/C̄ = Δ_b(1 − B)/e^{−ηF}. -/
theorem local_capacity {J Ji ρb ρbi κ X C : ℝ} (hJ : 0 < J) (hJi : 0 < Ji) (hρ : 0 < ρbi) (hκ : 0 < κ)
    (hcons : ρb * J = ρbi * Ji) (hC : J * C = Ji * (κ * ρbi) - X) :
    C = κ * ρb * (1 - X / (Ji * (κ * ρbi))) := by
  have : ρb = ρbi * Ji / J := by field_simp; linarith
  rw [this]; field_simp; field_simp at hC; linarith

theorem capacity_contrast (κ ρb ρbar B e : ℝ) (hκ : κ ≠ 0) (hρ : ρbar ≠ 0) (he : e ≠ 0) :
    κ * ρb * (1 - B) / (κ * ρbar * e) = (ρb / ρbar) * (1 - B) / e := by
  field_simp

/-- ∫₀^F e^{−ηu} du = (1 − e^{−ηF})/η. -/
theorem integral_exp_neg {η F : ℝ} (hη : η ≠ 0) :
    ∫ u in (0:ℝ)..F, Real.exp (-η * u) = (1 - Real.exp (-η * F)) / η := by
  have hd : ∀ u, HasDerivAt (fun u => -Real.exp (-η * u) / η) (Real.exp (-η * u)) u := by
    intro u
    have h1 : HasDerivAt (fun u => -η * u) (-η) u := by
      simpa using (hasDerivAt_id u).const_mul (-η)
    have := h1.exp.neg.div_const η
    convert this using 1; field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((by fun_prop : Continuous fun u => Real.exp (-η * u)).intervalIntegrable _ _)]
  simp; field_simp; ring

/-- C13-41: if Δ_b ≥ d > 0 on [0, F] (continuous), B = η∫₀^F e^{−ηu}/Δ_b(u) du ≤ (1 − e^{−ηF})/d. -/
theorem density_floor (Δ : ℝ → ℝ) (hΔ : Continuous Δ) {η F d : ℝ} (hη : 0 < η) (hF : 0 ≤ F) (hd : 0 < d)
    (hfloor : ∀ u, 0 ≤ u → u ≤ F → d ≤ Δ u) :
    η * ∫ u in (0:ℝ)..F, Real.exp (-η * u) / Δ u ≤ (1 - Real.exp (-η * F)) / d := by
  have hle : ∫ u in (0:ℝ)..F, Real.exp (-η * u) / Δ u ≤ ∫ u in (0:ℝ)..F, Real.exp (-η * u) / d := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hF
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div (by fun_prop) hΔ.continuousOn
      intro u hu; rw [Set.uIcc_of_le hF] at hu; linarith [hfloor u hu.1 hu.2]
    · exact (by fun_prop : Continuous fun u => Real.exp (-η * u) / d).intervalIntegrable _ _
    · intro u hu
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le hd (hfloor u hu.1.le hu.2.le)
  have : ∫ u in (0:ℝ)..F, Real.exp (-η * u) / d = (1 - Real.exp (-η * F)) / η / d := by
    rw [intervalIntegral.integral_div, integral_exp_neg hη.ne']
  rw [this] at hle
  calc η * ∫ u in (0:ℝ)..F, Real.exp (-η * u) / Δ u ≤ η * ((1 - Real.exp (-η * F)) / η / d) :=
        mul_le_mul_of_nonneg_left hle hη.le
    _ = _ := by field_simp

/-- C13-51, C13-52: a density obeying ∂_tρ = ∂_x J with zero boundary flux has constant total
∫_a^b ρ; and ρ = cρ_* (∂_x(ρ/ρ_*) = 0) carries zero flux J = Dρ_*∂_x(ρ/ρ_*). -/
theorem no_flux_conservation (J : ℝ → ℝ) (J' : ℝ → ℝ) {a b : ℝ} (hJ : ∀ x, HasDerivAt J (J' x) x)
    (hJ' : Continuous J') (ha : J a = 0) (hb : J b = 0) : ∫ x in a..b, J' x = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hJ x) (hJ'.intervalIntegrable _ _), ha, hb]
  ring

theorem stationary_profile (D ρs : ℝ → ℝ) (c : ℝ) (hρs : ∀ x, ρs x ≠ 0) (x : ℝ) :
    HasDerivAt (fun y => c * ρs y / ρs y) 0 x ∧ D x * ρs x * 0 = 0 := by
  refine ⟨?_, by ring⟩
  have : (fun y => c * ρs y / ρs y) = fun _ => c := by funext y; field_simp [hρs y]
  rw [this]; exact hasDerivAt_const x c

/-! ### Spatial-average estimator (C13-06), finite form -/

section Average
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

/-- C13-06: on a finite probability space with cell volumes v_i (Σv = V) and E[q_i] = q̄,
E[⟨q⟩] = q̄ and Var⟨q⟩ = (1/V²)Σ_ij v_iv_j C_ij with C_ij = E[(q_i − q̄)(q_j − q̄)]. -/
theorem average_mean_var (P : Ω → ℝ) (hP : ∑ ω, P ω = 1) (v : ι → ℝ) (V : ℝ) (hV : ∑ i, v i = V)
    (hV0 : V ≠ 0) (q : Ω → ι → ℝ) (qb : ℝ) (hmean : ∀ i, ∑ ω, P ω * q ω i = qb) :
    ∑ ω, P ω * ((1 / V) * ∑ i, v i * q ω i) = qb ∧
      ∑ ω, P ω * ((1 / V) * ∑ i, v i * q ω i - qb) ^ 2 =
        (1 / V ^ 2) * ∑ i, ∑ j, v i * v j * ∑ ω, P ω * ((q ω i - qb) * (q ω j - qb)) := by
  have hdev : ∀ ω, (1 / V) * ∑ i, v i * q ω i - qb = (1 / V) * ∑ i, v i * (q ω i - qb) := by
    intro ω
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hV]; field_simp
  constructor
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ i, ∑ ω, P ω * (1 / V * (v i * q ω i)) = 1 / V * v i * qb := by
      intro i; rw [← hmean i, Finset.mul_sum]; exact Finset.sum_congr rfl (fun ω _ => by ring)
    simp only [this, ← Finset.sum_mul, ← Finset.mul_sum, hV]; field_simp
  · have hsq : ∀ ω, ((1 / V) * ∑ i, v i * (q ω i - qb)) ^ 2 =
        (1 / V ^ 2) * ∑ i, ∑ j, v i * v j * ((q ω i - qb) * (q ω j - qb)) := by
      intro ω
      rw [mul_pow, one_div_pow, pow_two (∑ i, v i * (q ω i - qb)), Finset.sum_mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
    have swap : ∀ g : Ω → ι → ι → ℝ, ∑ ω, ∑ i, ∑ j, g ω i j = ∑ i, ∑ j, ∑ ω, g ω i j := by
      intro g; rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    calc ∑ ω, P ω * ((1 / V) * ∑ i, v i * q ω i - qb) ^ 2
        = ∑ ω, ∑ i, ∑ j, (1 / V ^ 2) * (v i * v j * (P ω * ((q ω i - qb) * (q ω j - qb)))) := by
          refine Finset.sum_congr rfl (fun ω _ => ?_)
          rw [hdev, hsq, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = ∑ i, ∑ j, ∑ ω, (1 / V ^ 2) * (v i * v j * (P ω * ((q ω i - qb) * (q ω j - qb)))) := swap _
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.mul_sum, Finset.mul_sum]

/-- C13-06 (1/V decay): if Σ_j v_j|C_ij| ≤ L for every i, then Var⟨q⟩ ≤ L/V. -/
theorem average_var_bound (v : ι → ℝ) (V L : ℝ) (hV : ∑ i, v i = V) (hV0 : 0 < V) (hv : ∀ i, 0 ≤ v i)
    (Cv : ι → ι → ℝ) (hL : ∀ i, ∑ j, v j * |Cv i j| ≤ L) :
    (1 / V ^ 2) * ∑ i, ∑ j, v i * v j * Cv i j ≤ L / V := by
  have h1 : ∑ i, ∑ j, v i * v j * Cv i j ≤ ∑ i, v i * L := by
    apply Finset.sum_le_sum; intro i _
    calc ∑ j, v i * v j * Cv i j ≤ ∑ j, v i * (v j * |Cv i j|) :=
          Finset.sum_le_sum (fun j _ => by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left (le_abs_self _) (mul_nonneg (hv i) (hv j)))
      _ = v i * ∑ j, v j * |Cv i j| := by rw [Finset.mul_sum]
      _ ≤ v i * L := mul_le_mul_of_nonneg_left (hL i) (hv i)
  rw [← Finset.sum_mul, hV] at h1
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hV0]
  nlinarith
end Average

/-! ### Mixing fraction (C13-69), first entry (C13-76), resolved kernel (C13-78) -/

section Mixing
open Entropic.AppFG.Info
variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Mutual information I(A;Y) = H(A) + H(Y) − H(A,Y). -/
def mutualInfo (P : X → Y → ℝ) : ℝ := H (pX P) + H (pY P) - Hjoint P

/-- H(Y) ≤ H(A,Y): conditional entropy is nonnegative. -/
theorem H_le_joint (P : X → Y → ℝ) (hP : ∀ x y, 0 ≤ P x y) : H (pY P) ≤ Hjoint P := by
  have e : Hjoint P - H (pY P) = ∑ x, ∑ y, P x y * (Real.log (pY P y) - Real.log (P x y)) := by
    have := sum_mul_log_pY P
    unfold Hjoint; simp only [negMulLog, mul_sub, Finset.sum_sub_distrib]
    rw [this]; simp only [neg_mul, Finset.sum_neg_distrib]; ring
  have : 0 ≤ ∑ x, ∑ y, P x y * (Real.log (pY P y) - Real.log (P x y)) := by
    apply Finset.sum_nonneg; intro x _; apply Finset.sum_nonneg; intro y _
    rcases (hP x y).eq_or_lt with h | h
    · rw [← h]; simp
    · exact mul_nonneg h.le (by linarith [Real.log_le_log h (le_pY hP x y)])
  linarith

/-- C13-69: H(A|Y) = H(A) − I(A;Y), and ε_mix = 1 − I/H(A) ∈ [0,1] when H(A) > 0;
ε_mix = 1 iff the joint law is a product. -/
theorem mixing_fraction (P : X → Y → ℝ) (hP : ∀ x y, 0 ≤ P x y) (h1 : ∑ x, ∑ y, P x y = 1)
    (hH : 0 < H (pX P)) :
    Hjoint P - H (pY P) = H (pX P) - mutualInfo P ∧
      0 ≤ 1 - mutualInfo P / H (pX P) ∧ 1 - mutualInfo P / H (pX P) ≤ 1 ∧
      (1 - mutualInfo P / H (pX P) = 1 ↔ ∀ x y, P x y = pX P x * pY P y) := by
  have hI0 : 0 ≤ mutualInfo P := by unfold mutualInfo; linarith [subadditive P hP h1]
  have hIH : mutualInfo P ≤ H (pX P) := by unfold mutualInfo; linarith [H_le_joint P hP]
  refine ⟨by unfold mutualInfo; ring, ?_, ?_, ?_⟩
  · rw [sub_nonneg, div_le_one hH]; exact hIH
  · have := div_nonneg hI0 hH.le; linarith
  · rw [← subadditive_eq_iff P hP h1]
    constructor
    · intro h
      have : mutualInfo P / H (pX P) = 0 := by linarith
      rw [div_eq_zero_iff] at this
      rcases this with h | h
      · unfold mutualInfo at h; linarith
      · linarith
    · intro h; have : mutualInfo P = 0 := by unfold mutualInfo; linarith
      rw [this]; simp

/-- C13-69: if A is a function of Y (each y carries one label), I(A;Y) = H(A), so ε_mix = 0. -/
theorem mixing_zero_of_function (P : X → Y → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (hdet : ∀ x y, P x y = 0 ∨ P x y = pY P y) (hH : 0 < H (pX P)) :
    1 - mutualInfo P / H (pX P) = 0 := by
  have : Hjoint P = H (pY P) := by
    have e : Hjoint P - H (pY P) = ∑ x, ∑ y, P x y * (Real.log (pY P y) - Real.log (P x y)) := by
      have := sum_mul_log_pY P
      unfold Hjoint; simp only [negMulLog, mul_sub, Finset.sum_sub_distrib]
      rw [this]; simp only [neg_mul, Finset.sum_neg_distrib]; ring
    have : ∑ x, ∑ y, P x y * (Real.log (pY P y) - Real.log (P x y)) = 0 := by
      apply Finset.sum_eq_zero; intro x _; apply Finset.sum_eq_zero; intro y _
      rcases hdet x y with h | h <;> rw [h] <;> ring
    linarith
  unfold mutualInfo; rw [this]; field_simp; ring

/-- C13-78: if 0 ≤ I ≤ H(A), H(A) > 0 and İ ≤ 0, then K = 1 − I/H(A) ∈ [0,1] and K̇ = −İ/H(A) ≥ 0. -/
theorem resolved_kernel {I : ℝ → ℝ} {I' HA t : ℝ} (hHA : 0 < HA) (hI : HasDerivAt I I' t)
    (h0 : 0 ≤ I t) (h1 : I t ≤ HA) (hd : I' ≤ 0) :
    0 ≤ 1 - I t / HA ∧ 1 - I t / HA ≤ 1 ∧ HasDerivAt (fun s => 1 - I s / HA) (-I' / HA) t ∧ 0 ≤ -I' / HA := by
  refine ⟨by rw [sub_nonneg, div_le_one hHA]; exact h1, by have := div_nonneg h0 hHA.le; linarith,
    by convert (hI.div_const HA).const_sub 1 using 1; ring, div_nonneg (by linarith) hHA.le⟩
end Mixing

/-- C13-76: F_Z(z) = P[∃ z′ ≥ z, event(z′)] is nonincreasing in z (absorbing first entry). -/
theorem absorbing_first_entry {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (E : ℝ → Set Ω) {z1 z2 : ℝ} (h : z1 ≤ z2) :
    μ (⋃ z' ∈ Set.Ici z2, E z') ≤ μ (⋃ z' ∈ Set.Ici z1, E z') := by
  apply MeasureTheory.measure_mono
  intro ω hω
  simp only [Set.mem_iUnion, Set.mem_Ici] at hω ⊢
  obtain ⟨z', hz, hω⟩ := hω
  exact ⟨z', le_trans h hz, hω⟩

/-- C13-89: the hazard rate enters Q_u and Q_R only through q with opposite signs, so
δ(Q_u + Q_R) is independent of δΓ. -/
theorem hazard_cancels (q q' : ℝ) (u Xu XR : Fin 4 → ℝ) :
    (-q • u + Xu) + (q • u + XR) = (-q' • u + Xu) + (q' • u + XR) := by
  ext μ; simp; ring

/-- C13-95: for an orthogonal projector P and W_α†W_β = δ_αβ P, (I − P)†(I − P) +
(1/9)Σ_α (W_αP)†(W_αP) = I. -/
theorem formation_isometry {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ) (W : Fin 9 → Matrix n n ℂ)
    (hP : P * P = P) (hPh : Pᴴ = P) (hW : ∀ α, (W α)ᴴ * W α = P) :
    (1 - P)ᴴ * (1 - P) + (1/9 : ℂ) • ∑ α, (W α * P)ᴴ * (W α * P) = 1 := by
  have h1 : ∀ α, (W α * P)ᴴ * (W α * P) = P := by
    intro α
    rw [Matrix.conjTranspose_mul, hPh, show P * (W α)ᴴ * (W α * P) = P * ((W α)ᴴ * W α) * P by
      simp only [Matrix.mul_assoc], hW, hP, hP]
  rw [Finset.sum_congr rfl (fun α _ => h1 α), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPh]
  norm_num
  rw [sub_mul, mul_sub, mul_sub, hP]; simp

end Entropic.AppO
