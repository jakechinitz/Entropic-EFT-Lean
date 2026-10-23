import Entropic.AppFG.Born
import Entropic.AppFG.Subadditivity
import Entropic.Spine
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! Appendix O: unimodular algebra, constant-mode projection, exchange currents, positivity of the
release system, admissibility projection, density-ratio bounds, isometries, reset coefficients and
clock monotonicity (ledger C13-01, -03 … -05, -07, -11, -13 … -16, -19, -21, -23, -25, -26, -28, -29,
-31, -39, -44, -45, -48 … -53, -58, -61, -63, -72, -74, -79 … -81, -83, -90, -93, -95, -98, -100). -/

noncomputable section
namespace Entropic.AppO
open Real Matrix

/-- C13-01: dim(V_{3/2} ⊗ V_{3/2}) = 16 = 7 + 9 = dim V₃ + dim(V₁ ⊗ V₁). -/
theorem face_map_dims : 4 * 4 = 16 ∧ 7 + 3 * 3 = 16 := ⟨rfl, rfl⟩

/-- C13-03: R_μν − ¼Rg_μν = 8πG(T_μν − ¼Tg_μν) together with R + 8πGT = 4Λ gives
R_μν − ½Rg_μν + Λg_μν = 8πG T_μν (componentwise). -/
theorem unimodular_to_einstein {Rmn gmn Tmn R T Λ k : ℝ}
    (htf : Rmn - R / 4 * gmn = k * (Tmn - T / 4 * gmn)) (hΛ : R + k * T = 4 * Λ) :
    Rmn - R / 2 * gmn + Λ * gmn = k * Tmn := by
  have : k * T = 4 * Λ - R := by linarith
  linear_combination htf + (-gmn / 4) * hΛ

/-- C13-03 (integration step): a function with zero derivative everywhere on ℝ is constant. -/
theorem integration_constant (f : ℝ → ℝ) (hf : ∀ x, HasDerivAt f 0 x) (x y : ℝ) : f x = f y :=
  is_const_of_deriv_eq_zero (fun x => (hf x).differentiableAt) (fun x => (hf x).deriv) x y

/-- C13-04: the trace-free part is invariant under T ↦ T − ρ_vac g (using g^μ_μ = 4). -/
theorem vacuum_shift (Tmn gmn T ρ : ℝ) :
    (Tmn - ρ * gmn) - (T - 4 * ρ) / 4 * gmn = Tmn - T / 4 * gmn := by ring

/-- C13-05: P₀ = 11ᵀ/N is the orthogonal projector onto constants; r = r̄1 + r_⊥ with Σr_⊥ = 0. -/
theorem constant_mode {N : ℕ} (hN : 0 < N) (r : Fin N → ℝ) :
    let rb := (∑ e, r e) / N
    ∑ e, (r e - rb) = 0 ∧ (∀ e, r e = rb + (r e - rb)) := by
  intro rb
  refine ⟨?_, fun e => by ring⟩
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [rb]; field_simp; ring

/-- C13-07: with V_F′ = ρ̇_Λ and φ̇ = 1, δρ_Λ − (ρ̇_Λ/φ̇)δφ = V_F′δφ − V_F′δφ = 0. -/
theorem clock_homogeneity (V' δφ : ℝ) : V' * δφ - (V' / 1) * δφ = 0 := by ring

/-- C13-11: for u_μ = −∇_μφ (symmetric Hessian) with ∇(u·u) = 0, the geodesic acceleration
u^μ∇_μu_ν = −(u^μH_μν) equals ½∇_ν(u·u) = −u^μH_νμ = 0. -/
theorem clock_geodesic (H : Fin 4 → Fin 4 → ℝ) (w : Fin 4 → ℝ) (hH : ∀ μ ν, H μ ν = H ν μ)
    (hnorm : ∀ ν, ∑ μ, w μ * H ν μ = 0) (ν : Fin 4) : ∑ μ, w μ * H μ ν = 0 := by
  rw [← hnorm ν]; exact Finset.sum_congr rfl (fun μ _ => by rw [hH])

/-- C13-13: Q_u + Q_R + Q_Λ = 0 for Q_u = −qu + (ρ_u/C)∇V, Q_R = qu + (R/C)∇V, Q_Λ = −∇V, C = ρ_u + R. -/
theorem currents_sum (q ρu R : ℝ) (u dV : Fin 4 → ℝ) (hC : ρu + R ≠ 0) :
    (-q • u + (ρu / (ρu + R)) • dV) + (q • u + (R / (ρu + R)) • dV) + -dV = 0 := by
  ext μ; simp; field_simp; ring

/-- C13-14: with ∇V = −Qu, Q_u = (−q − ρ_uQ/C)u, so ρ̇_u + θρ_u = −q − ρ_uQ/C (similarly for R, C). -/
theorem common_clock (q ρu R Q : ℝ) (u : Fin 4 → ℝ) :
    -q • u + (ρu / (ρu + R)) • (-Q • u) = (-q - ρu * Q / (ρu + R)) • u ∧
      q • u + (R / (ρu + R)) • (-Q • u) = (q - R * Q / (ρu + R)) • u := by
  constructor <;> (ext μ; simp; ring)

/-! ### Positivity of the release system (C13-15, C13-16) -/

/-- Integrating-factor lemma: if f′ = −k f + s with s ≥ 0 on [t₀, t] (K′ = k) and f(t₀) ≥ 0, then f ≥ 0. -/
theorem linear_positivity (f K k s : ℝ → ℝ) (t0 : ℝ) (hf : ∀ t, HasDerivAt f (-k t * f t + s t) t)
    (hK : ∀ t, HasDerivAt K (k t) t) (hs : ∀ t, t0 ≤ t → 0 ≤ s t) (h0 : 0 ≤ f t0) :
    ∀ t, t0 ≤ t → 0 ≤ f t := by
  set g : ℝ → ℝ := fun t => f t * Real.exp (K t)
  have hg : ∀ t, HasDerivAt g (s t * Real.exp (K t)) t := by
    intro t
    have := (hf t).mul ((hK t).exp)
    convert this using 1; ring
  have hmono : MonotoneOn g (Set.Ici t0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici t0)
    · exact fun t _ => (hg t).continuousAt.continuousWithinAt
    · exact fun t _ => (hg t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hg t).deriv]
      exact mul_nonneg (hs t (le_of_lt ht)) (Real.exp_pos _).le
  intro t ht
  have := hmono (Set.mem_Ici.mpr le_rfl) ht ht
  have hg0 : 0 ≤ g t0 := mul_nonneg h0 (Real.exp_pos _).le
  have hgt : 0 ≤ g t := le_trans hg0 this
  have := Real.exp_pos (K t)
  simp only [g] at hgt
  exact nonneg_of_mul_nonneg_left hgt this

/-- C13-16: with q = Γρ_u = Γ(C − R), Ṙ = −θR + q − RQ/C and Ċ = −θC − Q, F = R/C obeys Ḟ = Γ(1 − F). -/
theorem reallocated_fraction (R C Rd Cd θ Γ Q : ℝ) (hC : C ≠ 0)
    (hR : Rd = -θ * R + Γ * (C - R) - R * Q / C) (hCd : Cd = -θ * C - Q) :
    (Rd * C - R * Cd) / C ^ 2 = Γ * (1 - R / C) := by
  rw [hR, hCd]; field_simp; ring

/-- C13-19: if ∇V = λu with u·u = −1, the transverse force h(∇V) = ∇V + u(u·∇V) vanishes. -/
theorem transverse_force (u : Fin 4 → ℝ) (lam uu : ℝ) (hu : uu = -1) :
    lam • u + (uu * lam) • u = 0 := by
  rw [hu]; ext μ; simp; try ring

/-! ### Admissibility projection (C13-21) and density ratio (C13-23, C13-25, C13-26, C13-28, C13-29) -/

/-- C13-21 (finite form): Σ[ϱ]₊ ≥ Σϱ = M > 0, so ρ_adm = M[ϱ]₊/Σ[ϱ]₊ is ≥ 0, has total M, and equals ϱ
when ϱ ≥ 0. -/
theorem admissibility_projection {ι : Type*} [Fintype ι] (ϱ : ι → ℝ) {M : ℝ} (hM : 0 < M)
    (hsum : ∑ i, ϱ i = M) :
    M ≤ ∑ i, max (ϱ i) 0 ∧ (∀ i, 0 ≤ M * max (ϱ i) 0 / ∑ j, max (ϱ j) 0) ∧
      ∑ i, M * max (ϱ i) 0 / ∑ j, max (ϱ j) 0 = M ∧
      ((∀ i, 0 ≤ ϱ i) → ∀ i, M * max (ϱ i) 0 / ∑ j, max (ϱ j) 0 = ϱ i) := by
  have hle : M ≤ ∑ i, max (ϱ i) 0 := by
    rw [← hsum]; exact Finset.sum_le_sum (fun i _ => le_max_left _ _)
  have hpos : 0 < ∑ i, max (ϱ i) 0 := lt_of_lt_of_le hM hle
  refine ⟨hle, fun i => by positivity, ?_, fun hnn i => ?_⟩
  · rw [← Finset.sum_div, ← Finset.mul_sum]; field_simp
  · have : ∑ j, max (ϱ j) 0 = M := by
      rw [← hsum]; exact Finset.sum_congr rfl (fun j _ => max_eq_left (hnn j))
    rw [this, max_eq_left (hnn i)]; field_simp

/-- The contact-target ratio R(s, x) = (1/(eˣ − 1))[1 − ((s − 2)/(2s)) x/(1 − e^{−x})]. -/
def ratio (s x : ℝ) : ℝ := (1 / (Real.exp x - 1)) * (1 - (s - 2) / (2 * s) * (x / (1 - Real.exp (-x))))

/-- C13-23: for x > 0 and 0 < s ≤ 2 the ratio is > 0. -/
theorem ratio_pos {s x : ℝ} (hx : 0 < x) (hs : 0 < s) (hs2 : s ≤ 2) : 0 < ratio s x := by
  unfold ratio
  have he : 1 < Real.exp x := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hx
  have he' : Real.exp (-x) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have h1 : 0 < 1 / (Real.exp x - 1) := by apply div_pos one_pos; linarith
  have h2 : (s - 2) / (2 * s) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have h3 : 0 < x / (1 - Real.exp (-x)) := div_pos hx (by linarith)
  have : 0 < 1 - (s - 2) / (2 * s) * (x / (1 - Real.exp (-x))) := by nlinarith
  positivity

/-- C13-26 (reduction): for 0 < s ≤ 3 the ratio is bounded below by its s = 3 value R₃(x). -/
theorem ratio_ge_three {s x : ℝ} (hx : 0 < x) (hs : 0 < s) (hs3 : s ≤ 3) : ratio 3 x ≤ ratio s x := by
  unfold ratio
  have he : 1 < Real.exp x := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hx
  have he' : Real.exp (-x) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have h1 : 0 < 1 / (Real.exp x - 1) := by apply div_pos one_pos; linarith
  have h3 : 0 < x / (1 - Real.exp (-x)) := div_pos hx (by linarith)
  have hmono : (s - 2) / (2 * s) ≤ (3 - 2) / (2 * 3) := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  apply mul_le_mul_of_nonneg_left _ h1.le
  nlinarith [mul_le_mul_of_nonneg_right hmono h3.le]

/-- C13-25: for nonincreasing ρ ≥ 0 on [0, r], M(r) = ∫₀^r 4πt²ρ ≥ ρ(r)(4π/3)r³, hence
s = r·4πr²ρ(r)/M(r) ≤ 3. -/
theorem mass_slope_le_three (ρ : ℝ → ℝ) (hρc : Continuous ρ) {r : ℝ} (hr : 0 < r)
    (hmono : ∀ t, 0 ≤ t → t ≤ r → ρ r ≤ ρ t) (hM : 0 < ∫ t in (0:ℝ)..r, 4 * π * t ^ 2 * ρ t) :
    r * (4 * π * r ^ 2 * ρ r) / (∫ t in (0:ℝ)..r, 4 * π * t ^ 2 * ρ t) ≤ 3 := by
  have hlow : ρ r * (4 * π / 3 * r ^ 3) ≤ ∫ t in (0:ℝ)..r, 4 * π * t ^ 2 * ρ t := by
    have hint : ∫ t in (0:ℝ)..r, 4 * π * t ^ 2 * ρ r = ρ r * (4 * π / 3 * r ^ 3) := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_pow]; ring
    rw [← hint]
    apply intervalIntegral.integral_mono_on hr.le
    · exact (by fun_prop : Continuous fun t : ℝ => 4 * π * t ^ 2 * ρ r).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun t : ℝ => 4 * π * t ^ 2 * ρ t).intervalIntegrable _ _
    · intro t ht
      exact mul_le_mul_of_nonneg_left (hmono t ht.1 ht.2) (by positivity)
  rw [div_le_iff₀ hM]; nlinarith [Real.pi_pos]

/-- C13-28: δg/g_tar = (αN₋ − (1 − α)m_tar)/(M_b + m_tar) for g ∝ (M_b + m)/r². -/
theorem projection_change (Mb mtar Nm α : ℝ) (h : Mb + mtar ≠ 0) :
    (Mb + α * (mtar + Nm) - (Mb + mtar)) / (Mb + mtar) = (α * Nm - (1 - α) * mtar) / (Mb + mtar) := by
  congr 1; ring

/-- C13-29: if N₋ ≤ ζM_b, m_tar ≥ 0 and α ∈ [0,1], then |δg/g| ≤ max(ζ, 1 − α). -/
theorem projection_bound {Mb mtar Nm α ζ : ℝ} (hMb : 0 < Mb) (hm : 0 ≤ mtar) (hN0 : 0 ≤ Nm)
    (hN : Nm ≤ ζ * Mb) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    |(α * Nm - (1 - α) * mtar) / (Mb + mtar)| ≤ max ζ (1 - α) := by
  have hpos : 0 < Mb + mtar := by linarith
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos, abs_le]
  have hz : 0 ≤ ζ := by nlinarith
  constructor
  · nlinarith [le_max_right ζ (1 - α), le_max_left ζ (1 - α)]
  · nlinarith [le_max_right ζ (1 - α), le_max_left ζ (1 - α)]

/-- C13-31: σ_r = 0 and σ_θ² + σ_φ² = v_c² = r dΦ/dr satisfy the spherical Jeans equation. -/
theorem circular_jeans (ρ r dΦ : ℝ) (hr : r ≠ 0) :
    0 + ρ / r * (2 * 0 - r * dΦ) = -ρ * dΦ := by field_simp; ring

/-! ### Stock balance, equation of state, linear clock, fluid split (C13-39, -44, -45, -48) -/

/-- C13-39: J̇ = θJ and Ċ + θC = −Q give (JC)′ = −JQ. -/
theorem stock_balance (J C Jd Cd θ Q : ℝ) (hJ : Jd = θ * J) (hC : Cd + θ * C = -Q) :
    Jd * C + J * Cd = -(J * Q) := by
  rw [hJ]; linear_combination J * hC

/-- C13-44: w_eff = −1 − (1/3) d ln ρ_Λ/d ln a with ρ_Λ ∝ I and dI/d ln a = a^{−3}e^{−ηF}F′ is
< −1 whenever F′ > 0 and I > 0. -/
theorem effective_w {a I F' η F : ℝ} (ha : 0 < a) (hI : 0 < I) (hF : 0 < F') :
    -1 - (1/3) * (a ^ (-3:ℤ) * Real.exp (-η * F) * F' / I) < -1 := by
  have : 0 < a ^ (-3:ℤ) * Real.exp (-η * F) * F' / I := by positivity
  linarith

/-- C13-45: X = ½(1 − 2Ψ)(1 + δφ̇)² = ½ to first order iff δφ̇ = Ψ. -/
theorem linear_clock (Ψ dφ : ℝ) : (1/2) * (1 + 2 * dφ - 2 * Ψ) = 1/2 ↔ dφ = Ψ := by
  constructor <;> intro h <;> linarith

/-- C13-48: ρ_D = C − ρ_ref + V, p_D = −V give ρ_D + p_D = C − ρ_ref, and the decomposition
C uu − V g = (ρ_D + p_D)uu + p_D g + ρ_ref uu holds componentwise. -/
theorem conserved_fluid (C ρref V uu g : ℝ) :
    C * uu - V * g = ((C - ρref + V) + -V) * uu + -V * g + ρref * uu := by ring

/-! ### Radial adjustment and dissipation (C13-49, C13-50, C13-53) -/

/-- C13-49: w⁺ = (1 − s)w + s p m preserves the angular marginal, positivity, and contracts toward p m. -/
theorem radial_adjustment {ι : Type*} [Fintype ι] (w p : ι → ℝ) (s : ℝ) (hp : ∑ i, p i = 1)
    (hw : ∀ i, 0 ≤ w i) (hp0 : ∀ i, 0 ≤ p i) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∑ i, ((1 - s) * w i + s * p i * ∑ j, w j) = ∑ i, w i ∧
      (∀ i, 0 ≤ (1 - s) * w i + s * p i * ∑ j, w j) ∧
      (∀ i, (1 - s) * w i + s * p i * ∑ j, w j - p i * ∑ j, w j = (1 - s) * (w i - p i * ∑ j, w j)) := by
  refine ⟨?_, fun i => ?_, fun i => by ring⟩
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum, hp]; ring
  · have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hw j)
    have : 0 ≤ 1 - s := by linarith
    exact add_nonneg (mul_nonneg this (hw i)) (mul_nonneg (mul_nonneg hs0 (hp0 i)) (by assumption))

/-- C13-50: for ẇ_i = Σ_j c_ij(x_j − x_i)m with symmetric c ≥ 0, Σ_i ẇ_i = 0 and
Σ_i ẇ_i ln x_i = −½Σ_ij m c_ij (x_i − x_j)(ln x_i − ln x_j) ≤ 0. -/
theorem entropy_dissipation {ι : Type*} [Fintype ι] (c : ι → ι → ℝ) (x : ι → ℝ) (m : ℝ)
    (hc : ∀ i j, c i j = c j i) (hc0 : ∀ i j, 0 ≤ c i j) (hm : 0 ≤ m) (hx : ∀ i, 0 < x i) :
    ∑ i, ∑ j, c i j * (x j - x i) * m = 0 ∧
      ∑ i, (∑ j, c i j * (x j - x i) * m) * Real.log (x i) =
        -(1/2) * ∑ i, ∑ j, m * c i j * (x i - x j) * (Real.log (x i) - Real.log (x j)) ∧
      ∑ i, (∑ j, c i j * (x j - x i) * m) * Real.log (x i) ≤ 0 := by
  have A1 : ∑ i, ∑ j, c i j * (x j - x i) * m = ∑ i, ∑ j, c i j * (x i - x j) * m := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [hc]))
  have E1 : ∑ i, ∑ j, c i j * (x j - x i) * m + ∑ i, ∑ j, c i j * (x i - x j) * m = 0 := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_eq_zero; intro i _
    rw [← Finset.sum_add_distrib]; apply Finset.sum_eq_zero; intro j _; ring
  have h1 : ∑ i, ∑ j, c i j * (x j - x i) * m = 0 := by linarith
  have A : ∑ i, ∑ j, c i j * (x j - x i) * m * Real.log (x i) =
      ∑ i, ∑ j, c i j * (x i - x j) * m * Real.log (x j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [hc]))
  have E : ∑ i, ∑ j, c i j * (x j - x i) * m * Real.log (x i) +
      ∑ i, ∑ j, c i j * (x i - x j) * m * Real.log (x j) =
      -∑ i, ∑ j, m * c i j * (x i - x j) * (Real.log (x i) - Real.log (x j)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have h2 : ∑ i, (∑ j, c i j * (x j - x i) * m) * Real.log (x i) =
      -(1/2) * ∑ i, ∑ j, m * c i j * (x i - x j) * (Real.log (x i) - Real.log (x j)) := by
    simp only [Finset.sum_mul]
    linarith
  refine ⟨h1, h2, ?_⟩
  rw [h2]
  have : 0 ≤ ∑ i, ∑ j, m * c i j * (x i - x j) * (Real.log (x i) - Real.log (x j)) := by
    apply Finset.sum_nonneg; intro i _; apply Finset.sum_nonneg; intro j _
    have hmono : 0 ≤ (x i - x j) * (Real.log (x i) - Real.log (x j)) := by
      rcases le_total (x i) (x j) with h | h
      · have := Real.log_le_log (hx i) h; nlinarith
      · have := Real.log_le_log (hx j) h; nlinarith
    have := mul_nonneg hm (hc0 i j)
    nlinarith
  linarith

/-- C13-53: P_A B_A = 0 and W ⪰ 0 give P_A (B_A W B_A†) P_A† = 0. -/
theorem protected_null {n m : Type*} [Fintype n] [Fintype m] (P : Matrix n n ℂ) (B : Matrix n m ℂ)
    (W : Matrix m m ℂ) (h : P * B = 0) : P * (B * W * Bᴴ) * Pᴴ = 0 := by
  rw [show P * (B * W * Bᴴ) * Pᴴ = (P * B) * W * (P * B)ᴴ by
    rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc], h]; simp

/-! ### Normalization, overlaps, kernels (C13-58, -61, -63, -72, -74) -/

/-- C13-58: normalizing weights w_h e^{−CN} over histories at fixed N removes C. -/
theorem constant_cancels {ι : Type*} (S : Finset ι) (w : ι → ℝ) (C N : ℝ) (h : ι) (hw : 0 < ∑ x ∈ S, w x) :
    w h * Real.exp (-C * N) / ∑ x ∈ S, w x * Real.exp (-C * N) = w h / ∑ x ∈ S, w x := by
  rw [← Finset.sum_mul]; have := Real.exp_pos (-C * N); field_simp

/-- C13-61: identical record states give γ = 1, C_rec = Σp_ip_j = 1 and f_rec = 0. -/
theorem identity_free_record {ι : Type*} (S : Finset ι) (p : ι → ℝ) (hp : ∑ i ∈ S, p i = 1) :
    ∑ i ∈ S, ∑ j ∈ S, p i * p j * (1:ℝ) ^ 2 = 1 ∧ 1 - ∑ i ∈ S, ∑ j ∈ S, p i * p j * (1:ℝ) ^ 2 = 0 := by
  have : ∑ i ∈ S, ∑ j ∈ S, p i * p j * (1:ℝ) ^ 2 = 1 := by
    simp only [one_pow, mul_one, ← Finset.mul_sum, hp, ← Finset.sum_mul, one_mul]
  exact ⟨this, by rw [this]; ring⟩

/-- C13-63: the fresh-draw kernel K(b,b′) = p(b′) has stationary law p. -/
theorem fresh_draw {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∑ b, p b = 1) (b' : ι) :
    ∑ b, p b * p b' = p b' := by rw [← Finset.sum_mul, hp, one_mul]

/-- C13-72: for K_a = aδ + (1 − a)p with a > 0 and p not a point mass, the joint law differs from
p ⊗ p (so I(B;B′) > 0 and H(B′|B) < H(B′)). -/
theorem memory_not_product {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (a : ℝ) (ha : 0 < a)
    (b : ι) (hb0 : 0 < p b) (hb1 : p b < 1) :
    p b * (a * 1 + (1 - a) * p b) ≠ p b * p b := by
  intro h
  have : a * p b * (1 - p b) = 0 := by linear_combination h
  have : 0 < a * p b * (1 - p b) := by have := sub_pos.mpr hb1; positivity
  linarith

/-- C13-74: a continuous-additive pricing φ on [0, H] with values in [0,1] and φ(H) = 1 is L/H
(reduction to the Born additivity lemma). -/
theorem additive_pricing (φ : ℝ → ℝ) {H : ℝ} (hH : 0 < H) (hnn : ∀ L, 0 ≤ L → L ≤ H → 0 ≤ φ L)
    (hadd : ∀ L1 L2, 0 ≤ L1 → 0 ≤ L2 → L1 + L2 ≤ H → φ (L1 + L2) = φ L1 + φ L2) (h1 : φ H = 1)
    (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ H) : φ L = L / H := by
  have hF := Entropic.AppFG.Born.born (F := fun s => φ (s * H))
    (fun s hs0 hs1 => hnn _ (mul_nonneg hs0 hH.le) (by nlinarith))
    (fun s t hs ht hst => by
      show φ ((s + t) * H) = φ (s * H) + φ (t * H)
      rw [add_mul]; exact hadd _ _ (mul_nonneg hs hH.le) (mul_nonneg ht hH.le) (by nlinarith))
    (by show φ (1 * H) = 1; rw [one_mul, h1]) (L / H) (div_nonneg hL0 hH.le)
    (by rw [div_le_one hH]; exact hL1)
  have : φ (L / H * H) = L / H := hF
  rwa [div_mul_cancel₀ _ hH.ne'] at this

/-! ### Reset coefficient (C13-80, C13-81) and coarse-partition counterexample (C13-79) -/

/-- C13-80: with c(y) = min_A K(y|A) and e = Σc ∈ (0,1), K = e r + (1 − e)K̃ for r = c/e and
K̃ = (K − c)/(1 − e), both stochastic when K is. -/
theorem reset_decomposition {Y : Type*} [Fintype Y] (K c : Y → ℝ) (e : ℝ) (he0 : 0 < e) (he1 : e < 1)
    (hK : ∑ y, K y = 1) (hc : ∑ y, c y = e) (hcK : ∀ y, c y ≤ K y) :
    (∀ y, K y = e * (c y / e) + (1 - e) * ((K y - c y) / (1 - e))) ∧ ∑ y, c y / e = 1 ∧
      ∑ y, (K y - c y) / (1 - e) = 1 ∧ ∀ y, 0 ≤ (K y - c y) / (1 - e) := by
  have h1e : 1 - e ≠ 0 := by linarith
  refine ⟨fun y => by field_simp; ring, by rw [← Finset.sum_div, hc, div_self he0.ne'], ?_,
    fun y => div_nonneg (by linarith [hcK y]) (by linarith)⟩
  rw [← Finset.sum_div, Finset.sum_sub_distrib, hK, hc, div_self h1e]

/-- C13-81: post-processing cannot lower the reset coefficient: min_A Σ_y L(z|y)K(y|A) ≥ Σ_y L(z|y) c(y). -/
theorem reset_monotone {A Y : Type*} [Fintype Y] (L : Y → ℝ) (K : A → Y → ℝ) (c : Y → ℝ)
    (hL : ∀ y, 0 ≤ L y) (hc : ∀ a y, c y ≤ K a y) (a : A) :
    ∑ y, L y * c y ≤ ∑ y, L y * K a y :=
  Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hc a y) (hL y))

/-- C13-79: on ℤ/4 with labels (0,0,1,1) and bins {1,2},{3,4}, the bin either determines the label
(I = H(A), loss 0) or is independent of it (I = 0, loss 1): the joint tables are the deterministic
and the product tables. -/
theorem coarse_partition :
    let joint0 : Fin 2 → Fin 2 → ℝ := fun a b => if a = b then 1/2 else 0
    let joint1 : Fin 2 → Fin 2 → ℝ := fun _ _ => 1/4
    (∀ a b, joint1 a b = (∑ b', joint1 a b') * (∑ a', joint1 a' b)) ∧
      (∀ a, ∑ b, joint0 a b = 1/2) ∧ joint0 0 1 = 0 := by
  refine ⟨fun a b => by simp [Fin.sum_univ_two]; norm_num, fun a => by fin_cases a <;> simp [Fin.sum_univ_two],
    by simp⟩

/-! ### Virial time, isometries, label cap, clock deficit, formation energy (C13-83, -90, -93, -95, -98, -100) -/

/-- C13-83: M = (4π/3)Δρ_cR³, ρ_c = 3H²/(8πG), V² = GM/R give V² = ΔH²R²/2, i.e. R/V = 1/(H√(Δ/2)). -/
theorem virial_time {G H Δ R : ℝ} (hG : G ≠ 0) :
    G * ((4 * π / 3) * Δ * (3 * H ^ 2 / (8 * π * G)) * R ^ 3) / R = Δ * H ^ 2 * R ^ 2 / 2 ∨ R = 0 := by
  rcases eq_or_ne R 0 with h | h
  · right; exact h
  · left; have := Real.pi_pos; field_simp; ring

/-- C13-90, C13-95: S₀†S₀ = I − E, S†S = E and W_α†W_α = I give S₀†S₀ + (1/9)Σ_α(W_αS)†(W_αS) = I. -/
theorem release_isometry {n : Type*} [Fintype n] [DecidableEq n] (S0 S E : Matrix n n ℂ) (W : Fin 9 → Matrix n n ℂ)
    (h0 : S0ᴴ * S0 = 1 - E) (hS : Sᴴ * S = E) (hW : ∀ α, (W α)ᴴ * W α = 1) :
    S0ᴴ * S0 + (1/9 : ℂ) • ∑ α, (W α * S)ᴴ * (W α * S) = 1 := by
  have : ∀ α, (W α * S)ᴴ * (W α * S) = E := by
    intro α; rw [Matrix.conjTranspose_mul, show Sᴴ * (W α)ᴴ * (W α * S) = Sᴴ * ((W α)ᴴ * W α) * S by
      simp only [Matrix.mul_assoc], hW, Matrix.mul_one, hS]
  rw [Finset.sum_congr rfl (fun α _ => this α), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, h0]
  norm_num

/-- C13-93: switching a label flag a: 1 → 0 lowers the cap by M/ε and never raises it. -/
theorem label_cap (rest M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    rest + 0 * M / ε = rest + 1 * M / ε - M / ε ∧ rest + 0 * M / ε ≤ rest + 1 * M / ε := by
  constructor
  · ring
  · have : 0 ≤ M / ε := div_nonneg hM hε.le
    simp only [zero_mul, zero_div, one_mul, add_zero]; linarith

/-- C13-98: for future unit timelike u, v (u₀ = √(1 + |ū|²), v₀ = √(1 + |v̄|²)), γ = u₀v₀ − ū·v̄ ≥ 1. -/
theorem reverse_cauchy_schwarz (ub vb : Fin 3 → ℝ) :
    1 ≤ Real.sqrt (1 + ub ⬝ᵥ ub) * Real.sqrt (1 + vb ⬝ᵥ vb) - ub ⬝ᵥ vb := by
  have hu : 0 ≤ ub ⬝ᵥ ub := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hcs : (ub ⬝ᵥ vb) ^ 2 ≤ (ub ⬝ᵥ ub) * (vb ⬝ᵥ vb) := by
    simp only [dotProduct, Fin.sum_univ_three]
    nlinarith [sq_nonneg (ub 0 * vb 1 - ub 1 * vb 0), sq_nonneg (ub 0 * vb 2 - ub 2 * vb 0),
      sq_nonneg (ub 1 * vb 2 - ub 2 * vb 1)]
  have hd : 0 ≤ ub ⬝ᵥ ub + vb ⬝ᵥ vb - 2 * ub ⬝ᵥ vb := by
    simp only [dotProduct, Fin.sum_univ_three]
    nlinarith [sq_nonneg (ub 0 - vb 0), sq_nonneg (ub 1 - vb 1), sq_nonneg (ub 2 - vb 2)]
  rw [← Real.sqrt_mul (by linarith)]
  have key : (1 + ub ⬝ᵥ vb) ^ 2 ≤ (1 + ub ⬝ᵥ ub) * (1 + vb ⬝ᵥ vb) := by nlinarith
  have := Real.abs_le_sqrt key
  linarith [le_abs_self (1 + ub ⬝ᵥ vb)]

/-- C13-98 (deficit growth): dΔ/dτ = γ/τ* − dN/dτ ≥ (γ − 1)/τ* ≥ 0 when dN/dτ ≤ 1/τ* and γ ≥ 1. -/
theorem deficit_rate {γ τ dN : ℝ} (hτ : 0 < τ) (hγ : 1 ≤ γ) (hN : dN ≤ 1 / τ) :
    (γ - 1) / τ ≤ γ / τ - dN ∧ 0 ≤ (γ - 1) / τ := by
  refine ⟨?_, div_nonneg (by linarith) hτ.le⟩
  have : (γ - 1) / τ = γ / τ - 1 / τ := by ring
  linarith

/-- C13-98 (persistence): a deficit with nonnegative derivative that is positive at τ₀ stays positive. -/
theorem deficit_persists (Δ Δ' : ℝ → ℝ) (hd : ∀ t, HasDerivAt Δ (Δ' t) t) (hnn : ∀ t, 0 ≤ Δ' t)
    {t0 : ℝ} (h0 : 0 < Δ t0) : ∀ t, t0 ≤ t → 0 < Δ t := by
  have hm : Monotone Δ := monotone_of_deriv_nonneg (fun t => (hd t).differentiableAt)
    (fun t => by rw [(hd t).deriv]; exact hnn t)
  exact fun t ht => lt_of_lt_of_le h0 (hm ht)

/-- C13-99 (invariant part): if every allowed step preserves n_∅ = 0 and does not raise the committed
stock c, then any finite sequence of allowed steps from a state with n_∅ = 0 keeps n_∅ = 0 and c
nonincreasing. -/
theorem no_late_recruitment {S : Type*} (n0 : S → ℕ) (c : S → ℝ) (Allowed : (S → S) → Prop)
    (hstep : ∀ f, Allowed f → ∀ x, n0 x = 0 → n0 (f x) = 0 ∧ c (f x) ≤ c x) :
    ∀ (L : List (S → S)), (∀ f ∈ L, Allowed f) → ∀ x, n0 x = 0 →
      n0 (L.foldl (fun y f => f y) x) = 0 ∧ c (L.foldl (fun y f => f y) x) ≤ c x := by
  intro L
  induction L with
  | nil => intro _ x hx; exact ⟨hx, le_rfl⟩
  | cons f L ih =>
    intro hL x hx
    obtain ⟨h1, h2⟩ := hstep f (hL f List.mem_cons_self) x hx
    obtain ⟨h3, h4⟩ := ih (fun g hg => hL g (List.mem_cons_of_mem _ hg)) (f x) h1
    exact ⟨h3, le_trans h4 h2⟩

/-- C13-100: m_pc²/ε with ε = g/(4π²) at the closure root lies in (4.99, 5.00) GeV
(m_pc² = 0.938272 GeV). -/
theorem formation_energy {η : ℝ} (h : Entropic.FiniteModel.ClosureStationary η) :
    4.99 < 0.938272 / (Entropic.ClosureRoot.gshare η / (4 * π ^ 2)) ∧
      0.938272 / (Entropic.ClosureRoot.gshare η / (4 * π ^ 2)) < 5.00 := by
  obtain ⟨e1, e2⟩ := Entropic.Spine.epsilon_bracket h
  have hp : 0 < Entropic.ClosureRoot.gshare η / (4 * π ^ 2) := by linarith
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

end Entropic.AppO
