import Entropic.Pass2.Var

/-! Second pass, chunk 16: Euler–Lagrange equations of the reduced actions.

`quadLag` is the density s(x) u + Σᵢ wᵢ(x) pᵢ + k |p|² + r(x); `qLag` is Σᵢ wᵢ(x) pᵢ + K Q(|p|²/a₀²) + r(x)
with Q ∈ C². The two-potential action (C11-54, C01-44), the Newton action (C11-57), the static scalar
action (C01-47) and the QUMOND-type carrier action (C02-11, C12-02) are of these forms in each of their
fields; their stationarity under all test variations is equivalent to the stated field equations. -/

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Entropic.Var

variable {n : ℕ}

theorem pd_add {f g : E n → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (i : Fin n) (x : E n) :
    pd (fun y => f y + g y) i x = pd f i x + pd g i x := by
  unfold pd; rw [fderiv_fun_add (hf x) (hg x)]; rfl

theorem pd_sub {f g : E n → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (i : Fin n) (x : E n) :
    pd (fun y => f y - g y) i x = pd f i x - pd g i x := by
  unfold pd; rw [fderiv_fun_sub (hf x) (hg x)]; rfl

theorem pd_const_mul {f : E n → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (i : Fin n) (x : E n) :
    pd (fun y => c * f y) i x = c * pd f i x := by
  simp [pd, fderiv_const_mul (hf x)]

theorem pd_mul {f g : E n → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (i : Fin n) (x : E n) :
    pd (fun y => f y * g y) i x = pd f i x * g x + f x * pd g i x := by
  unfold pd; rw [fderiv_fun_mul (hf x) (hg x)]; simp [smul_eq_mul]; ring

theorem pd_const (c : ℝ) (i : Fin n) (x : E n) : pd (fun _ => c) i x = 0 := by simp [pd]

theorem pd_const_fun (c : ℝ) (i : Fin n) : pd (fun _ : E n => c) i = fun _ => 0 := funext (pd_const c i)

theorem dvg_zero (x : E n) : dvg (fun _ _ => (0:ℝ)) x = 0 := by simp [dvg, pd_const]

/-- grad (f + ε g) = grad f + ε grad g. -/
theorem grad_add_smul {f g : E n → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (ε : ℝ) (x : E n) :
    grad (fun y => f y + ε * g y) x = grad f x + ε • grad g x := by
  funext i
  simp only [grad, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [pd_add hf (hg.const_mul ε), pd_const_mul hg]

theorem c1_of_c2 {f : E n → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 f := hf.of_le (by norm_num)

theorem diff_of_c1 {f : E n → ℝ} (hf : ContDiff ℝ 1 f) : Differentiable ℝ f := hf.differentiable one_ne_zero

theorem pd_c1 {f : E n → ℝ} (hf : ContDiff ℝ 2 f) (i : Fin n) : ContDiff ℝ 1 (pd f i) :=
  pd_contDiff (m := 1) hf i

/-! ### The quadratic family -/

/-- L(x, u, p) = s(x) u + Σᵢ wᵢ(x) pᵢ + k |p|² + r(x). -/
noncomputable def quadLag (s : E n → ℝ) (w : Fin n → E n → ℝ) (k : ℝ) (r : E n → ℝ) (hs : Continuous s)
    (hw : ∀ i, Continuous (w i)) (hr : Continuous r) : Lag n where
  L x u p := s x * u + ∑ i, w i x * p i + k * ∑ i, p i ^ 2 + r x
  Lu x _ _ := s x
  Lp i x _ p := w i x + 2 * k * p i
  line x u p a b := by
    have h1 : HasDerivAt (fun ε : ℝ => s x * (u + ε * a)) (s x * a) 0 := by
      have := (((hasDerivAt_id (0:ℝ)).mul_const a).const_add u).const_mul (s x)
      simpa using this
    have h2 : HasDerivAt (fun ε : ℝ => ∑ i, w i x * (p + ε • b) i) (∑ i, w i x * b i) 0 := by
      refine HasDerivAt.fun_sum fun i _ => ?_
      have := (((hasDerivAt_id (0:ℝ)).mul_const (b i)).const_add (p i)).const_mul (w i x)
      simpa using this
    have h3 : HasDerivAt (fun ε : ℝ => k * ∑ i, (p + ε • b) i ^ 2) (k * ∑ i, 2 * p i * b i) 0 := by
      refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun i _ => ?_)
      have := (((hasDerivAt_id (0:ℝ)).mul_const (b i)).const_add (p i)).fun_pow 2
      convert this using 1
      · funext ε; simp
      · simp <;> ring
    have h := ((h1.add h2).add h3).add_const (r x)
    convert h using 1
    rw [show ∑ i, (w i x + 2 * k * p i) * b i = ∑ i, w i x * b i + k * ∑ i, 2 * p i * b i by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring]
    ring
  cont := by
    have : ∀ i, Continuous fun z : E n × ℝ × (Fin n → ℝ) => w i z.1 * z.2.2 i := fun i =>
      ((hw i).comp continuous_fst).mul ((continuous_apply i).comp (continuous_snd.comp continuous_snd))
    exact (((hs.comp continuous_fst).mul (continuous_fst.comp continuous_snd)).add
      (continuous_finsetSum _ fun i _ => this i)).add
      (continuous_const.mul (continuous_finsetSum _ fun i _ =>
        ((continuous_apply i).comp (continuous_snd.comp continuous_snd)).pow 2)) |>.add (hr.comp continuous_fst)
  cont_u := hs.comp continuous_fst
  cont_p i := ((hw i).comp continuous_fst).add
    (continuous_const.mul ((continuous_apply i).comp (continuous_snd.comp continuous_snd)))

/-- Euler–Lagrange equation of the quadratic family: s = div w + 2k Δu. -/
theorem quad_EL (s : E n → ℝ) (w : Fin n → E n → ℝ) (k : ℝ) (r : E n → ℝ) (hs : Continuous s)
    (hw : ∀ i, ContDiff ℝ 1 (w i)) (hr : Continuous r) {u : E n → ℝ} (hu : ContDiff ℝ 2 u) :
    (∀ η, IsTest η → HasDerivAt (dA (quadLag s w k r hs (fun i => (hw i).continuous) hr) u η) 0 0) ↔
      ∀ x, s x = dvg w x + 2 * k * lap u x := by
  have hV : ∀ i, ContDiff ℝ 1 fun y =>
      (quadLag s w k r hs (fun i => (hw i).continuous) hr).Lp i y (u y) (grad u y) := fun i =>
    (hw i).add (contDiff_const.mul (pd_c1 hu i))
  rw [euler_lagrange _ (c1_of_c2 hu) hV]
  refine forall_congr' fun x => ?_
  have e : dvg (fun i y => (quadLag s w k r hs (fun i => (hw i).continuous) hr).Lp i y (u y) (grad u y)) x =
      dvg w x + 2 * k * lap u x := by
    simp only [dvg, lap, quadLag, grad, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pd_add (diff_of_c1 (hw i)) ((diff_of_c1 (pd_c1 hu i)).const_mul _),
      pd_const_mul (diff_of_c1 (pd_c1 hu i))]
  rw [e]; rfl

/-! ### Linearity of div and Δ -/

theorem dvg_congr {V W : Fin n → E n → ℝ} (h : ∀ i y, V i y = W i y) (x : E n) : dvg V x = dvg W x := by
  have : V = W := funext fun i => funext fun y => h i y
  rw [this]

theorem dvg_lin (α β : ℝ) {A B : Fin n → E n → ℝ} (hA : ∀ i, Differentiable ℝ (A i))
    (hB : ∀ i, Differentiable ℝ (B i)) (x : E n) :
    dvg (fun i y => α * A i y + β * B i y) x = α * dvg A x + β * dvg B x := by
  simp only [dvg, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pd_add ((hA i).const_mul α) ((hB i).const_mul β), pd_const_mul (hA i), pd_const_mul (hB i)]

theorem dvg_smul (α : ℝ) {A : Fin n → E n → ℝ} (hA : ∀ i, Differentiable ℝ (A i)) (x : E n) :
    dvg (fun i y => α * A i y) x = α * dvg A x := by
  simp only [dvg, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => pd_const_mul (hA i) α i x

theorem lap_sub {f g : E n → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E n) :
    lap (fun y => f y - g y) x = lap f x - lap g x := by
  have e : ∀ i, pd (fun y => f y - g y) i = fun y => pd f i y - pd g i y := fun i => funext fun y =>
    pd_sub (diff_of_c1 (c1_of_c2 hf)) (diff_of_c1 (c1_of_c2 hg)) i y
  simp only [lap, dvg, e, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => pd_sub (diff_of_c1 (pd_c1 hf i)) (diff_of_c1 (pd_c1 hg i)) i x

theorem lap_const_sub (C : ℝ) {f : E n → ℝ} (hf : ContDiff ℝ 2 f) (x : E n) :
    lap (fun y => C - f y) x = -lap f x := by
  rw [lap_sub contDiff_const hf]
  simp [lap, dvg, pd_const_fun, pd_const]

/-! ### Variations of action densities -/

/-- Variation of an action density D in its field: ∫ [D(u + εη) − D(u)]. -/
noncomputable def var (D : (E n → ℝ) → E n → ℝ) (u η : E n → ℝ) (ε : ℝ) : ℝ :=
  ∫ x, (D (fun y => u y + ε * η y) x - D u x)

theorem var_eq (Λ : Lag n) (D : (E n → ℝ) → E n → ℝ)
    (hD : ∀ f, Differentiable ℝ f → ∀ x, D f x = Λ.L x (f x) (grad f x)) {u η : E n → ℝ}
    (hu : Differentiable ℝ u) (hη : Differentiable ℝ η) : var D u η = dA Λ u η := by
  funext ε; unfold var dA; congr 1; funext x
  rw [hD (fun y => u y + ε * η y) (hu.add (hη.const_mul ε)), hD u hu, grad_add_smul hu hη]

theorem stationary_iff (Λ : Lag n) (D : (E n → ℝ) → E n → ℝ)
    (hD : ∀ f, Differentiable ℝ f → ∀ x, D f x = Λ.L x (f x) (grad f x)) {u : E n → ℝ}
    (hu : ContDiff ℝ 1 u) :
    (∀ η, IsTest η → HasDerivAt (var D u η) 0 0) ↔ ∀ η, IsTest η → HasDerivAt (dA Λ u η) 0 0 :=
  forall_congr' fun η => imp_congr_right fun hη => by
    rw [var_eq Λ D hD (diff_of_c1 hu) (diff_of_c1 hη.c1)]

theorem sum_pd_mul (A B : Fin n → ℝ) (c : ℝ) : ∑ i, c * A i * B i = c * ∑ i, B i * A i := by
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

theorem sum_pd_mul' (A B : Fin n → ℝ) (c : ℝ) : ∑ i, c * A i * B i = c * ∑ i, A i * B i := by
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

theorem eight_pi_ne {G : ℝ} (hG : G ≠ 0) : 8 * Real.pi * G ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hG

/-- −ρ = −(2/(8πG)) L ⟺ L = 4πGρ. -/
theorem poisson_iff {G : ℝ} (hG : G ≠ 0) (r L L' : ℝ) :
    -r = -(2 / (8 * Real.pi * G)) * L + 2 * 0 * L' ↔ L = 4 * Real.pi * G * r := by
  have h := eight_pi_ne hG
  rw [mul_zero, zero_mul, add_zero]
  constructor
  · intro e; field_simp at e; linarith
  · intro e; rw [e]; field_simp; ring

/-! ### C11-54, C11-55, C01-45: the reduced two-potential action -/

/-- The reduced two-potential density (C11-54, C01-44): (|∇Ψ|² − 2∇Φ·∇Ψ)/(8πG) − ρΦ. -/
noncomputable def I2 (G : ℝ) (ρ Φ Ψ : E n → ℝ) (x : E n) : ℝ :=
  (∑ i, pd Ψ i x ^ 2 - 2 * ∑ i, pd Φ i x * pd Ψ i x) / (8 * Real.pi * G) - ρ x * Φ x

/-- C11-55, C01-45 (first equation): stationarity in Φ under all test variations ⟺ ΔΨ = 4πGρ. -/
theorem two_potential_Φ {G : ℝ} (hG : G ≠ 0) {ρ Φ Ψ : E n → ℝ} (hρ : Continuous ρ) (hΦ : ContDiff ℝ 2 Φ)
    (hΨ : ContDiff ℝ 2 Ψ) :
    (∀ η, IsTest η → HasDerivAt (var (fun f => I2 G ρ f Ψ) Φ η) 0 0) ↔
      ∀ x, lap Ψ x = 4 * Real.pi * G * ρ x := by
  have hw : ∀ i, ContDiff ℝ 1 fun y => -(2 / (8 * Real.pi * G)) * pd Ψ i y := fun i =>
    contDiff_const.mul (pd_c1 hΨ i)
  have hr : Continuous fun y => (∑ i, pd Ψ i y ^ 2) / (8 * Real.pi * G) :=
    (continuous_finsetSum _ fun i _ => (pd_continuous (c1_of_c2 hΨ) i).pow 2).div_const _
  refine (stationary_iff (quadLag (fun y => -ρ y) (fun i y => -(2 / (8 * Real.pi * G)) * pd Ψ i y) 0
      (fun y => (∑ i, pd Ψ i y ^ 2) / (8 * Real.pi * G)) hρ.neg (fun i => (hw i).continuous) hr) _
      (fun f _ x => by
        simp only [I2, quadLag, grad]
        rw [sum_pd_mul]; ring) (c1_of_c2 hΦ)).trans ((quad_EL _ _ _ _ hρ.neg hw hr hΦ).trans ?_)
  refine forall_congr' fun x => ?_
  rw [dvg_smul _ (fun i => diff_of_c1 (pd_c1 hΨ i))]
  exact poisson_iff hG _ _ _

/-- C11-55, C01-45 (second equation): stationarity in Ψ under all test variations ⟺ Δ(Φ − Ψ) = 0. -/
theorem two_potential_Ψ {G : ℝ} (hG : G ≠ 0) {ρ Φ Ψ : E n → ℝ} (hρ : Continuous ρ) (hΦ : ContDiff ℝ 2 Φ)
    (hΨ : ContDiff ℝ 2 Ψ) :
    (∀ η, IsTest η → HasDerivAt (var (fun f => I2 G ρ Φ f) Ψ η) 0 0) ↔
      ∀ x, lap (fun y => Φ y - Ψ y) x = 0 := by
  have hw : ∀ i, ContDiff ℝ 1 fun y => -(2 / (8 * Real.pi * G)) * pd Φ i y := fun i =>
    contDiff_const.mul (pd_c1 hΦ i)
  have hr : Continuous fun y => -ρ y * Φ y := hρ.neg.mul hΦ.continuous
  refine (stationary_iff (quadLag (fun _ => 0) (fun i y => -(2 / (8 * Real.pi * G)) * pd Φ i y)
      (1 / (8 * Real.pi * G)) (fun y => -ρ y * Φ y) continuous_const (fun i => (hw i).continuous) hr) _
      (fun f _ x => by
        simp only [I2, quadLag, grad]
        rw [sum_pd_mul']; ring) (c1_of_c2 hΨ)).trans ((quad_EL _ _ _ _ continuous_const hw hr hΨ).trans ?_)
  refine forall_congr' fun x => ?_
  rw [dvg_smul _ (fun i => diff_of_c1 (pd_c1 hΦ i)), lap_sub hΦ hΨ]
  have h := eight_pi_ne hG
  have hc : (8 * Real.pi * G)⁻¹ ≠ 0 := inv_ne_zero h
  simp only [lap] at *
  constructor
  · intro e
    have : (8 * Real.pi * G)⁻¹ * (dvg (pd Φ) x - dvg (pd Ψ) x) = 0 := by linear_combination (1 / 2 : ℝ) * e
    exact (mul_eq_zero.1 this).resolve_left hc
  · intro e
    linear_combination (2 / (8 * Real.pi * G)) * e

/-! ### C11-57, C11-58: the Newton action -/

/-- The Newton density −|∇Φ|²/(8πG) − ρΦ. -/
noncomputable def IN (G : ℝ) (ρ Φ : E n → ℝ) (x : E n) : ℝ :=
  -(∑ i, pd Φ i x ^ 2) / (8 * Real.pi * G) - ρ x * Φ x

/-- C11-57 (substitution): I^(2)[Φ, Φ] = I_Newton[Φ] pointwise. -/
theorem I2_diag (G : ℝ) (ρ Φ : E n → ℝ) (x : E n) : I2 G ρ Φ Φ x = IN G ρ Φ x := by
  simp only [I2, IN, ← sq]; ring

/-- C11-57: the Euler–Lagrange equation of the Newton action is ΔΦ = 4πGρ. -/
theorem newton_EL {G : ℝ} (hG : G ≠ 0) {ρ Φ : E n → ℝ} (hρ : Continuous ρ) (hΦ : ContDiff ℝ 2 Φ) :
    (∀ η, IsTest η → HasDerivAt (var (IN G ρ) Φ η) 0 0) ↔ ∀ x, lap Φ x = 4 * Real.pi * G * ρ x := by
  refine (stationary_iff (quadLag (fun y => -ρ y) (fun _ _ => 0) (-1 / (8 * Real.pi * G)) (fun _ => 0) hρ.neg
      (fun _ => continuous_const) continuous_const) _ (fun f _ x => by simp [IN, quadLag, grad]; ring)
      (c1_of_c2 hΦ)).trans ((quad_EL _ _ _ _ hρ.neg (fun _ => contDiff_const) continuous_const hΦ).trans ?_)
  refine forall_congr' fun x => ?_
  rw [dvg_zero, zero_add]
  have h := eight_pi_ne hG
  simp only [Pi.neg_apply]
  constructor
  · intro e; field_simp at e; linarith
  · intro e; rw [e]; field_simp; ring

/-- C11-58: varying I^(2)[Φ, Φ] in the single field Φ gives the one equation ΔΦ = 4πGρ, while independent
variation of I^(2)[Φ, Ψ] gives the two equations ΔΨ = 4πGρ and Δ(Φ − Ψ) = 0. -/
theorem identification_before_variation {G : ℝ} (hG : G ≠ 0) {ρ Φ Ψ : E n → ℝ} (hρ : Continuous ρ)
    (hΦ : ContDiff ℝ 2 Φ) (hΨ : ContDiff ℝ 2 Ψ) :
    ((∀ η, IsTest η → HasDerivAt (var (fun f => I2 G ρ f f) Φ η) 0 0) ↔
        ∀ x, lap Φ x = 4 * Real.pi * G * ρ x) ∧
      ((∀ η, IsTest η → HasDerivAt (var (fun f => I2 G ρ f Ψ) Φ η) 0 0) ∧
          (∀ η, IsTest η → HasDerivAt (var (fun f => I2 G ρ Φ f) Ψ η) 0 0) ↔
        (∀ x, lap Ψ x = 4 * Real.pi * G * ρ x) ∧ ∀ x, lap (fun y => Φ y - Ψ y) x = 0) := by
  refine ⟨?_, and_congr (two_potential_Φ hG hρ hΦ hΨ) (two_potential_Ψ hG hρ hΦ hΨ)⟩
  have : (fun f => I2 G ρ f f) = IN G ρ := funext fun f => funext fun x => I2_diag G ρ f x
  rw [this]; exact newton_EL hG hρ hΦ

/-! ### C01-47: the static scalar action -/

/-- The static density −(γ/2)|∇S|² − (λ + κχ) S. -/
noncomputable def Iscal (γ lam κ : ℝ) (χ S : E n → ℝ) (x : E n) : ℝ :=
  -(γ / 2) * ∑ i, pd S i x ^ 2 - (lam + κ * χ x) * S x

/-- C01-47 (static case): stationarity ⟺ γ ΔS = λ + κχ. -/
theorem scalar_EL (γ lam κ : ℝ) {χ S : E n → ℝ} (hχ : Continuous χ) (hS : ContDiff ℝ 2 S) :
    (∀ η, IsTest η → HasDerivAt (var (Iscal γ lam κ χ) S η) 0 0) ↔ ∀ x, γ * lap S x = lam + κ * χ x := by
  have hs : Continuous fun y => -(lam + κ * χ y) := (continuous_const.add (continuous_const.mul hχ)).neg
  refine (stationary_iff (quadLag (fun y => -(lam + κ * χ y)) (fun _ _ => 0) (-(γ / 2)) (fun _ => 0) hs
      (fun _ => continuous_const) continuous_const) _ (fun f _ x => by simp [Iscal, quadLag, grad]; ring)
      (c1_of_c2 hS)).trans ((quad_EL _ _ _ _ hs (fun _ => contDiff_const) continuous_const hS).trans ?_)
  refine forall_congr' fun x => ?_
  rw [dvg_zero, zero_add]
  constructor <;> intro e <;> linarith

/-- C01-47 (renormalized static form): with λ = 0, χ = ρ and S = S_∞ − δS, γΔS = κρ ⟺ ΔδS = −(κ/γ)ρ. -/
theorem scalar_static (γ κ Sinf : ℝ) (hγ : γ ≠ 0) {ρ δS : E n → ℝ} (hδ : ContDiff ℝ 2 δS) (x : E n) :
    γ * lap (fun y => Sinf - δS y) x = 0 + κ * ρ x ↔ lap δS x = -(κ / γ) * ρ x := by
  rw [lap_const_sub Sinf hδ, zero_add]
  constructor
  · intro e; field_simp; linarith
  · intro e; rw [e]; field_simp

/-! ### C02-11, C12-02, C02-12: the QUMOND-type carrier action -/

/-- L(x, u, p) = Σᵢ wᵢ(x) pᵢ + K Q(|p|²/a₀²) + r(x), Q ∈ C¹. -/
noncomputable def qLag (w : Fin n → E n → ℝ) (K a0 : ℝ) (Q : ℝ → ℝ) (hQ : ContDiff ℝ 1 Q) (r : E n → ℝ)
    (hw : ∀ i, Continuous (w i)) (hr : Continuous r) : Lag n where
  L x _ p := ∑ i, w i x * p i + K * Q ((∑ i, p i ^ 2) / a0 ^ 2) + r x
  Lu _ _ _ := 0
  Lp i x _ p := w i x + K * deriv Q ((∑ j, p j ^ 2) / a0 ^ 2) * (2 * p i / a0 ^ 2)
  line x u p a b := by
    have h2 : HasDerivAt (fun ε : ℝ => ∑ i, w i x * (p + ε • b) i) (∑ i, w i x * b i) 0 := by
      refine HasDerivAt.fun_sum fun i _ => ?_
      have := (((hasDerivAt_id (0:ℝ)).mul_const (b i)).const_add (p i)).const_mul (w i x)
      simpa using this
    have hz : HasDerivAt (fun ε : ℝ => (∑ i, (p + ε • b) i ^ 2) / a0 ^ 2) ((∑ i, 2 * p i * b i) / a0 ^ 2) 0 := by
      refine HasDerivAt.div_const (HasDerivAt.fun_sum fun i _ => ?_) _
      have := (((hasDerivAt_id (0:ℝ)).mul_const (b i)).const_add (p i)).fun_pow 2
      convert this using 1
      · funext ε; simp
      · simp <;> ring
    have hQd : HasDerivAt Q (deriv Q ((∑ i, p i ^ 2) / a0 ^ 2)) ((∑ i, (p + (0:ℝ) • b) i ^ 2) / a0 ^ 2) := by
      simpa using ((hQ.differentiable one_ne_zero) ((∑ i, p i ^ 2) / a0 ^ 2)).hasDerivAt
    have h3 := (hQd.comp (0:ℝ) hz).const_mul K
    have h := ((h2.add h3).add_const (r x))
    refine HasDerivAt.congr_deriv h ?_
    simp only [zero_smul, add_zero, zero_mul, zero_add]
    rw [show ∑ i, (w i x + K * deriv Q ((∑ j, p j ^ 2) / a0 ^ 2) * (2 * p i / a0 ^ 2)) * b i =
        ∑ i, w i x * b i + K * (deriv Q ((∑ i, p i ^ 2) / a0 ^ 2) * ((∑ i, 2 * p i * b i) / a0 ^ 2)) by
      rw [Finset.sum_div _ (fun i => 2 * p i * b i), Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring]
  cont := by
    have hp : ∀ i, Continuous fun z : E n × ℝ × (Fin n → ℝ) => z.2.2 i := fun i =>
      (continuous_apply i).comp (continuous_snd.comp continuous_snd)
    exact ((continuous_finsetSum _ fun i _ => ((hw i).comp continuous_fst).mul (hp i)).add
      (continuous_const.mul (hQ.continuous.comp ((continuous_finsetSum _ fun i _ => (hp i).pow 2).div_const _)))).add
      (hr.comp continuous_fst)
  cont_u := continuous_const
  cont_p i := by
    have hp : ∀ i, Continuous fun z : E n × ℝ × (Fin n → ℝ) => z.2.2 i := fun i =>
      (continuous_apply i).comp (continuous_snd.comp continuous_snd)
    exact ((hw i).comp continuous_fst).add ((continuous_const.mul ((hQ.continuous_deriv le_rfl).comp
      ((continuous_finsetSum _ fun j _ => (hp j).pow 2).div_const _))).mul
      ((continuous_const.mul (hp i)).div_const _))

/-- z_b = |∇Φ_b|²/a₀². -/
noncomputable def zb (a0 : ℝ) (Φb : E n → ℝ) (y : E n) : ℝ := (∑ j, pd Φb j y ^ 2) / a0 ^ 2


/-- The carrier density (C02-11, C12-02): −{[2∇Φ·∇Φ_b − a₀² Q(z)]/(8πG) + ρΦ}, z = |∇Φ_b|²/a₀². -/
noncomputable def Icar (G a0 : ℝ) (Q : ℝ → ℝ) (ρ Φ Φb : E n → ℝ) (x : E n) : ℝ :=
  -((2 * ∑ i, pd Φ i x * pd Φb i x - a0 ^ 2 * Q (zb a0 Φb x)) / (8 * Real.pi * G) + ρ x * Φ x)

theorem zb_continuous (a0 : ℝ) {Φb : E n → ℝ} (h : ContDiff ℝ 1 Φb) : Continuous (zb a0 Φb) :=
  (continuous_finsetSum _ fun j _ => (pd_continuous h j).pow 2).div_const _

theorem zb_c1 (a0 : ℝ) {Φb : E n → ℝ} (h : ContDiff ℝ 2 Φb) : ContDiff ℝ 1 (zb a0 Φb) := by
  unfold zb
  exact (ContDiff.sum fun j _ => (pd_c1 h j).pow 2).div_const _

/-- C02-11, C12-02 (i): stationarity of the carrier action in Φ ⟺ ΔΦ_b = 4πGρ. -/
theorem carrier_Φ {G a0 : ℝ} (hG : G ≠ 0) {Q : ℝ → ℝ} (hQ : Continuous Q) {ρ Φ Φb : E n → ℝ}
    (hρ : Continuous ρ) (hΦ : ContDiff ℝ 2 Φ) (hΦb : ContDiff ℝ 2 Φb) :
    (∀ η, IsTest η → HasDerivAt (var (fun f => Icar G a0 Q ρ f Φb) Φ η) 0 0) ↔
      ∀ x, lap Φb x = 4 * Real.pi * G * ρ x := by
  have hw : ∀ i, ContDiff ℝ 1 fun y => -(2 / (8 * Real.pi * G)) * pd Φb i y := fun i =>
    contDiff_const.mul (pd_c1 hΦb i)
  have hr : Continuous fun y => a0 ^ 2 * Q (zb a0 Φb y) / (8 * Real.pi * G) :=
    (continuous_const.mul (hQ.comp (zb_continuous a0 (c1_of_c2 hΦb)))).div_const _
  refine (stationary_iff (quadLag (fun y => -ρ y) (fun i y => -(2 / (8 * Real.pi * G)) * pd Φb i y) 0
      (fun y => a0 ^ 2 * Q (zb a0 Φb y) / (8 * Real.pi * G)) hρ.neg (fun i => (hw i).continuous) hr) _
      (fun f _ x => by
        simp only [Icar, quadLag, grad]
        rw [sum_pd_mul]; ring) (c1_of_c2 hΦ)).trans ((quad_EL _ _ _ _ hρ.neg hw hr hΦ).trans ?_)
  refine forall_congr' fun x => ?_
  rw [dvg_smul _ (fun i => diff_of_c1 (pd_c1 hΦb i))]
  exact poisson_iff hG _ _ _

/-- C02-11, C12-02 (ii): stationarity of the carrier action in Φ_b ⟺ ΔΦ = div[Q'(z)∇Φ_b] (Q ∈ C²). -/
theorem carrier_Φb {G a0 : ℝ} (hG : G ≠ 0) (ha : a0 ≠ 0) {Q : ℝ → ℝ} (hQ : ContDiff ℝ 2 Q)
    {ρ Φ Φb : E n → ℝ} (hρ : Continuous ρ) (hΦ : ContDiff ℝ 2 Φ) (hΦb : ContDiff ℝ 2 Φb) :
    (∀ η, IsTest η → HasDerivAt (var (fun f => Icar G a0 Q ρ Φ f) Φb η) 0 0) ↔
      ∀ x, lap Φ x = dvg (fun i y => deriv Q (zb a0 Φb y) * pd Φb i y) x := by
  have hQ1 : ContDiff ℝ 1 Q := hQ.of_le (by norm_num)
  have hdQ : ContDiff ℝ 1 (deriv Q) := (contDiff_succ_iff_deriv.1 hQ).2.2
  have hw : ∀ i, Continuous fun y => -(2 / (8 * Real.pi * G)) * pd Φ i y := fun i =>
    continuous_const.mul (pd_continuous (c1_of_c2 hΦ) i)
  have hr : Continuous fun y => -ρ y * Φ y := hρ.neg.mul hΦ.continuous
  set Λ := qLag (fun i y => -(2 / (8 * Real.pi * G)) * pd Φ i y) (a0 ^ 2 / (8 * Real.pi * G)) a0 Q hQ1
    (fun y => -ρ y * Φ y) hw hr with hΛ
  have hD : ∀ f : E n → ℝ, Differentiable ℝ f → ∀ x, Icar G a0 Q ρ Φ f x = Λ.L x (f x) (grad f x) := by
    intro f _ x
    simp only [hΛ, Icar, qLag, grad, zb]
    rw [sum_pd_mul']; ring
  have hB : ∀ i, ContDiff ℝ 1 fun y => deriv Q (zb a0 Φb y) * pd Φb i y := fun i =>
    (hdQ.comp (zb_c1 a0 hΦb)).mul (pd_c1 hΦb i)
  have hLp : ∀ i y, Λ.Lp i y (Φb y) (grad Φb y) =
      -(2 / (8 * Real.pi * G)) * pd Φ i y + (2 / (8 * Real.pi * G)) * (deriv Q (zb a0 Φb y) * pd Φb i y) := by
    intro i y
    simp only [hΛ, qLag, grad, zb]
    field_simp
  have hV : ∀ i, ContDiff ℝ 1 fun y => Λ.Lp i y (Φb y) (grad Φb y) := fun i => by
    have : (fun y => Λ.Lp i y (Φb y) (grad Φb y)) = fun y =>
        -(2 / (8 * Real.pi * G)) * pd Φ i y + (2 / (8 * Real.pi * G)) * (deriv Q (zb a0 Φb y) * pd Φb i y) :=
      funext (hLp i)
    rw [this]; exact (contDiff_const.mul (pd_c1 hΦ i)).add (contDiff_const.mul (hB i))
  rw [stationary_iff Λ _ hD (c1_of_c2 hΦb), euler_lagrange Λ (c1_of_c2 hΦb) hV]
  refine forall_congr' fun x => ?_
  rw [dvg_congr hLp, dvg_lin _ _ (fun i => diff_of_c1 (pd_c1 hΦ i)) (fun i => diff_of_c1 (hB i))]
  have h := eight_pi_ne hG
  have hc : (8 * Real.pi * G)⁻¹ ≠ 0 := inv_ne_zero h
  show (0:ℝ) = _ ↔ _
  constructor
  · intro e
    have : (8 * Real.pi * G)⁻¹ * (lap Φ x - dvg (fun i y => deriv Q (zb a0 Φb y) * pd Φb i y) x) = 0 := by
      simp only [lap] at e ⊢; linear_combination (1 / 2 : ℝ) * e
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hc)
  · intro e
    simp only [lap] at e ⊢
    linear_combination (2 / (8 * Real.pi * G)) * e

/-- C02-12: if both carrier equations hold, then φ_⊥ = Φ − Φ_b obeys Δφ_⊥ = div[(Q'(z) − 1)∇Φ_b]. For the
manuscript's Q = z + Q_⊥ one has Q' − 1 = Q_⊥' = n_B(z^{1/4}) for z > 0 (`Main.Galactic.Qperp_deriv`). -/
theorem carrier_excess {a0 : ℝ} {Q : ℝ → ℝ} (hQ : ContDiff ℝ 2 Q) {Φ Φb : E n → ℝ} (hΦ : ContDiff ℝ 2 Φ)
    (hΦb : ContDiff ℝ 2 Φb) (h : ∀ x, lap Φ x = dvg (fun i y => deriv Q (zb a0 Φb y) * pd Φb i y) x) (x : E n) :
    lap (fun y => Φ y - Φb y) x = dvg (fun i y => (deriv Q (zb a0 Φb y) - 1) * pd Φb i y) x := by
  have hdQ : ContDiff ℝ 1 (deriv Q) := (contDiff_succ_iff_deriv.1 hQ).2.2
  have hB : ∀ i, Differentiable ℝ fun y => deriv Q (zb a0 Φb y) * pd Φb i y := fun i =>
    diff_of_c1 ((hdQ.comp (zb_c1 a0 hΦb)).mul (pd_c1 hΦb i))
  have e := dvg_lin 1 (-1) hB (fun i => diff_of_c1 (pd_c1 hΦb i)) x
  rw [lap_sub hΦ hΦb, h x, dvg_congr (fun i y => by ring : ∀ i y, (deriv Q (zb a0 Φb y) - 1) * pd Φb i y =
    1 * (deriv Q (zb a0 Φb y) * pd Φb i y) + -1 * pd Φb i y) x, e]
  simp only [lap]; ring

end Entropic.Var
