import Entropic.BlackHole
import Entropic.Spine
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! Appendix F: strong-field sector, horizon counting, ringdown (ledger C06-01 … -36). -/

noncomputable section
namespace Entropic.AppFG
open Real Set Filter Topology Matrix

/-! ### F.1 capacity fraction and lapse (C06-01, -03, -04) -/

/-- C06-01: q = S_ent/S_∞ ∈ [0, 1] whenever 0 ≤ S_ent ≤ S_∞. -/
theorem capacity_fraction {S Sinf : ℝ} (hS : 0 < Sinf) (h0 : 0 ≤ S) (h1 : S ≤ Sinf) :
    S / Sinf ∈ Icc (0:ℝ) 1 :=
  ⟨div_nonneg h0 hS.le, (div_le_one hS).mpr h1⟩

/-- C06-03: d/dδ (1 − δ)^α at δ = 0 is −α, i.e. (1 − δ)^α = 1 − αδ + o(δ). -/
theorem power_weak_field (α : ℝ) :
    HasDerivAt (fun δ : ℝ => (1 - δ) ^ α) (-α) 0 := by
  have hg : HasDerivAt (fun δ : ℝ => 1 - δ) (-1) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_sub 1
  have h := (Real.hasDerivAt_rpow_const (p := α) (x := 1 - 0) (Or.inl (by norm_num))).comp (0:ℝ) hg
  convert h using 1 <;> simp [Function.comp_def]

/-- The exponent of a power law on (0,1] equals its one-sided slope at q = 1. -/
theorem exponent_eq_slope {f : ℝ → ℝ} {α d : ℝ} (hα : ∀ q ∈ Ioc (0:ℝ) 1, f q = q ^ α)
    (hd : HasDerivWithinAt f d (Ioc (0:ℝ) 1) 1) : α = d := by
  have hpow : HasDerivWithinAt (fun q : ℝ => q ^ α) α (Ioc (0:ℝ) 1) 1 := by
    have := (Real.hasDerivAt_rpow_const (p := α) (x := 1) (Or.inl one_ne_zero)).hasDerivWithinAt
      (s := Ioc (0:ℝ) 1)
    simpa using this
  have hc : HasDerivWithinAt (fun q : ℝ => q ^ α) d (Ioc (0:ℝ) 1) 1 :=
    hd.congr (fun q hq => (hα q hq).symm) (by simp [hα 1 ⟨one_pos, le_rfl⟩])
  exact (uniqueDiffOn_Ioc 0 1 1 ⟨one_pos, le_rfl⟩).eq_deriv _ hpow hc

/-- C06-04 (second form): a continuous, positive, multiplicative F on (0,1] with
F(1 − δ) = 1 − δ + o(δ) is F(q) = q. -/
theorem lapse_square_is_identity {F : ℝ → ℝ} (hpos : ∀ q ∈ Ioc (0:ℝ) 1, 0 < F q)
    (hmul : ∀ x ∈ Ioc (0:ℝ) 1, ∀ y ∈ Ioc (0:ℝ) 1, F (x * y) = F x * F y)
    (hcont : ContinuousOn F (Ioc (0:ℝ) 1)) (hd : HasDerivWithinAt F 1 (Ioc (0:ℝ) 1) 1) :
    ∀ q ∈ Ioc (0:ℝ) 1, F q = q := by
  obtain ⟨α, hα⟩ := Entropic.BlackHole.lapse_is_power hpos hmul hcont
  have h1 := exponent_eq_slope hα hd
  intro q hq; rw [hα q hq, h1, Real.rpow_one]

/-! ### F.2–F.3 reduced action and field equations (C06-06, -09, -10, -12, -13, -14) -/

/-- C06-06 pointwise: if ⁽⁴⁾R = ⁽²⁾R + (2/R²)(1 − (∇R)² − 2R□R), then
R²·⁽⁴⁾R = R²·⁽²⁾R + 2 − 2(∇R)² − 4R□R; and 4π·c³/(16πG) = c³/(4G). -/
theorem reduced_integrand {R R2 R4 X box : ℝ} (hR : R ≠ 0)
    (h : R4 = R2 + 2 / R ^ 2 * (1 - X - 2 * R * box)) :
    R ^ 2 * R4 = R ^ 2 * R2 + 2 - 2 * X - 4 * R * box := by
  rw [h]; field_simp; ring

theorem reduced_prefactor {c G : ℝ} (hG : G ≠ 0) :
    4 * Real.pi * (c ^ 3 / (16 * Real.pi * G)) = c ^ 3 / (4 * G) := by
  have := Real.pi_ne_zero; field_simp; ring

/-- C06-09 (pointwise tensor form): in a 2D orbit space with metric h, inverse h⁻¹, gradient
v = ∇R and symmetric Hessian H = ∇∇R, the metric field equation
2R(h_ab □R − H_ab) + h_ab(q − 1) = 0 (q = h^{ab}v_av_b, □R = h^{ab}H_ab) forces
∇_a[R(1 − q)] = v_a(1 − q) − 2R H_ab h^{bc} v_c = 0: the Misner–Sharp mass is constant. -/
theorem misner_sharp_conserved (h hinv : Matrix (Fin 2) (Fin 2) ℝ) (hh : h * hinv = 1)
    (hsym : hinv.transpose = hinv) (H : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) (R : ℝ)
    (heq : ∀ a b, 2 * R * (h a b * (∑ c, ∑ d, hinv c d * H c d) - H a b) +
      h a b * ((∑ c, ∑ d, hinv c d * v c * v d) - 1) = 0)
    (hHsym : H.transpose = H) (hhinv : hinv * h = 1) :
    ∀ a, v a * (1 - ∑ c, ∑ d, hinv c d * v c * v d) -
      2 * R * ∑ b, ∑ c, H a b * hinv b c * v c = 0 := by
  set box := ∑ c, ∑ d, hinv c d * H c d
  set q := ∑ c, ∑ d, hinv c d * v c * v d
  -- trace: hinv^{ab} E_ab = 2R(2 box − box) + 2(q − 1)
  have htr : ∑ a, ∑ b, hinv a b * h b a = 2 := by
    have := congrArg Matrix.trace hhinv
    simpa [Matrix.trace, Matrix.mul_apply] using this
  have hT : 2 * R * box = 2 * (1 - q) := by
    have h0 : ∑ a, ∑ b, hinv a b * (2 * R * (h b a * box - H b a) + h b a * (q - 1)) = 0 := by
      simp [heq]
    have e1 : ∑ a, ∑ b, hinv a b * (2 * R * (h b a * box - H b a) + h b a * (q - 1)) =
        2 * R * box * (∑ a, ∑ b, hinv a b * h b a) - 2 * R * (∑ a, ∑ b, hinv a b * H b a) +
          (q - 1) * (∑ a, ∑ b, hinv a b * h b a) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_)); ring
    have e2 : ∑ a, ∑ b, hinv a b * H b a = box := by
      simp only [box]; rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
      have := congrFun (congrFun hsym c) d; simp at this; rw [this]
    rw [e1, e2, htr] at h0; linarith
  intro a
  -- contraction with h^{bc} v_c
  have hc : ∑ b, ∑ c, (2 * R * (h a b * box - H a b) + h a b * (q - 1)) * hinv b c * v c = 0 := by
    simp [heq]
  have hδ : ∀ c, ∑ b, h a b * hinv b c = if a = c then 1 else 0 := by
    intro c; have := congrFun (congrFun hh a) c; simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have e3 : ∑ b, ∑ c, (2 * R * (h a b * box - H a b) + h a b * (q - 1)) * hinv b c * v c =
      (2 * R * box + (q - 1)) * v a - 2 * R * ∑ b, ∑ c, H a b * hinv b c * v c := by
    have : ∀ b c, (2 * R * (h a b * box - H a b) + h a b * (q - 1)) * hinv b c * v c =
        (2 * R * box + (q - 1)) * (h a b * hinv b c * v c) - 2 * R * (H a b * hinv b c * v c) := by
      intro b c; ring
    simp_rw [this, Finset.sum_sub_distrib, ← Finset.mul_sum]
    congr 2
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hδ]; simp
  rw [e3] at hc
  rw [hT] at hc
  linarith

/-- C06-10: if q enters only through √h·λ(N² − q), its Euler–Lagrange equation is
−√h λ = 0, so λ = 0. -/
theorem multiplier_zero {s lam N : ℝ} (hs : 0 < s) :
    HasDerivAt (fun q => s * lam * (N ^ 2 - q)) (-(s * lam)) 0 ∧ (-(s * lam) = 0 → lam = 0) := by
  refine ⟨?_, fun h => ?_⟩
  · have := ((hasDerivAt_id (0:ℝ)).const_sub (N ^ 2)).const_mul (s * lam); simpa using this
  · have : s * lam = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hs.ne'

/-- C06-12: for h = diag(−f, 1/f) (f = 1 − r_h/r ≠ 0) the rr component of h⁻¹ is f, so
q_geo = h^{rr} = 1 − r_h/r = N². -/
theorem qgeo_inverse_metric {f : ℝ} (hf : f ≠ 0) :
    (Matrix.diagonal ![-f, 1/f])⁻¹ = Matrix.diagonal ![-1/f, f] := by
  rw [Matrix.inv_eq_left_inv]
  rw [Matrix.diagonal_mul_diagonal]
  rw [show (fun i => ![-1/f, f] i * ![-f, 1/f] i) = fun _ => (1:ℝ) by
    funext i; fin_cases i <;> simp <;> field_simp]
  exact Matrix.diagonal_one

/-- C06-13: δS/S_∞ = 2GM/(c²r) and q = 1 − δS/S_∞ give q = q_geo. -/
theorem weak_deficit_matches {G M c r : ℝ} : 1 - 2 * G * M / (c ^ 2 * r) =
    Entropic.BlackHole.qS (Entropic.BlackHole.rS G c M) r := by
  unfold Entropic.BlackHole.qS Entropic.BlackHole.rS; ring_nf

/-! ### Trapping classification (C06-15) -/

/-- For a 2D Lorentzian metric G with future null vectors k₊, k₋ (Gk₊·k₊ = Gk₋·k₋ = 0,
m = k₊·Gk₋ < 0), every covector w obeys w·G⁻¹w = 2(w·k₊)(w·k₋)/m. With w = ∇R and
θ± = (2/R)k±·∇R this is q_geo = R²θ₊θ₋/(2m), so sign q_geo = −sign(θ₊θ₋). -/
theorem null_decomposition (G : Matrix (Fin 2) (Fin 2) ℝ) (kp km : Fin 2 → ℝ)
    (hpp : kp ⬝ᵥ (G *ᵥ kp) = 0) (hmm : km ⬝ᵥ (G *ᵥ km) = 0) (hm : kp ⬝ᵥ (G *ᵥ km) ≠ 0)
    (hGsym : G.transpose = G) (hGinv : IsUnit G.det) (w : Fin 2 → ℝ) :
    w ⬝ᵥ (G⁻¹ *ᵥ w) = 2 * (w ⬝ᵥ kp) * (w ⬝ᵥ km) / (kp ⬝ᵥ (G *ᵥ km)) := by
  set m := kp ⬝ᵥ (G *ᵥ km)
  set K : Matrix (Fin 2) (Fin 2) ℝ := !![kp 0, km 0; kp 1, km 1]
  set M : Matrix (Fin 2) (Fin 2) ℝ := !![0, m; m, 0]
  have h01 : G 1 0 = G 0 1 := by
    have := congrFun (congrFun hGsym 0) 1; simpa using this
  have hmp : km ⬝ᵥ (G *ᵥ kp) = m := by
    simp only [m, dotProduct, Matrix.mulVec, Fin.sum_univ_two]; rw [h01]; ring
  have hKGK : K.transpose * G * K = M := by
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two] at hpp hmm hmp
    simp only [m, dotProduct, Matrix.mulVec, Fin.sum_univ_two] at hmp ⊢
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [K, M, Matrix.mul_apply, Fin.sum_univ_two, m, dotProduct, Matrix.mulVec] <;>
      linarith
  have hdetM : IsUnit M.det := by
    simp only [M, Matrix.det_fin_two_of]; simp; exact hm
  have hdetK : IsUnit K.transpose.det := by
    have h := congrArg Matrix.det hKGK
    rw [Matrix.det_mul, Matrix.det_mul] at h
    have : Matrix.det K.transpose * (Matrix.det G * Matrix.det K) ≠ 0 := by
      rw [← mul_assoc, h]; exact hdetM.ne_zero
    exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul this)
  have hdetK' : IsUnit K.det := by rwa [Matrix.det_transpose] at hdetK
  have hGK : G * K = (K.transpose)⁻¹ * M := by
    rw [← hKGK, ← mul_assoc, ← mul_assoc, Matrix.nonsing_inv_mul _ hdetK, one_mul]
  have hinvG : G⁻¹ = K * M⁻¹ * K.transpose := by
    apply Matrix.inv_eq_right_inv
    rw [← mul_assoc, ← mul_assoc, hGK, mul_assoc (K.transpose)⁻¹ M, Matrix.mul_nonsing_inv _ hdetM,
      mul_one, Matrix.nonsing_inv_mul _ hdetK]
  have hMinv : M⁻¹ = !![0, 1/m; 1/m, 0] := by
    apply Matrix.inv_eq_right_inv
    ext i j; fin_cases i <;> fin_cases j <;> simp [M, Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp
  rw [hinvG, hMinv]
  simp only [K, dotProduct, Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  field_simp; ring

/-- Sign classification: with m < 0, q_geo = 2(∇R·k₊)(∇R·k₋)/m has the sign opposite to
θ₊θ₋ = (4/R²)(∇R·k₊)(∇R·k₋), and is unchanged in sign by positive rescalings of k±. -/
theorem trapping_sign {a b m R : ℝ} (hm : m < 0) (hR : 0 < R) :
    let q := 2 * a * b / m
    let θp := 2 / R * a
    let θm := 2 / R * b
    (0 < q ↔ θp * θm < 0) ∧ (q = 0 ↔ θp * θm = 0) ∧ (q < 0 ↔ 0 < θp * θm) ∧
      q = R ^ 2 * θp * θm / (2 * m) := by
  intro q θp θm
  have hθ : θp * θm = 4 / R ^ 2 * (a * b) := by simp only [θp, θm]; field_simp; ring
  have h4 : 0 < 4 / R ^ 2 := by positivity
  have hq : q = 2 / m * (a * b) := by simp only [q]; ring
  have h2m : 2 / m < 0 := div_neg_of_pos_of_neg (by norm_num) hm
  have k1 : 0 < 2 / m * (a * b) ↔ a * b < 0 := by
    constructor
    · intro h; by_contra hc; push_neg at hc
      have := mul_nonpos_of_nonpos_of_nonneg h2m.le hc; linarith
    · intro h; exact mul_pos_of_neg_of_neg h2m h
  have k2 : 2 / m * (a * b) < 0 ↔ 0 < a * b := by
    constructor
    · intro h; by_contra hc; push_neg at hc
      have := mul_nonneg_of_nonpos_of_nonpos h2m.le hc; linarith
    · intro h; exact mul_neg_of_neg_of_pos h2m h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hθ, hq, k1]; constructor
    · intro h; exact mul_neg_of_pos_of_neg h4 h
    · intro h; by_contra hc; push_neg at hc
      have := mul_nonneg h4.le hc; linarith
  · rw [hθ, hq]; constructor
    · intro h; rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd h1 h2m.ne
      · rw [h1]; ring
    · intro h; rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd h1 h4.ne'
      · rw [h1]; ring
  · rw [hθ, hq, k2]; constructor
    · intro h; exact mul_pos h4 h
    · intro h; by_contra hc; push_neg at hc
      have := mul_nonpos_of_nonneg_of_nonpos h4.le hc; linarith
  · simp only [q, θp, θm]; field_simp

/-! ### F.5 horizon counting (C06-18 … -26) -/

/-- C06-21: N independent binary cuts carry ln 2^N = N ln 2. -/
theorem cut_entropy (N : ℕ) : Real.log (2 ^ N) = N * Real.log 2 := by
  rw [Real.log_pow]

def ZA (J : ℝ) : ℝ := J / Real.sqrt (J * (J + 1))

/-- C06-22: Z_A(3N) = √(3N/(3N+1)), Z_A(3) = √3/2, Z_A strictly increasing in N, Z_A → 1. -/
theorem ZA_props :
    (∀ N : ℕ, 1 ≤ N → ZA (3 * N) = Real.sqrt (3 * N / (3 * N + 1))) ∧
      ZA 3 = Real.sqrt 3 / 2 ∧
      StrictMonoOn (fun x : ℝ => Real.sqrt (x / (x + 1))) (Ioi 0) ∧
      Tendsto (fun N : ℕ => Real.sqrt (3 * (N:ℝ) / (3 * N + 1))) atTop (𝓝 1) := by
  have key : ∀ x : ℝ, 0 < x → x / Real.sqrt (x * (x + 1)) = Real.sqrt (x / (x + 1)) := by
    intro x hx
    have hs : Real.sqrt (x * (x + 1)) ^ 2 = x * (x + 1) := Real.sq_sqrt (by positivity)
    have hsp : 0 < Real.sqrt (x * (x + 1)) := Real.sqrt_pos.mpr (by positivity)
    rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
    field_simp; rw [hs]
  refine ⟨fun N hN => key _ (by have h1 : (1:ℝ) ≤ (N:ℝ) := (by exact_mod_cast hN); linarith),
    ?_, ?_, ?_⟩
  · unfold ZA; rw [show (3:ℝ) * (3 + 1) = 12 by norm_num,
      show (12:ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    have := Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num)
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
  · intro a ha b hb hab
    have ha' : (0:ℝ) < a := ha; have hb' : (0:ℝ) < b := hb
    apply Real.sqrt_lt_sqrt (by positivity)
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
  · have h1 : Tendsto (fun N : ℕ => 1 - 1 / (3 * (N:ℝ) + 1)) atTop (𝓝 (1 - 0)) := by
      apply tendsto_const_nhds.sub
      apply tendsto_const_nhds.div_atTop
      exact tendsto_atTop_add_const_right _ _ ((tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num))
    have h2 := (Real.continuous_sqrt.tendsto _).comp h1
    rw [sub_zero, Real.sqrt_one] at h2
    refine h2.congr (fun N => ?_)
    simp only [Function.comp]
    congr 1
    have : (0:ℝ) < 3 * N + 1 := by positivity
    field_simp; ring

end Entropic.AppFG
