import Entropic.AppH1.Algebra
import Entropic.AppCDE.Continuum
import Entropic.BlackHole
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Appendix H.6–H.9 marked vertex and charged transfer (ledger C07-13, -23, -42, -56, -57,
-58, -61, -65, -66, -67, -68, -69, -70, -72, -73, -74, -75, -87, -127). -/

noncomputable section
namespace Entropic.AppH1
open Real Matrix Entropic.FiniteModel Entropic.ClosureRoot

/-! ### Gibbs inequality and the seven-layer KL identity (C07-13, -23, -42, -72) -/

/-- Pointwise: P ln(P/Q) ≥ P − Q (P ≥ 0, Q > 0), with equality iff P = Q. -/
theorem gibbs_pointwise {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 < Q) :
    P - Q ≤ P * Real.log (P / Q) ∧ (P * Real.log (P / Q) = P - Q → P = Q) := by
  rcases hP.eq_or_lt with h | h
  · subst h; simp; refine ⟨hQ.le, fun h => by linarith⟩
  · have hr : 0 < Q / P := by positivity
    have h1 := Real.log_le_sub_one_of_pos hr
    rw [Real.log_div hQ.ne' h.ne'] at h1
    rw [Real.log_div h.ne' hQ.ne']
    constructor
    · have : P * (Real.log Q - Real.log P) ≤ P * (Q / P - 1) := mul_le_mul_of_nonneg_left h1 h.le
      rw [show P * (Q / P - 1) = Q - P by field_simp] at this; linarith
    · intro heq
      by_contra hne
      have hq1 : Q / P ≠ 1 := by intro h'; apply hne; field_simp at h'; linarith
      have h2 := Real.log_lt_sub_one_of_pos hr hq1
      rw [Real.log_div hQ.ne' h.ne'] at h2
      have : P * (Real.log Q - Real.log P) < P * (Q / P - 1) := mul_lt_mul_of_pos_left h2 h
      rw [show P * (Q / P - 1) = Q - P by field_simp] at this; linarith

/-- Gibbs: for probability laws P, Q on a finite set with Q > 0, D(P‖Q) ≥ 0, and D = 0 iff P = Q. -/
theorem gibbs {α : Type*} [Fintype α] (P Q : α → ℝ) (hP : ∀ x, 0 ≤ P x) (hQ : ∀ x, 0 < Q x)
    (hP1 : ∑ x, P x = 1) (hQ1 : ∑ x, Q x = 1) :
    0 ≤ ∑ x, P x * Real.log (P x / Q x) ∧ (∑ x, P x * Real.log (P x / Q x) = 0 → P = Q) := by
  have hpt := fun x => gibbs_pointwise (hP x) (hQ x)
  have hsum : ∑ x, (P x - Q x) ≤ ∑ x, P x * Real.log (P x / Q x) :=
    Finset.sum_le_sum (fun x _ => (hpt x).1)
  rw [Finset.sum_sub_distrib, hP1, hQ1, sub_self] at hsum
  refine ⟨hsum, fun h0 => ?_⟩
  funext x
  have hnn : ∀ x ∈ Finset.univ, 0 ≤ P x * Real.log (P x / Q x) - (P x - Q x) :=
    fun x _ => by linarith [(hpt x).1]
  have hz : ∑ x, (P x * Real.log (P x / Q x) - (P x - Q x)) = 0 := by
    rw [Finset.sum_sub_distrib, h0, Finset.sum_sub_distrib, hP1, hQ1]; ring
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz x (Finset.mem_univ x)
  exact (hpt x).2 (by linarith)

variable {B : Type*} [Fintype B] [DecidableEq B]

/-- Marginal on coordinate i of a law on `Fin n → B`. -/
def marg {n : ℕ} (P : (Fin n → B) → ℝ) (i : Fin n) (b : B) : ℝ :=
  ∑ x : Fin n → B, if x i = b then P x else 0

/-- Σ_x P(x) f(x_i) = Σ_b marg_i(b) f(b). -/
theorem sum_marg {n : ℕ} (P : (Fin n → B) → ℝ) (i : Fin n) (f : B → ℝ) :
    ∑ x : Fin n → B, P x * f (x i) = ∑ b, marg P i b * f b := by
  simp only [marg, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_ite_eq]; simp

/-- C07-23, -42: if every one-coordinate marginal of P on Bⁿ is p (p > 0), then
D(P‖p^{⊗n}) = nH(p) − H(P) ≥ 0, with equality iff P = p^{⊗n}. -/
theorem fixed_marginal_kl {n : ℕ} (P : (Fin n → B) → ℝ) (p : B → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hP1 : ∑ x, P x = 1) (hp : ∀ b, 0 < p b) (hp1 : ∑ b, p b = 1) (hm : ∀ i, marg P i = p) :
    ∑ x, P x * Real.log (P x / ∏ i, p (x i)) =
        n * (∑ b, Real.negMulLog (p b)) - ∑ x, Real.negMulLog (P x) ∧
      0 ≤ n * (∑ b, Real.negMulLog (p b)) - ∑ x, Real.negMulLog (P x) ∧
      (n * (∑ b, Real.negMulLog (p b)) - ∑ x, Real.negMulLog (P x) = 0 → P = fun x => ∏ i, p (x i)) := by
  have hQ : ∀ x : Fin n → B, 0 < ∏ i, p (x i) := fun x => Finset.prod_pos (fun i _ => hp _)
  have hQ1 : ∑ x : Fin n → B, ∏ i, p (x i) = 1 := by
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (t := fun _ => Finset.univ)]; simp [hp1]
  have hid : ∑ x, P x * Real.log (P x / ∏ i, p (x i)) =
      n * (∑ b, Real.negMulLog (p b)) - ∑ x, Real.negMulLog (P x) := by
    have e1 : ∀ x, P x * Real.log (P x / ∏ i, p (x i)) =
        -Real.negMulLog (P x) - ∑ i, P x * Real.log (p (x i)) := by
      intro x
      rcases (hP x).eq_or_lt with h | h
      · rw [← h]; simp
      · rw [Real.log_div h.ne' (hQ x).ne', Real.log_prod (fun i _ => (hp _).ne'), mul_sub,
          Finset.mul_sum]
        unfold Real.negMulLog; ring
    simp_rw [e1, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    simp_rw [sum_marg P _ (fun b => Real.log (p b)), hm]
    simp [Real.negMulLog, Finset.sum_neg_distrib]; ring
  obtain ⟨g1, g2⟩ := gibbs P (fun x => ∏ i, p (x i)) hP hQ hP1 hQ1
  refine ⟨hid, by rw [← hid]; exact g1, fun h0 => g2 (by rw [hid, h0])⟩

/-- C07-72: the joint entropy of a law with a coordinate marginal p is at least H(p). -/
theorem joint_ge_marginal {n : ℕ} (P : (Fin n → B) → ℝ) (hP : ∀ x, 0 ≤ P x) (i : Fin n) :
    ∑ b, Real.negMulLog (marg P i b) ≤ ∑ x, Real.negMulLog (P x) := by
  have hle : ∀ x, P x ≤ marg P i (x i) := by
    intro x; unfold marg
    exact le_of_eq_of_le (by simp) (Finset.single_le_sum (f := fun y => if y i = x i then P y else 0)
      (fun y _ => by split_ifs <;> simp [hP]) (Finset.mem_univ x))
  have key : ∀ x, P x * (-Real.log (marg P i (x i))) ≤ Real.negMulLog (P x) := by
    intro x
    rcases (hP x).eq_or_lt with h | h
    · rw [← h]; simp
    · unfold Real.negMulLog
      have := Real.log_le_log h (hle x)
      nlinarith
  calc ∑ b, Real.negMulLog (marg P i b) = ∑ x, P x * (-Real.log (marg P i (x i))) := by
        rw [sum_marg P i (fun b => -Real.log (marg P i b))]
        refine Finset.sum_congr rfl (fun b _ => ?_); unfold Real.negMulLog; ring
    _ ≤ _ := Finset.sum_le_sum (fun x _ => key x)

/-! ### Pair contraction, dilation and Pfaffian (C07-56, -57, -58, -61) -/

/-- C07-56: u = 2ηq² with q = 2/7 is 8η/49 and 0 < u < 1 at the closure root. -/
theorem pair_contraction {η : ℝ} (h : ClosureStationary η) :
    2 * η * (2/7) ^ 2 = 8 * η / 49 ∧ 0 < 8 * η / 49 ∧ 8 * η / 49 < 1 := by
  obtain ⟨a, b⟩ := Entropic.AppCDE.eta_bracket h
  refine ⟨by ring, by linarith, by linarith⟩

/-- C07-57 (Halmos dilation, row case): for b ∈ ℝⁿ with |b|² = u < 1, the block matrix
U = [[I − c bbᵀ, −b], [bᵀ, √(1−u)]] with c = (1 − √(1−u))/u is orthogonal (UᵀU = I); its
no-event amplitude is √(1 − u). The upper block is √(I − bbᵀ). -/
theorem halmos_sqrt {n : Type*} [Fintype n] [DecidableEq n] (b : n → ℝ) {u : ℝ}
    (hu : ∑ i, b i * b i = u) (hu0 : 0 < u) (hu1 : u < 1) :
    let c := (1 - Real.sqrt (1 - u)) / u
    let S : Matrix n n ℝ := 1 - c • vecMulVec b b
    S * S = 1 - vecMulVec b b ∧ S *ᵥ b = Real.sqrt (1 - u) • b := by
  intro c S
  have hs : Real.sqrt (1 - u) ^ 2 = 1 - u := Real.sq_sqrt (by linarith)
  have hbb : vecMulVec b b * vecMulVec b b = u • vecMulVec b b := by
    ext i j; simp only [mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
    rw [show ∑ k, b i * b k * (b k * b j) = (∑ k, b k * b k) * (b i * b j) by
      rw [Finset.sum_mul]; congr 1; ext k; ring, hu]
  have hc : 2 * c - c ^ 2 * u = 1 := by
    simp only [c]; field_simp
    nlinarith [hs]
  constructor
  · simp only [S]
    rw [sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, smul_mul_smul_comm,
      hbb, smul_smul]
    rw [show (1 : Matrix n n ℝ) - c • vecMulVec b b - (c • vecMulVec b b - (c * c * u) • vecMulVec b b) =
      1 - (2 * c - c * c * u) • vecMulVec b b by module]
    rw [show 2 * c - c * c * u = 1 by nlinarith [hc], one_smul]
  · simp only [S]
    rw [sub_mulVec, one_mulVec, smul_mulVec]
    have : vecMulVec b b *ᵥ b = u • b := by
      ext i; simp only [mulVec, vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul]
      rw [show ∑ k, b i * b k * b k = b i * ∑ k, b k * b k by rw [Finset.mul_sum]; congr 1; ext k; ring,
        hu]; ring
    rw [this, smul_smul]
    have hc2 : c * u = 1 - Real.sqrt (1 - u) := by simp only [c]; field_simp
    rw [hc2]; module

/-- C07-58: for J = [[0,1],[−1,0]], Pf(αJ) = α and det(αJ) = α² = Pf²; 21 independent blocks
give α²¹ = (1 − u)^{21/2}, while 1 − u per block would give (1 − u)²¹. -/
theorem pfaffian_edge {α u : ℝ} (hα : α = Real.sqrt (1 - u)) (hu : u ≤ 1) :
    (α • !![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = α ∧
      (α • !![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ).det = α ^ 2 ∧
      α ^ 21 = (1 - u) ^ (21/2 : ℝ) ∧ Nat.choose 7 2 = 21 := by
  refine ⟨by simp, by simp [det_fin_two]; ring, ?_, by decide⟩
  rw [hα, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num

/-! ### Charged transfer (C07-66 … -70) -/

/-- C07-66: a continuous positive semigroup T on [0,∞) with T(1) = e^{−a} is T(s) = e^{−as}. -/
theorem scalar_semigroup {T : ℝ → ℝ} {a : ℝ} (hpos : ∀ s, 0 ≤ s → 0 < T s)
    (hmul : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = T s * T t) (hc : ContinuousOn T (Set.Ici 0))
    (h1 : T 1 = Real.exp (-a)) : ∀ s, 0 ≤ s → T s = Real.exp (-a * s) := by
  -- f(q) = T(−ln q) on (0,1] is continuous, positive and multiplicative
  set f : ℝ → ℝ := fun q => T (-Real.log q)
  have hlog : ∀ q ∈ Set.Ioc (0:ℝ) 1, 0 ≤ -Real.log q := by
    intro q hq
    have := Real.log_nonpos hq.1.le hq.2
    linarith
  have fpos : ∀ q ∈ Set.Ioc (0:ℝ) 1, 0 < f q := fun q hq => hpos _ (hlog q hq)
  have fmul : ∀ x ∈ Set.Ioc (0:ℝ) 1, ∀ y ∈ Set.Ioc (0:ℝ) 1, f (x * y) = f x * f y := by
    intro x hx y hy
    simp only [f]; rw [Real.log_mul hx.1.ne' hy.1.ne', neg_add]
    exact hmul _ _ (hlog x hx) (hlog y hy)
  have fcont : ContinuousOn f (Set.Ioc (0:ℝ) 1) := by
    apply hc.comp (Real.continuousOn_log.mono (fun q hq => hq.1.ne')).neg
    intro q hq; exact hlog q hq
  obtain ⟨α, hα⟩ := Entropic.BlackHole.lapse_is_power fpos fmul fcont
  have hT : ∀ s, 0 ≤ s → T s = Real.exp (-α * s) := by
    intro s hs
    have hq : Real.exp (-s) ∈ Set.Ioc (0:ℝ) 1 := Entropic.BlackHole.exp_neg_mem hs
    have h2 := hα _ hq
    change T (-Real.log (Real.exp (-s))) = _ at h2
    rw [Real.log_exp, neg_neg] at h2
    rw [h2, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]; ring_nf
  have : α = a := by
    have h := hT 1 zero_le_one; rw [h1] at h
    have := Real.exp_injective h; linarith
  intro s hs; rw [hT s hs, this]

/-- C07-67: T_e = e^{−aZ n_e} with a = −(3/2)ln(1−r): H_e = −(ħ/τ)ln T_e =
−(3ħZ/(2τ))ln(1−r)·n_e; vacuum eigenvalue 1, occupied e^{−aZ} ∈ (0,1). -/
theorem charged_transfer {ħ τ r Z : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hZ : 0 < Z) (ne : ℝ) :
    let a := -(3/2) * Real.log (1 - r)
    ((-(ħ / τ)) * Real.log (Real.exp (-a * Z * ne)) = -(3 * ħ * Z / (2 * τ)) * Real.log (1 - r) * ne ∧
      Real.exp (-a * Z * 0) = 1 ∧ 0 < Real.exp (-a * Z * 1) ∧ Real.exp (-a * Z * 1) < 1) := by
  intro a
  have ha : 0 < a := by
    have := Real.log_lt_log (by linarith) (show 1 - r < 1 by linarith); simp at this
    simp only [a]; linarith
  refine ⟨by rw [Real.log_exp]; simp only [a]; ring, by simp, Real.exp_pos _, ?_⟩
  calc Real.exp (-a * Z * 1) < Real.exp 0 := Real.exp_lt_exp.mpr (by nlinarith)
    _ = 1 := Real.exp_zero

/-- C07-68: det [[1, −√r vᵀ], [−√r v, I]] = 1 − r vᵀv (Schur complement). -/
theorem recurrence_det {M : Type*} [Fintype M] [DecidableEq M] (v : M → ℝ) (r : ℝ) :
    (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) (-(Real.sqrt r) • replicateRow (Fin 1) v)
      (-(Real.sqrt r) • replicateCol (Fin 1) v) (1 : Matrix M M ℝ)).det =
      1 - Real.sqrt r ^ 2 * ∑ i, v i * v i := by
  rw [det_fromBlocks_one₂₂, det_fin_one]
  simp [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => by ring)

/-- C07-69: the recurrence kernel has eigenvectors (1, ∓v/|v|) with eigenvalues 1 ± √(rZ)
(Z = vᵀv), eigenvalue 1 on v^⊥; positive definite iff rZ < 1. -/
theorem recurrence_spectrum {r Z : ℝ} (hr : 0 ≤ r) (hZ : 0 < Z) :
    (0 < 1 - Real.sqrt (r * Z) ↔ r * Z < 1) ∧
      (1 + Real.sqrt (r * Z)) * (1 - Real.sqrt (r * Z)) = 1 - r * Z := by
  have hs := Real.sq_sqrt (mul_nonneg hr hZ.le)
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, by nlinarith [hs]⟩
  · have : Real.sqrt (r * Z) < 1 := by linarith
    nlinarith [Real.sqrt_nonneg (r * Z)]
  · have : Real.sqrt (r * Z) < 1 := by
      rw [Real.sqrt_lt' one_pos]; linarith
    linarith

/-- The eigen-equations of the kernel 𝒦 = [[1, −√r vᵀ], [−√r v, I]] restricted to
x = (1, t·v) with t²Z = 1 (t = ±1/√Z, Z = vᵀv): both components scale by λ = 1 − √r·tZ,
i.e. λ = 1 ∓ √(rZ). -/
theorem recurrence_eigen {r Z t : ℝ} (ht2 : t ^ 2 * Z = 1) :
    (1 - Real.sqrt r * (t * Z) = (1 - Real.sqrt r * (t * Z)) * 1) ∧
      (-(Real.sqrt r) * 1 + t = (1 - Real.sqrt r * (t * Z)) * t) := by
  refine ⟨by ring, by linear_combination (Real.sqrt r) * ht2⟩

theorem recurrence_eigen_t {Z : ℝ} (hZ : 0 < Z) :
    (1 / Real.sqrt Z) ^ 2 * Z = 1 ∧ (-1 / Real.sqrt Z) ^ 2 * Z = 1 := by
  have hs : Real.sqrt Z ^ 2 = Z := Real.sq_sqrt hZ.le
  have hp : 0 < Real.sqrt Z := Real.sqrt_pos.mpr hZ
  constructor <;> field_simp <;> linarith

/-- C07-70: T_evt = (1 − rZ)^{3/2} on the occupied sector gives E = −(3ħ/(2τ))ln(1 − rZ). -/
theorem recurrence_energy {ħ τ r Z : ℝ} (h : 0 < 1 - r * Z) :
    -(ħ / τ) * Real.log ((1 - r * Z) ^ (3/2 : ℝ)) = -(3 * ħ / (2 * τ)) * Real.log (1 - r * Z) := by
  rw [Real.log_rpow h]; ring

/-! ### Routing controls and lepton values (C07-65, -73, -74, -75) -/

/-- C07-74: m_τc² = (m_τ/m_e)·0.51099895069 MeV ∈ (1776.9187, 1776.9189); against PDG
1776.93 ± 0.09 MeV this is −0.125σ (C07-75). -/
theorem tau_mass {η : ℝ} (h : ClosureStationary η) :
    1776.9187 < Entropic.Spine.tauRatio η * 0.51099895069 ∧
      Entropic.Spine.tauRatio η * 0.51099895069 < 1776.9189 ∧
      -0.1260 < (Entropic.Spine.tauRatio η * 0.51099895069 - 1776.93) / 0.09 ∧
      (Entropic.Spine.tauRatio η * 0.51099895069 - 1776.93) / 0.09 < -0.1235 := by
  obtain ⟨a, b⟩ := Entropic.Spine.tauRatio_bracket h
  refine ⟨by nlinarith, by nlinarith, ?_, ?_⟩
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith
  · rw [div_lt_iff₀ (by norm_num)]; nlinarith

/-- C07-65: G_* scales as Z²; replacing the electron factor (1+ζ)(1+7ζ²) by (1+ζ)(1+7ζ²/9)
gives −14.6σ, and by (1+ζ)(1+49ζ²) gives +98.1σ from CODATA G = 6.67430(15)·10⁻¹¹. -/
theorem routing_controls {η : ℝ} (h : ClosureStationary η) :
    let z := Entropic.Spine.zeta η
    let G := fun Z : ℝ => Entropic.AppCDE.Gstar η * (Z / Entropic.AppCDE.Ze η) ^ 2
    ((-14.7 : ℝ) < (G ((1 + z) * (1 + 7 * z ^ 2 / 9)) - 6.67430e-11) / 0.00015e-11 ∧
      (G ((1 + z) * (1 + 7 * z ^ 2 / 9)) - 6.67430e-11) / 0.00015e-11 < -14.5 ∧
      98.0 < (G ((1 + z) * (1 + 49 * z ^ 2)) - 6.67430e-11) / 0.00015e-11 ∧
      (G ((1 + z) * (1 + 49 * z ^ 2)) - 6.67430e-11) / 0.00015e-11 < 98.2) := by
  intro z G
  obtain ⟨g1, g2, -, -⟩ := Entropic.AppCDE.Gstar_value h
  obtain ⟨z1, z2⟩ := Entropic.AppCDE.zeta_rat h
  have hZe : Entropic.AppCDE.Ze η = (1 + z) * (1 + 7 * z ^ 2) := rfl
  have hz0 : 0 < z := by linarith
  have r1 : ((1 + z) * (1 + 7 * z ^ 2 / 9) / Entropic.AppCDE.Ze η) = (1 + 7 * z ^ 2 / 9) / (1 + 7 * z ^ 2) := by
    rw [hZe]; field_simp
  have r2 : ((1 + z) * (1 + 49 * z ^ 2) / Entropic.AppCDE.Ze η) = (1 + 49 * z ^ 2) / (1 + 7 * z ^ 2) := by
    rw [hZe]; field_simp
  simp only [G, r1, r2]
  have hd : 0 < 1 + 7 * z ^ 2 := by positivity
  -- bracket the ratios
  have q1l : 0.99983668 < (1 + 7 * z ^ 2 / 9) / (1 + 7 * z ^ 2) := by
    rw [lt_div_iff₀ hd]; nlinarith
  have q1u : (1 + 7 * z ^ 2 / 9) / (1 + 7 * z ^ 2) < 0.99983670 := by
    rw [div_lt_iff₀ hd]; nlinarith
  have q2l : 1.00110234 < (1 + 49 * z ^ 2) / (1 + 7 * z ^ 2) := by
    rw [lt_div_iff₀ hd]; nlinarith
  have q2u : (1 + 49 * z ^ 2) / (1 + 7 * z ^ 2) < 1.00110235 := by
    rw [div_lt_iff₀ hd]; nlinarith
  have s1l := mul_lt_mul'' q1l q1l (by norm_num) (by norm_num)
  have s1u := mul_lt_mul'' q1u q1u (by positivity) (by positivity)
  have s2l := mul_lt_mul'' q2l q2l (by norm_num) (by norm_num)
  have s2u := mul_lt_mul'' q2u q2u (by positivity) (by positivity)
  rw [← sq] at s1l s1u s2l s2u
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith
  · rw [div_lt_iff₀ (by norm_num)]; nlinarith
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith
  · rw [div_lt_iff₀ (by norm_num)]; nlinarith

/-! ### Orientation bit and renewal triangularity (C07-87, -127) -/

/-- C07-87: if a uniform bit σ is a function of both B_t and B_{t+1} (same value), the pair
cannot be independent: P(σ = +, σ′ = −) = 0 ≠ 1/4 = P(σ=+)P(σ′=−). -/
theorem orientation_bit {α : Type*} [Fintype α] (P : α → α → ℝ) (s : α → Bool)
    (hsame : ∀ b b', P b b' ≠ 0 → s b = s b')
    (hplus : ∑ b, ∑ b', (if s b = true then P b b' else 0) = 1/2)
    (hminus : ∑ b, ∑ b', (if s b' = false then P b b' else 0) = 1/2) :
    ¬ (∀ b b', P b b' = (∑ c, P b c) * (∑ c, P c b')) := by
  intro hind
  have hzero : ∑ b, ∑ b', (if s b = true ∧ s b' = false then P b b' else 0) = 0 := by
    apply Finset.sum_eq_zero; intro b _; apply Finset.sum_eq_zero; intro b' _
    split_ifs with h
    · by_contra hne; have := hsame b b' hne; rw [h.1, h.2] at this; exact absurd this (by decide)
    · rfl
  have hprod : ∑ b, ∑ b', (if s b = true ∧ s b' = false then P b b' else 0) =
      (∑ b, if s b = true then ∑ c, P b c else 0) * (∑ b', if s b' = false then ∑ c, P c b' else 0) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun b' _ => ?_))
    by_cases h1 : s b = true
    · by_cases h2 : s b' = false
      · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2, hind b b']
      · rw [if_neg (fun h => h2 h.2), if_neg h2, mul_zero]
    · rw [if_neg (fun h => h1 h.1), if_neg h1, zero_mul]
  have e1 : (∑ b, if s b = true then ∑ c, P b c else 0) = 1/2 := by
    rw [← hplus]; refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases h1 : s b = true
    · rw [if_pos h1]; exact Finset.sum_congr rfl (fun c _ => (if_pos h1).symm)
    · rw [if_neg h1]; exact (Finset.sum_eq_zero (fun c _ => if_neg h1)).symm
  have e2 : (∑ b', if s b' = false then ∑ c, P c b' else 0) = 1/2 := by
    rw [← hminus, Finset.sum_comm]; refine Finset.sum_congr rfl (fun b' _ => ?_)
    by_cases h2 : s b' = false
    · rw [if_pos h2]; exact Finset.sum_congr rfl (fun c _ => (if_pos h2).symm)
    · rw [if_neg h2]; exact (Finset.sum_eq_zero (fun c _ => if_neg h2)).symm
  rw [hprod, e1, e2] at hzero; norm_num at hzero

/-- C07-127: for an idempotent P (Q = 1 − P) and any U, 𝒯 = PU kills Q-range from the left
(Q𝒯 = 0), 𝒯ⁿ⁺¹ = (PUP)ⁿ PU, and every nonzero eigenvalue of 𝒯 is an eigenvalue of A = PUP
(with eigenvector in range P). -/
theorem renewal_triangular {R : Type*} [Ring R] (P U : R) (hP : P * P = P) :
    (1 - P) * (P * U) = 0 ∧ (∀ n : ℕ, (P * U) ^ (n + 1) = (P * U * P) ^ n * (P * U)) := by
  refine ⟨by rw [sub_mul, one_mul, ← mul_assoc, hP, sub_self], fun n => ?_⟩
  induction n with
  | zero => simp
  | succ n ih =>
    have key : P * U * (P * U) = P * U * P * (P * U) := by
      calc P * U * (P * U) = P * U * (P * P * U) := by rw [hP]
        _ = P * U * P * (P * U) := by simp only [mul_assoc]
    rw [pow_succ, ih, pow_succ, mul_assoc, key, ← mul_assoc]

theorem renewal_eigen {K : Type*} [AddCommGroup K] [Module ℝ K] (P U : K →ₗ[ℝ] K)
    (hP : P ∘ₗ P = P) {lam : ℝ} (hl : lam ≠ 0) {x : K} (hx : (P ∘ₗ U) x = lam • x) :
    P x = x ∧ (P ∘ₗ U ∘ₗ P) x = lam • x := by
  have hPx : P x = x := by
    have : P ((P ∘ₗ U) x) = (P ∘ₗ U) x := by
      simp only [LinearMap.comp_apply]; exact congrFun (congrArg DFunLike.coe hP) _
    rw [hx, map_smul] at this
    exact (smul_right_injective K hl) this
  refine ⟨hPx, ?_⟩
  simp only [LinearMap.comp_apply] at hx ⊢; rw [hPx, hx]

end Entropic.AppH1
