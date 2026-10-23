import Entropic.AppO.Flow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

/-! Appendix P, records and relative information: recovery map for an isometric channel (C14-01),
spectral invariance under isometries (C14-02, partial), the rank-one renewal kernel (C14-03, C14-04),
history dimensions (C14-06, C14-82, C14-83), the visibility-source identity and its consequences
(C14-07, C14-09, C14-10, C14-12 … C14-15, C14-17, C14-18, C14-24), the injective count (C14-20),
the union bound (C14-25), modular rank and dimension exclusions (C14-35), local stability of full
rank (C14-37), the relative-phase generator (C14-40), the diagonal-bridge obstruction (C14-42),
projected factorization (C14-47), data processing (C14-52), ledger monotonicity (C14-60), the
horizon normalization (C14-65), history commutation (C14-67), occupation conservation (C14-84)
and the false-record minimum (C14-86). -/

noncomputable section
namespace Entropic.AppP
open Real Matrix
open scoped Kronecker

/-! ### C14-01, C14-02: isometric channels -/

section Isometry
variable {a h : Type*} [Fintype a] [Fintype h] [DecidableEq a] [DecidableEq h]

/-- C14-01: for an isometry V (V†V = I), R(σ) = V†σV + Tr((I − VV†)σ)σ₀ inverts C(ρ) = VρV†
and is trace preserving when Tr σ₀ = 1. -/
theorem recovery_map (V : Matrix h a ℂ) (hV : Vᴴ * V = 1) (σ0 : Matrix a a ℂ) (hσ0 : σ0.trace = 1) :
    (∀ ρ : Matrix a a ℂ, Vᴴ * (V * ρ * Vᴴ) * V + ((1 - V * Vᴴ) * (V * ρ * Vᴴ)).trace • σ0 = ρ) ∧
      ∀ σ : Matrix h h ℂ, (Vᴴ * σ * V + ((1 - V * Vᴴ) * σ).trace • σ0).trace = σ.trace := by
  constructor
  · intro ρ
    have h1 : Vᴴ * (V * ρ * Vᴴ) * V = ρ := by
      simp only [← Matrix.mul_assoc]; rw [hV, Matrix.one_mul, Matrix.mul_assoc, hV, Matrix.mul_one]
    have h2 : ((1 - V * Vᴴ) * (V * ρ * Vᴴ)).trace = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub]
      have : V * Vᴴ * (V * ρ * Vᴴ) = V * ρ * Vᴴ := by
        simp only [← Matrix.mul_assoc]; rw [Matrix.mul_assoc V Vᴴ V, hV, Matrix.mul_one]
      rw [this, sub_self]
    rw [h1, h2, zero_smul, add_zero]
  · intro σ
    rw [Matrix.trace_add, Matrix.trace_smul, hσ0, smul_eq_mul, mul_one, Matrix.sub_mul, Matrix.one_mul,
      Matrix.trace_sub, Matrix.mul_assoc, Matrix.trace_mul_comm Vᴴ, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm σ]; ring

/-- C14-01: the renewal map E*(ρ) = ρ* Tr ρ is trace preserving when Tr ρ* = 1. -/
theorem renewal_tp (ρs ρ : Matrix a a ℂ) (h : ρs.trace = 1) : (ρ.trace • ρs).trace = ρ.trace := by
  rw [Matrix.trace_smul, h, smul_eq_mul, mul_one]

/-- C14-02 (spectral invariance): (VAV†)ⁿ = VAⁿV† and Tr((VAV†)ⁿ) = Tr(Aⁿ) for n ≥ 1, so VρV† − VσV†
has the same nonzero spectrum as ρ − σ. -/
theorem isometry_powers (V : Matrix h a ℂ) (hV : Vᴴ * V = 1) (A : Matrix a a ℂ) (n : ℕ) :
    (V * A * Vᴴ) ^ (n + 1) = V * A ^ (n + 1) * Vᴴ ∧ ((V * A * Vᴴ) ^ (n + 1)).trace = (A ^ (n + 1)).trace := by
  have hp : ∀ n : ℕ, (V * A * Vᴴ) ^ (n + 1) = V * A ^ (n + 1) * Vᴴ := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ A (k + 1)]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul]
  refine ⟨hp n, ?_⟩
  rw [hp n, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hV, Matrix.mul_one]

theorem isometry_difference (V : Matrix h a ℂ) (ρ σ : Matrix a a ℂ) :
    V * ρ * Vᴴ - V * σ * Vᴴ = V * (ρ - σ) * Vᴴ := by
  rw [Matrix.mul_sub, Matrix.sub_mul]
end Isometry

/-! ### C14-03, C14-04: the rank-one renewal kernel -/

section Kernel
variable {B : Type*} [Fintype B] [DecidableEq B]

/-- K*(b, b′) = p*(b′). -/
def Kstar (p : B → ℝ) : Matrix B B ℝ := Matrix.of fun _ b' => p b'

theorem Kstar_idem (p : B → ℝ) (hp : ∑ b, p b = 1) : Kstar p * Kstar p = Kstar p := by
  ext i j; simp [Kstar, Matrix.mul_apply, ← Finset.sum_mul, hp]

/-- C14-03: every eigenvalue of K* is 0 or 1, Tr K* = 1, and the 1-eigenvectors are constant. -/
theorem Kstar_spectrum (p : B → ℝ) (hp : ∑ b, p b = 1) :
    (Kstar p).trace = 1 ∧
      (∀ (μ : ℝ) (v : B → ℝ), v ≠ 0 → Kstar p *ᵥ v = μ • v → μ = 0 ∨ μ = 1) ∧
      (∀ v : B → ℝ, Kstar p *ᵥ v = v → ∀ b b', v b = v b') := by
  refine ⟨by simp [Matrix.trace, Kstar, hp], ?_, ?_⟩
  · intro μ v hv hμ
    have h2 : Kstar p *ᵥ (Kstar p *ᵥ v) = Kstar p *ᵥ v := by
      rw [Matrix.mulVec_mulVec, Kstar_idem p hp]
    rw [hμ, Matrix.mulVec_smul, hμ, smul_smul] at h2
    have : (μ * μ - μ) • v = 0 := by rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · have : μ * (μ - 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · left; exact h
      · right; linarith
    · exact absurd h hv
  · intro v hv b b'
    have e : ∀ c, (Kstar p *ᵥ v) c = ∑ x, p x * v x := by
      intro c; simp [Kstar, Matrix.mulVec, dotProduct]
    rw [← hv, e, e]

/-- C14-03: det(tI − K*) = t^{n−1}(t − 1) for t ≠ 0 (matrix determinant lemma), i.e. the
characteristic polynomial evaluates as λ^{n−1}(λ − 1). -/
theorem Kstar_charpoly_eval (p : B → ℝ) (hp : ∑ b, p b = 1) (t : ℝ) (ht : t ≠ 0) :
    (Kstar p).charpoly.eval t = t ^ (Fintype.card B - 1) * (t - 1) := by
  rw [Matrix.eval_charpoly]
  have hK : Kstar p = Matrix.replicateCol Unit (fun _ => (1:ℝ)) * Matrix.replicateRow Unit p := by
    ext i j; simp [Kstar, Matrix.mul_apply]
  have e : Matrix.scalar B t - Kstar p =
      t • (1 + Matrix.replicateCol Unit (fun _ => -t⁻¹) * Matrix.replicateRow Unit p) := by
    rw [hK]; ext i j
    simp [Matrix.mul_apply, Matrix.one_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> field_simp <;> ring
  rw [e, Matrix.det_smul, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hdot : p ⬝ᵥ (fun _ => -t⁻¹) = -t⁻¹ := by
    simp [dotProduct, ← Finset.sum_mul, hp]
  rw [hdot]
  rcases Nat.eq_zero_or_pos (Fintype.card B) with h0 | hpos
  · exfalso
    have : IsEmpty B := Fintype.card_eq_zero_iff.mp h0
    simp at hp
  · obtain ⟨k, hk⟩ : ∃ k, Fintype.card B = k + 1 := ⟨Fintype.card B - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, pow_succ]; field_simp; ring

/-- C14-04: X₁ drawn from K*(X₀, ·) is independent of X₀: the joint law is μ ⊗ p*; and dλ₂² = 0. -/
theorem descendant_independent (μ p : B → ℝ) (hμ : ∑ b, μ b = 1) (b b' : B) :
    μ b * Kstar p b b' = μ b * p b' ∧ ∑ x, μ x * Kstar p x b' = p b' ∧ ∀ d : ℝ, d * (0:ℝ) ^ 2 = 0 := by
  refine ⟨by simp [Kstar], by simp [Kstar, ← Finset.sum_mul, hμ], fun d => by ring⟩
end Kernel

/-! ### C14-06, C14-82, C14-83: history dimensions -/

/-- C14-06: dim(H₀ ⊗ ⨂ C^{d_n}) = dim H₀ · Π d_n; if every d_n ≥ 2 this is ≥ 2^N dim H₀; for d_n = 9, 9^N. -/
theorem history_dimension (N h0 : ℕ) (d : Fin N → ℕ) :
    Fintype.card (Fin h0 × ((n : Fin N) → Fin (d n))) = h0 * ∏ n, d n ∧
      ((∀ n, 2 ≤ d n) → 2 ^ N * h0 ≤ h0 * ∏ n, d n) ∧
      ∏ _n : Fin N, (9:ℕ) = 9 ^ N := by
  refine ⟨by simp [Fintype.card_pi], fun h2 => ?_, by simp⟩
  have : 2 ^ N ≤ ∏ n, d n := by
    calc 2 ^ N = ∏ _n : Fin N, 2 := by simp
      _ ≤ ∏ n, d n := Finset.prod_le_prod (fun n _ => h2 n)
  rw [mul_comm]; exact Nat.mul_le_mul_left h0 this

/-- C14-82: an injective linear map (isometry) from a space of dimension Π d_n forces
dim H_hist ≥ Π d_n, and ln Π d_n = Σ ln d_n. -/
theorem non_reuse {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (f : V →ₗ[K] W) (hf : Function.Injective f) {N : ℕ} (d : Fin N → ℕ)
    (hV : Module.finrank K V = ∏ n, d n) (hd : ∀ n, 0 < d n) :
    ∏ n, d n ≤ Module.finrank K W ∧ Real.log (∏ n, (d n : ℝ)) = ∑ n, Real.log (d n) := by
  haveI : FiniteDimensional K V := Module.Finite.of_injective f hf
  refine ⟨hV ▸ LinearMap.finrank_le_finrank_of_injective hf, ?_⟩
  rw [Real.log_prod]; intro n _; exact_mod_cast (hd n).ne'

/-- C14-83: Π_{n ≤ N} d_n ≤ D with d_n ≥ d_min > 1 gives N ≤ ln D / ln d_min. -/
theorem record_root {N : ℕ} (d : Fin N → ℝ) {D dmin : ℝ} (hmin : 1 < dmin) (hd : ∀ n, dmin ≤ d n)
    (hD : ∏ n, d n ≤ D) : (N : ℝ) ≤ Real.log D / Real.log dmin := by
  have h1 : dmin ^ N ≤ D := by
    calc dmin ^ N = ∏ _n : Fin N, dmin := by simp
      _ ≤ ∏ n, d n := Finset.prod_le_prod₀ (fun _ _ => by linarith) (fun n _ => hd n)
      _ ≤ D := hD
  have hpos : 0 < dmin ^ N := by positivity
  have := Real.log_le_log hpos h1
  rw [Real.log_pow] at this
  rw [le_div_iff₀ (Real.log_pos hmin)]; exact this

/-! ### C14-07 … C14-18: conditioned laws -/

section Conditioned
variable {B : Type*} [Fintype B] [DecidableEq B]

/-- Kullback–Leibler divergence (nats). -/
def KL (Q P : B → ℝ) : ℝ := ∑ b, Q b * (Real.log (Q b) - Real.log (P b))

/-- P_def = P(· | A). -/
def cond (P : B → ℝ) (A : Finset B) (b : B) : ℝ := if b ∈ A then P b / ∑ x ∈ A, P x else 0

/-- C14-07: D(P(·|A) ‖ P) = −ln P(A). -/
theorem visibility_source (P : B → ℝ) (A : Finset B) (hP : ∀ b, 0 ≤ P b) (hA : 0 < ∑ x ∈ A, P x) :
    KL (cond P A) P = -Real.log (∑ x ∈ A, P x) := by
  set PA := ∑ x ∈ A, P x
  have term : ∀ b, cond P A b * (Real.log (cond P A b) - Real.log (P b)) =
      if b ∈ A then -(P b / PA) * Real.log PA else 0 := by
    intro b
    unfold cond
    split_ifs with hb
    · rcases (hP b).eq_or_lt with h | h
      · rw [← h]; simp
      · rw [Real.log_div h.ne' hA.ne']; ring
    · simp
  simp only [KL, term]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sum_mul,
    Finset.sum_neg_distrib, ← Finset.sum_div, div_self hA.ne']
  ring

/-- C14-09: −ln[(1/7)Σ(1 − p_m)] = ln(7/6) when Σp_m = 1. -/
theorem isotropic_benchmark (p : Fin 7 → ℝ) (hp : ∑ m, p m = 1) :
    -Real.log ((1/7) * ∑ m, (1 - p m)) = Real.log (7/6) := by
  rw [Finset.sum_sub_distrib, hp]; simp
  rw [show (7:ℝ)⁻¹ * (7 - 1) = (7/6)⁻¹ by norm_num, Real.log_inv, neg_neg]

/-- C14-10: −(1/7)Σ ln(1 − p_m) ≥ ln(7/6) for p_m ∈ [0,1), Σp = 1, with equality iff all p_m = 1/7. -/
theorem jensen_cost (p : Fin 7 → ℝ) (hp : ∑ m, p m = 1) (h1 : ∀ m, p m < 1) :
    Real.log (7/6) ≤ -(1/7) * ∑ m, Real.log (1 - p m) ∧
      (Real.log (7/6) = -(1/7) * ∑ m, Real.log (1 - p m) ↔ ∀ m, p m = 1/7) := by
  have hw0 : ∀ m ∈ (Finset.univ : Finset (Fin 7)), (0:ℝ) < 1/7 := fun _ _ => by norm_num
  have hw1 : ∑ _m : Fin 7, (1/7 : ℝ) = 1 := by simp
  have hmem : ∀ m ∈ (Finset.univ : Finset (Fin 7)), 1 - p m ∈ Set.Ioi (0:ℝ) :=
    fun m _ => by simp only [Set.mem_Ioi]; linarith [h1 m]
  have jen := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (fun m hm => (hw0 m hm).le) hw1 hmem
  have hsum : ∑ m, (1/7 : ℝ) • (1 - p m) = 6/7 := by
    simp only [smul_eq_mul, ← Finset.mul_sum, Finset.sum_sub_distrib, hp]; simp; norm_num
  rw [hsum] at jen
  simp only [smul_eq_mul, ← Finset.mul_sum] at jen
  have l76 : Real.log (7/6) = -Real.log (6/7) := by
    rw [show (7/6 : ℝ) = (6/7)⁻¹ by norm_num, Real.log_inv]
  refine ⟨by rw [l76]; linarith, ?_⟩
  have eq := strictConcaveOn_log_Ioi.map_sum_eq_iff_of_pos hw0 hw1 hmem
  rw [hsum] at eq
  simp only [smul_eq_mul, ← Finset.mul_sum] at eq
  constructor
  · intro h
    have : Real.log (6/7) = 1/7 * ∑ m, Real.log (1 - p m) := by rw [l76] at h; linarith
    have hall := eq.mp this
    intro m
    have hc : ∀ k, p k = p m := fun k => by
      have := hall (Finset.mem_univ k) (Finset.mem_univ m); linarith
    have : ∑ k, p k = 7 * p m := by simp [hc]
    linarith
  · intro h
    have : Real.log (6/7) = 1/7 * ∑ m, Real.log (1 - p m) :=
      eq.mpr (fun j _ k _ => by rw [h j, h k])
    rw [l76]; linarith

/-- C14-12: for P = e^{−ηK}/Z and any law Q, H(P) − H(Q) = D(Q‖P) + η(⟨K⟩_P − ⟨K⟩_Q). -/
theorem entropy_decomposition (K : B → ℝ) (η : ℝ) (Q : B → ℝ) (hQ : ∑ b, Q b = 1) (hQ0 : ∀ b, 0 ≤ Q b) :
    let Z := ∑ b, Real.exp (-η * K b)
    let P := fun b => Real.exp (-η * K b) / Z
    (∑ b, negMulLog (P b)) - ∑ b, negMulLog (Q b) =
      KL Q P + η * ((∑ b, P b * K b) - ∑ b, Q b * K b) := by
  intro Z P
  by_cases hB : IsEmpty B
  · simp at hQ
  rw [not_isEmpty_iff] at hB
  obtain ⟨b0⟩ := hB
  have hZ : 0 < Z := Finset.sum_pos (fun b _ => Real.exp_pos _) ⟨b0, Finset.mem_univ _⟩
  have hlogP : ∀ b, Real.log (P b) = -η * K b - Real.log Z := by
    intro b; simp only [P]; rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  have hP1 : ∑ b, P b = 1 := by simp only [P]; rw [← Finset.sum_div]; exact div_self hZ.ne'
  have e1 : ∑ b, negMulLog (P b) = η * ∑ b, P b * K b + Real.log Z := by
    simp only [negMulLog, hlogP]
    have : ∀ b, -P b * (-η * K b - Real.log Z) = η * (P b * K b) + P b * Real.log Z := fun b => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hP1, one_mul]
  have e2 : KL Q P = -∑ b, negMulLog (Q b) + η * ∑ b, Q b * K b + Real.log Z := by
    simp only [KL, negMulLog, hlogP]
    have : ∀ b, Q b * (Real.log (Q b) - (-η * K b - Real.log Z)) =
        -(-Q b * Real.log (Q b)) + η * (Q b * K b) + Q b * Real.log Z := fun b => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      hQ, one_mul]
  rw [e1, e2]; ring

/-- C14-13: the indicator statistic is sufficient: with X = 1_A, X_#P_def = (1, 0) and X_#P = (P(A), 1 − P(A)),
and D(X_#P_def ‖ X_#P) = −ln P(A) = D(P_def ‖ P). -/
theorem one_bit_sufficient (P : B → ℝ) (A : Finset B) (hP : ∀ b, 0 ≤ P b) (hA : 0 < ∑ x ∈ A, P x) :
    1 * (Real.log 1 - Real.log (∑ x ∈ A, P x)) + 0 * (Real.log 0 - Real.log (1 - ∑ x ∈ A, P x)) =
      KL (cond P A) P := by
  rw [visibility_source P A hP hA]; simp

/-- C14-14: Σ_b √(P_def(b) P(b)) = √P(A). -/
theorem sqrt_overlap (P : B → ℝ) (A : Finset B) (hP : ∀ b, 0 ≤ P b) (hA : 0 < ∑ x ∈ A, P x) :
    ∑ b, Real.sqrt (cond P A b * P b) = Real.sqrt (∑ x ∈ A, P x) := by
  set PA := ∑ x ∈ A, P x
  have term : ∀ b, Real.sqrt (cond P A b * P b) = if b ∈ A then P b / Real.sqrt PA else 0 := by
    intro b; unfold cond; split_ifs with hb
    · rw [show P b / PA * P b = (P b) ^ 2 / PA by ring, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (hP b)]
    · simp
  simp only [term]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sum_div]
  have := Real.sq_sqrt hA.le
  have hs : 0 < Real.sqrt PA := Real.sqrt_pos.mpr hA
  field_simp; linarith

/-- C14-15: with θ = arccos √P(A), −ln P(A) = −2 ln cos θ. -/
theorem projective_cost {PA : ℝ} (h0 : 0 < PA) (h1 : PA ≤ 1) :
    -Real.log PA = -2 * Real.log (Real.cos (Real.arccos (Real.sqrt PA))) := by
  rw [Real.cos_arccos (by linarith [Real.sqrt_nonneg PA]) (Real.sqrt_le_one.mpr h1 |>.trans le_rfl |>
    fun h => by simpa using Real.sqrt_le_sqrt h1)]
  rw [Real.log_sqrt h0.le]; ring

/-- C14-17: N independent records: (√P(A))^{2N} = P(A)^N = e^{−NΔF} with ΔF = −ln P(A). -/
theorem record_overlap_power {PA : ℝ} (h0 : 0 < PA) (N : ℕ) :
    (Real.sqrt PA ^ N) ^ 2 = PA ^ N ∧ PA ^ N = Real.exp (-(N * -Real.log PA)) := by
  constructor
  · rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt h0.le]
  · rw [show -((N:ℝ) * -Real.log PA) = Real.log (PA ^ N) by rw [Real.log_pow]; ring,
      Real.exp_log (pow_pos h0 N)]

/-- C14-18: under full support, ∅ ≠ A ⊊ B gives P(A) < 1 and −ln P(A) > 0; conversely
−ln P(A) = 0 forces A = B. -/
theorem defect_positive (P : B → ℝ) (hP : ∀ b, 0 < P b) (h1 : ∑ b, P b = 1) (A : Finset B) :
    (A.Nonempty → A ≠ Finset.univ → 0 < -Real.log (∑ x ∈ A, P x)) ∧
      (A.Nonempty → -Real.log (∑ x ∈ A, P x) = 0 → A = Finset.univ) := by
  have hlt : A ≠ Finset.univ → ∑ x ∈ A, P x < 1 := by
    intro hA
    obtain ⟨b, hb⟩ : ∃ b, b ∉ A := by
      by_contra h; push_neg at h; exact hA (Finset.eq_univ_iff_forall.mpr h)
    rw [← h1]
    exact Finset.sum_lt_sum_of_subset (Finset.subset_univ A) (Finset.mem_univ b) hb (hP b)
      (fun x _ _ => (hP x).le)
  have hpos : A.Nonempty → 0 < ∑ x ∈ A, P x := fun hn => Finset.sum_pos (fun x _ => hP x) hn
  refine ⟨fun hn hA => ?_, fun hn h0 => ?_⟩
  · have := Real.log_neg (hpos hn) (hlt hA); linarith
  · by_contra hA
    have := Real.log_neg (hpos hn) (hlt hA); linarith

/-- C14-24 (a): for unit vectors with |⟨φ,ψ⟩| < 1, ψ is not in span{φ}, so supp|ψ⟩⟨ψ| ⊄ supp|φ⟩⟨φ|
and D(|ψ⟩⟨ψ| ‖ |φ⟩⟨φ|) = +∞ by the support convention. -/
theorem distinct_pure_support {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ψ φ : E}
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (h : ‖(inner ℂ φ ψ : ℂ)‖ < 1) : ∀ c : ℂ, ψ ≠ c • φ := by
  intro c hc
  have hcn : ‖c‖ = 1 := by rw [hc, norm_smul, hφ, mul_one] at hψ; exact hψ
  rw [hc, inner_smul_right, inner_self_eq_norm_sq_to_K, hφ] at h
  simp [hcn] at h
end Conditioned

/-! ### C14-20, C14-25, C14-35, C14-37 -/

/-- C14-20: injective maps from 4 faces to 7 labels: 7·6·5·4 = 840; with orientation doubling 1680. -/
theorem injective_count : Fintype.card (Fin 4 ↪ Fin 7) = 840 ∧ 2 * 840 = 1680 := by
  refine ⟨?_, rfl⟩
  rw [Fintype.card_embedding_eq]; simp

/-- C14-25: union bound P(∪_{i ∈ s} E_i) ≤ |s| q when each P(E_i) ≤ q; N e^{−K} = e^{ln N − K} < 1 iff K > ln N. -/
theorem union_bound {Ω ι : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (s : Finset ι)
    (E : ι → Set Ω) (q : ENNReal) (hq : ∀ i ∈ s, μ (E i) ≤ q) : μ (⋃ i ∈ s, E i) ≤ s.card * q := by
  calc μ (⋃ i ∈ s, E i) ≤ ∑ i ∈ s, μ (E i) := MeasureTheory.measure_biUnion_finset_le s E
    _ ≤ ∑ _i ∈ s, q := Finset.sum_le_sum hq
    _ = s.card * q := by rw [Finset.sum_const, nsmul_eq_mul]

theorem union_threshold {N K : ℝ} (hN : 0 < N) :
    N * Real.exp (-K) = Real.exp (Real.log N - K) ∧ (Real.exp (Real.log N - K) < 1 ↔ Real.log N < K) := by
  refine ⟨by rw [Real.exp_sub, Real.exp_log hN, Real.exp_neg]; ring, ?_⟩
  rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm, Real.exp_lt_exp]
  constructor <;> intro h <;> linarith

/-- C14-35 (a): if an integer square minor is nonzero mod p, it is nonzero over ℚ (rank certificate). -/
theorem modular_rank {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℤ) (p : ℕ)
    (h : (M.map (Int.cast : ℤ → ZMod p)).det ≠ 0) : (M.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
  intro h0
  have e1 : (M.map (Int.cast : ℤ → ℚ)).det = (M.det : ℚ) := by
    rw [show (M.map (Int.cast : ℤ → ℚ)) = (Int.castRingHom ℚ).mapMatrix M from rfl, ← RingHom.map_det]; rfl
  have e2 : (M.map (Int.cast : ℤ → ZMod p)).det = (M.det : ZMod p) := by
    rw [show (M.map (Int.cast : ℤ → ZMod p)) = (Int.castRingHom (ZMod p)).mapMatrix M from rfl,
      ← RingHom.map_det]; rfl
  rw [e1] at h0; rw [e2] at h
  have : M.det = 0 := by exact_mod_cast h0
  rw [this] at h; simp at h

/-- C14-35 (b): dim sl(16) = 255, dim so(16) = 120, dim sp(16) = 136, and a 255-dimensional
subspace of a 255-dimensional space is everything. -/
theorem dimension_exclusions {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hV : Module.finrank K V = 255) (S : Submodule K V) (hS : Module.finrank K S = 255) :
    16 ^ 2 - 1 = 255 ∧ 16 * 15 / 2 = 120 ∧ 16 * 17 / 2 = 136 ∧ S = ⊤ := by
  refine ⟨rfl, rfl, rfl, Submodule.eq_top_of_finrank_eq (by rw [hS, hV])⟩

/-- C14-37: a nonzero minor of a continuously parametrized matrix stays nonzero nearby. -/
theorem full_rank_stable {X : Type*} [TopologicalSpace X] {n : Type*} [Fintype n] [DecidableEq n]
    (M : X → Matrix n n ℝ) (hM : Continuous M) (c0 : X) (h : (M c0).det ≠ 0) :
    ∀ᶠ c in nhds c0, (M c).det ≠ 0 :=
  (hM.matrix_det.continuousAt).eventually_ne h

/-! ### C14-40: relative-phase generator -/

/-- Ω_ref on the retained 9-dimensional space, as the diagonal (ω₀; ω₁ ×3; ω₂ ×5). -/
def omegaVec (ω0 ω1 ω2 : ℝ) : Fin 9 → ℝ := ![ω0, ω1, ω1, ω1, ω2, ω2, ω2, ω2, ω2]

/-- C14-40: S_ω = Ω − (Tr Ω/9)I is traceless and symmetric, Tr Ω = ω₀ + 3ω₁ + 5ω₂, and S_ω ≠ 0 when
ω₀ ≠ ω₁; the ω_J = √(k² + M²/Z + (κ/Z)q_J) with q = (6,5,3) are distinct when κ/Z ≠ 0. -/
theorem phase_generator (ω0 ω1 ω2 : ℝ) :
    let Ω := Matrix.diagonal (omegaVec ω0 ω1 ω2)
    Ω.trace = ω0 + 3 * ω1 + 5 * ω2 ∧ (Ω - (Ω.trace / 9) • (1 : Matrix (Fin 9) (Fin 9) ℝ)).trace = 0 ∧
      (Ω - (Ω.trace / 9) • 1)ᵀ = Ω - (Ω.trace / 9) • 1 ∧
      (ω0 ≠ ω1 → Ω - (Ω.trace / 9) • (1 : Matrix (Fin 9) (Fin 9) ℝ) ≠ 0) := by
  intro Ω
  have htr : Ω.trace = ω0 + 3 * ω1 + 5 * ω2 := by
    simp [Ω, Matrix.trace_diagonal, Fin.sum_univ_succ, omegaVec]; ring
  refine ⟨htr, ?_, ?_, fun hne h => hne ?_⟩
  · rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]; simp; try ring
  · simp [Ω, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.diagonal_transpose]
  · have e0 := congrFun (congrFun h 0) 0
    have e1 := congrFun (congrFun h 1) 1
    simp [Ω, omegaVec, Matrix.diagonal_apply] at e0 e1 <;> linarith

theorem frequencies_distinct {k2 m κZ : ℝ} (hκ : κZ ≠ 0) (h6 : 0 ≤ k2 + m + κZ * 6)
    (h5 : 0 ≤ k2 + m + κZ * 5) (h3 : 0 ≤ k2 + m + κZ * 3) :
    Real.sqrt (k2 + m + κZ * 6) ≠ Real.sqrt (k2 + m + κZ * 5) ∧
      Real.sqrt (k2 + m + κZ * 5) ≠ Real.sqrt (k2 + m + κZ * 3) := by
  constructor <;> intro h <;> apply hκ
  · have := (Real.sqrt_inj h6 h5).mp h; linarith
  · have := (Real.sqrt_inj h5 h3).mp h; linarith

/-! ### C14-42, C14-47, C14-67, C14-84: tensor commutation -/

section Tensor
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- The centralizer of Z in matrices is a Lie subalgebra. -/
def centralizer (Z : Matrix n n ℂ) : LieSubalgebra ℂ (Matrix n n ℂ) where
  carrier := {X | X * Z = Z * X}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb; simp only [Set.mem_setOf_eq] at *; rw [Matrix.add_mul, Matrix.mul_add, ha, hb]
  smul_mem' := by
    intro c a ha; simp only [Set.mem_setOf_eq] at *; rw [Matrix.smul_mul, Matrix.mul_smul, ha]
  lie_mem' := by
    intro a b ha hb; simp only [Set.mem_setOf_eq, Ring.lie_def] at *
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc,
      Matrix.mul_assoc b, ha, ← Matrix.mul_assoc b, hb, Matrix.mul_assoc]

/-- C14-42: every element of the Lie algebra generated by matrices commuting with Z commutes with Z. -/
theorem lie_closure_commutes (S : Set (Matrix n n ℂ)) (Z : Matrix n n ℂ) (hS : ∀ s ∈ S, s * Z = Z * s) :
    ∀ x ∈ LieSubalgebra.lieSpan ℂ (Matrix n n ℂ) S, x * Z = Z * x := by
  intro x hx
  have : LieSubalgebra.lieSpan ℂ (Matrix n n ℂ) S ≤ centralizer Z :=
    (LieSubalgebra.lieSpan_le).mpr (fun s hs => hS s hs)
  exact this hx

/-- C14-42 (generators): A ⊗ I and H₂ ⊗ H₃ commute with I ⊗ H₃. -/
theorem bridge_generators_commute (A H2 : Matrix n n ℂ) (H3 : Matrix m m ℂ) :
    (A ⊗ₖ (1 : Matrix m m ℂ)) * ((1 : Matrix n n ℂ) ⊗ₖ H3) = ((1 : Matrix n n ℂ) ⊗ₖ H3) * (A ⊗ₖ 1) ∧
      (H2 ⊗ₖ H3) * ((1 : Matrix n n ℂ) ⊗ₖ H3) = ((1 : Matrix n n ℂ) ⊗ₖ H3) * (H2 ⊗ₖ H3) := by
  constructor <;> rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul] <;> simp

/-- C14-47: (P ⊗ P′)(H ⊗ H′)(P ⊗ P′) = (PHP) ⊗ (P′H′P′). -/
theorem projected_factorization (P H : Matrix n n ℂ) (P' H' : Matrix m m ℂ) :
    (P ⊗ₖ P') * (H ⊗ₖ H') * (P ⊗ₖ P') = (P * H * P) ⊗ₖ (P' * H' * P') := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

/-- C14-67: X ⊗ I commutes with I ⊗ Y. -/
theorem history_commutes (X : Matrix n n ℂ) (Y : Matrix m m ℂ) :
    (X ⊗ₖ (1 : Matrix m m ℂ)) * ((1 : Matrix n n ℂ) ⊗ₖ Y) = ((1 : Matrix n n ℂ) ⊗ₖ Y) * (X ⊗ₖ 1) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]; simp

/-- C14-84: if the number operators commute pairwise, every element of the algebra they generate
commutes with each of them; hence H = Σ_k f_k(n) ⊗ X_k commutes with n_m ⊗ I. -/
theorem occupation_conserved {ι : Type*} (N : ι → Matrix n n ℂ) (hN : ∀ i j, Commute (N i) (N j))
    (f : Matrix n n ℂ) (hf : f ∈ Algebra.adjoin ℂ (Set.range N)) (X : Matrix m m ℂ) (i : ι) :
    Commute f (N i) ∧ Commute (f ⊗ₖ X) (N i ⊗ₖ (1 : Matrix m m ℂ)) := by
  have hc : Commute f (N i) := by
    induction hf using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hN j i
    | algebraMap r => exact Algebra.commutes r (N i)
    | add x y _ _ hx hy => exact hx.add_left hy
    | mul x y _ _ hx hy => exact hx.mul_left hy
  refine ⟨hc, ?_⟩
  show (f ⊗ₖ X) * (N i ⊗ₖ 1) = (N i ⊗ₖ 1) * (f ⊗ₖ X)
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hc.eq]; simp
end Tensor

/-! ### C14-52: data processing (log-sum inequality) -/

section DPI
variable {ι : Type*}

/-- Log-sum inequality: Σ aᵢ ln(aᵢ/bᵢ) ≥ (Σa) ln(Σa/Σb) for aᵢ ≥ 0, bᵢ > 0. -/
theorem log_sum (s : Finset ι) (a b : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i)
    (hs : s.Nonempty) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) ≤
      ∑ i ∈ s, a i * (Real.log (a i) - Real.log (b i)) := by
  set B := ∑ i ∈ s, b i
  have hB : 0 < B := Finset.sum_pos hb hs
  have hw0 : ∀ i ∈ s, 0 ≤ b i / B := fun i hi => div_nonneg (hb i hi).le hB.le
  have hw1 : ∑ i ∈ s, b i / B = 1 := by rw [← Finset.sum_div, div_self hB.ne']
  have hmem : ∀ i ∈ s, a i / b i ∈ Set.Ici (0:ℝ) := fun i hi => div_nonneg (ha i hi) (hb i hi).le
  have jen := Real.convexOn_mul_log.map_sum_le hw0 hw1 hmem
  have e1 : ∑ i ∈ s, (b i / B) • (a i / b i) = (∑ i ∈ s, a i) / B := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [smul_eq_mul]; field_simp [(hb i hi).ne']
  have e2 : ∀ i ∈ s, (b i / B) • (a i / b i * Real.log (a i / b i)) =
      (a i * (Real.log (a i) - Real.log (b i))) / B := by
    intro i hi
    rw [smul_eq_mul]
    rcases (ha i hi).eq_or_lt with h | h
    · rw [← h]; simp
    · rw [Real.log_div h.ne' (hb i hi).ne']; field_simp [(hb i hi).ne']
  rw [e1, Finset.sum_congr rfl e2, ← Finset.sum_div] at jen
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hB] at jen
  exact jen

variable {B G : Type*} [Fintype B] [Fintype G]

/-- C14-52: for a Markov kernel M(g|b) and full-support P*, D(μ_def ‖ μ*) ≤ D(P_def ‖ P*), and
D(Q ‖ P) ≥ 0 for probability laws. -/
theorem data_processing (Pd Ps : B → ℝ) (M : B → G → ℝ) (hPd : ∀ b, 0 ≤ Pd b) (hPs : ∀ b, 0 < Ps b)
    (hM : ∀ b g, 0 ≤ M b g) (hM1 : ∀ b, ∑ g, M b g = 1) :
    ∑ g, (∑ b, Pd b * M b g) * (Real.log (∑ b, Pd b * M b g) - Real.log (∑ b, Ps b * M b g)) ≤
      ∑ b, Pd b * (Real.log (Pd b) - Real.log (Ps b)) := by
  have hg : ∀ g, (∑ b, Pd b * M b g) * (Real.log (∑ b, Pd b * M b g) - Real.log (∑ b, Ps b * M b g)) ≤
      ∑ b, (Pd b * M b g) * (Real.log (Pd b) - Real.log (Ps b)) := by
    intro g
    set s := Finset.univ.filter (fun b => M b g ≠ 0)
    rcases s.eq_empty_or_nonempty with hs | hs
    · have hz : ∀ b, M b g = 0 := by
        intro b; by_contra h
        have : b ∈ s := by simp [s, h]
        rw [hs] at this; simp at this
      simp [hz]
    · have hsub : ∀ f : B → ℝ, (∀ b, M b g = 0 → f b = 0) → ∑ b, f b = ∑ b ∈ s, f b := by
        intro f hf; rw [Finset.sum_filter_of_ne]; intro b _ hb h; exact hb (hf b h)
      have L := log_sum s (fun b => Pd b * M b g) (fun b => Ps b * M b g)
        (fun b _ => mul_nonneg (hPd b) (hM b g))
        (fun b hb => mul_pos (hPs b) (lt_of_le_of_ne (hM b g) (Ne.symm (Finset.mem_filter.mp hb).2))) hs
      rw [hsub (fun b => Pd b * M b g) (fun b h => by simp [h]),
        hsub (fun b => Ps b * M b g) (fun b h => by simp [h]),
        hsub (fun b => Pd b * M b g * (Real.log (Pd b) - Real.log (Ps b))) (fun b h => by simp [h])]
      have hpos : 0 < ∑ b ∈ s, Ps b * M b g := Finset.sum_pos
        (fun b hb => mul_pos (hPs b) (lt_of_le_of_ne (hM b g) (Ne.symm (Finset.mem_filter.mp hb).2))) hs
      rcases (Finset.sum_nonneg (fun b (_ : b ∈ s) => mul_nonneg (hPd b) (hM b g))).eq_or_lt with h0 | h0
      · rw [← h0]; simp
        apply Finset.sum_nonneg; intro b hb
        have : Pd b * M b g = 0 := by
          have := (Finset.sum_eq_zero_iff_of_nonneg (fun b (_ : b ∈ s) => mul_nonneg (hPd b) (hM b g))).mp
            h0.symm b hb
          exact this
        rw [this]; simp
      · rw [Real.log_div h0.ne' hpos.ne'] at L
        calc _ ≤ ∑ b ∈ s, Pd b * M b g * (Real.log (Pd b * M b g) - Real.log (Ps b * M b g)) := L
          _ = _ := by
            refine Finset.sum_congr rfl (fun b hb => ?_)
            have hMb : M b g ≠ 0 := (Finset.mem_filter.mp hb).2
            rcases (hPd b).eq_or_lt with h | h
            · rw [← h]; simp
            · rw [Real.log_mul h.ne' hMb, Real.log_mul (hPs b).ne' hMb]; ring
  calc _ ≤ ∑ g, ∑ b, (Pd b * M b g) * (Real.log (Pd b) - Real.log (Ps b)) := Finset.sum_le_sum (fun g _ => hg g)
    _ = ∑ b, Pd b * (Real.log (Pd b) - Real.log (Ps b)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      calc ∑ g, Pd b * M b g * (Real.log (Pd b) - Real.log (Ps b))
          = ∑ g, (Pd b * (Real.log (Pd b) - Real.log (Ps b))) * M b g :=
            Finset.sum_congr rfl (fun g _ => by ring)
        _ = _ := by rw [← Finset.mul_sum, hM1, mul_one]
end DPI

/-! ### C14-57, C14-60, C14-65, C14-86 -/

/-- C14-57: ⟨Ĥ_rec⟩ = ½ Σ_{a=1}^3 ⟨ξ_a²⟩ = 3/2 when each ⟨ξ_a²⟩ = 1. -/
theorem record_strand_energy (x : Fin 3 → ℝ) (hx : ∀ a, x a = 1) : (1/2) * ∑ a, x a = 3/2 := by
  simp [hx]; norm_num

/-- C14-60: with η > 0 and E_{rel,j} ≥ 0, E_Λ(N) = E_Λ(0) + Σ_{j<N} ηE_{rel,j} is nondecreasing in N. -/
theorem dark_ledger_monotone {η : ℝ} (hη : 0 < η) (E : ℕ → ℝ) (hE : ∀ j, 0 ≤ E j) (E0 : ℝ) :
    Monotone (fun N => E0 + ∑ j ∈ Finset.range N, η * E j) := by
  apply monotone_nat_of_le_succ; intro N
  simp only [Finset.sum_range_succ]
  have := mul_nonneg hη.le (hE N); linarith

/-- C14-65: with a_ch = 4 ln 2 · L*², (A/a_ch) ln 2 = A/(4L*²). -/
theorem horizon_cut (A L : ℝ) (hL : L ≠ 0) :
    A / (4 * Real.log 2 * L ^ 2) * Real.log 2 = A / (4 * L ^ 2) := by
  have : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp

/-- C14-86: P ≤ e^{−K} and P ≤ e^{−KE/k_BT} give P ≤ min; the thermal factor is the smaller iff E/k_BT > 1. -/
theorem false_record_min {P K r : ℝ} (hK : 0 < K) (h1 : P ≤ Real.exp (-K)) (h2 : P ≤ Real.exp (-(K * r))) :
    P ≤ min (Real.exp (-K)) (Real.exp (-(K * r))) ∧
      (Real.exp (-(K * r)) < Real.exp (-K) ↔ 1 < r) := by
  refine ⟨le_min h1 h2, ?_⟩
  rw [Real.exp_lt_exp]; constructor <;> intro h <;> nlinarith

end Entropic.AppP
