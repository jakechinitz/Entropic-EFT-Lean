import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

/-! Appendix J: route triple, colour channel, Wilson coefficient, diamond lattice and couplings
(ledger C10-25, -26, -29 … -31, -33, -34, -36, -37, -40 … -43, -45 … -48, -50, -52 … -54). -/

noncomputable section
namespace Entropic.AppIJ
open Matrix
open scoped Kronecker

/-- C10-25: D_μS_Q = ∂_μS_Q − qA_μ is invariant under S_Q ↦ S_Q + α, A_μ ↦ A_μ + ∂_μα/q. -/
theorem baseline_gauge (dS A dα q : ℝ) (hq : q ≠ 0) : (dS + dα) - q * (A + dα / q) = dS - q * A := by
  field_simp; ring

/-- C10-26: the fixed-point-free involutions of {1,2,3,4} (perfect matchings) number 3, and S₄ acts
transitively on them by conjugation. -/
theorem pairings :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 4) => σ * σ = 1 ∧ ∀ i, σ i ≠ i)).card = 3 ∧
      ∀ μ ν : Equiv.Perm (Fin 4), (μ * μ = 1 ∧ ∀ i, μ i ≠ i) → (ν * ν = 1 ∧ ∀ i, ν i ≠ i) →
        ∃ g : Equiv.Perm (Fin 4), g * μ * g⁻¹ = ν := by
  constructor
  · decide
  · decide

/-! ### Route covariance and Gram matrices (C10-29, -30, -33) -/

def J3 : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun _ _ => 1
def P1 : Matrix (Fin 3) (Fin 3) ℝ := (1/3 : ℝ) • J3
def P2 : Matrix (Fin 3) (Fin 3) ℝ := 1 - P1

theorem P1_idem : P1 * P1 = P1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P1, J3, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

theorem P2_idem : P2 * P2 = P2 := by
  simp only [P2, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, P1_idem]; abel

theorem P1_P2 : P1 * P2 = 0 := by simp [P2, Matrix.mul_sub, P1_idem]

/-- C10-29: aI + b(J − I) = (a + 2b)P₁ + (a − b)P₂. -/
theorem circulant_decomp (a b : ℝ) :
    a • (1 : Matrix (Fin 3) (Fin 3) ℝ) + b • (J3 - 1) = (a + 2 * b) • P1 + (a - b) • P2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P1, P2, J3, Matrix.one_apply] <;> ring

/-- C10-33: G = I − (1/20)(J − I) = (9/10)P₁ + (21/20)P₂, and (21/20)/(9/10) = 7/6. -/
theorem route_gram :
    (1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) + (-1/20 : ℝ) • (J3 - 1) = (9/10 : ℝ) • P1 + (21/20 : ℝ) • P2 ∧
      ((21:ℝ)/20) / (9/10) = 7/6 := by
  refine ⟨by rw [circulant_decomp]; norm_num, by norm_num⟩

/-- C10-30: for C = λ₁P₁ + λ₂P₂, 1ᵀC1 = 3λ₁ = Var(R_A + R_B + R_C); with R_A+R_B+R_C = 72 − (3/2)K²,
λ₁ = (1/3)(9/4)Var(K²) = (3/4)Var(K²). -/
theorem singlet_eigenvalue (l1 l2 : ℝ) :
    (fun _ => (1:ℝ)) ⬝ᵥ ((l1 • P1 + l2 • P2) *ᵥ fun _ => 1) = 3 * l1 ∧
      ∀ VarK : ℝ, (1/3) * ((3/2) ^ 2 * VarK) = (3/4) * VarK := by
  constructor
  · simp [P1, P2, J3, dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.one_apply]; ring
  · intro V; ring

/-- C10-31: the permutation action of S₃ on 1^⊥ ⊂ ℝ³ is irreducible: for every nonzero v with
v₀ + v₁ + v₂ = 0 some transposition σ makes v and σv linearly independent (nonzero 2×2 minor). -/
theorem route_irreducible (v : Fin 3 → ℝ) (hs : v 0 + v 1 + v 2 = 0) (hv : v ≠ 0) :
    v 0 * v 0 - v 1 * v 1 ≠ 0 ∨ v 0 * v 0 - v 2 * v 2 ≠ 0 ∨ v 1 * v 1 - v 2 * v 2 ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2, h3⟩ := h
  apply hv
  have e1 : (v 0 - v 1) * (v 0 + v 1) = 0 := by linarith
  have e2 : (v 0 - v 2) * (v 0 + v 2) = 0 := by linarith
  funext i
  rcases mul_eq_zero.mp e1 with a | a <;> rcases mul_eq_zero.mp e2 with b | b <;>
    fin_cases i <;> simp <;> linarith

/-! ### Holonomy and return failure (C10-36, C10-37, C10-40, C10-41) -/

/-- C10-36: if U_{yx} ↦ V_y U_{yx} V_x⁻¹, a path-ordered product transforms by the end-point frames,
in particular a closed loop transforms by conjugation. -/
theorem holonomy_gauge {G : Type*} [Group G] (V : ℕ → G) (U : ℕ → G) (n : ℕ) :
    (List.ofFn fun k : Fin n => V (n - k) * U (n - 1 - k) * (V (n - 1 - k))⁻¹).prod =
      V n * (List.ofFn fun k : Fin n => U (n - 1 - k)).prod * (V 0)⁻¹ := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ]
    have h1 : (List.ofFn fun k : Fin m => V (m + 1 - (k + 1)) * U (m + 1 - 1 - (k + 1)) *
        (V (m + 1 - 1 - (k + 1)))⁻¹) = List.ofFn fun k : Fin m => V (m - k) * U (m - 1 - k) * (V (m - 1 - k))⁻¹ := by
      congr 1; funext k; congr 3 <;> omega
    have h2 : (List.ofFn fun k : Fin m => U (m + 1 - 1 - (k + 1))) = List.ofFn fun k : Fin m => U (m - 1 - k) := by
      congr 1; funext k; congr 1; omega
    rw [h1, h2, ih, Nat.add_sub_cancel]
    group

/-- C10-37: for unit q and unitary U, ‖P − UPU*‖²_HS = 2(1 − |⟨q, Uq⟩|²), P = qq*. -/
theorem return_failure {n : Type*} [Fintype n] [DecidableEq n] (q : n → ℂ) (U : Matrix n n ℂ)
    (hq : star q ⬝ᵥ q = 1) (hU : Uᴴ * U = 1) :
    let P := Matrix.vecMulVec q (star q)
    let Q := U * P * Uᴴ
    ((P - Q) * (P - Q)).trace = 2 * (1 - (star q ⬝ᵥ (U *ᵥ q)) * star (star q ⬝ᵥ (U *ᵥ q))) := by
  intro P Q
  have hP : P * P = P := by
    ext i j; simp only [P, Matrix.mul_apply, Matrix.vecMulVec_apply]
    rw [show ∑ k, q i * star q k * (q k * star q j) = q i * star q j * ∑ k, star q k * q k by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)]
    rw [show ∑ k, star q k * q k = star q ⬝ᵥ q from rfl, hq, mul_one]
  have htrP : P.trace = 1 := by
    rw [← hq]; simp only [P, Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, dotProduct, Pi.star_apply]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hQQ : Q * Q = Q := by
    simp only [Q]
    rw [show U * P * Uᴴ * (U * P * Uᴴ) = U * P * (Uᴴ * U) * P * Uᴴ by simp only [Matrix.mul_assoc], hU,
      Matrix.mul_one, Matrix.mul_assoc U P P, hP]
  have htrQ : Q.trace = 1 := by
    simp only [Q]; rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, htrP]
  have hPMP : ∀ M : Matrix n n ℂ, P * M * P = (star q ⬝ᵥ (M *ᵥ q)) • P := by
    intro M; ext i j
    simp only [P, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct,
      Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
  have hPU : (P * Uᴴ).trace = star (star q ⬝ᵥ (U *ᵥ q)) := by
    simp only [P, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply,
      Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hPQ : (P * Q).trace = (star q ⬝ᵥ (U *ᵥ q)) * star (star q ⬝ᵥ (U *ᵥ q)) := by
    simp only [Q]
    rw [show P * (U * P * Uᴴ) = P * U * P * Uᴴ by simp only [Matrix.mul_assoc], hPMP, Matrix.smul_mul,
      Matrix.trace_smul, hPU, smul_eq_mul]
  have hQP : (Q * P).trace = (P * Q).trace := Matrix.trace_mul_comm _ _
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub,
    hP, hQQ, htrP, htrQ, hQP, hPQ]
  ring

/-- C10-40: the trace of Ad(U): X ↦ UXU† on M_n is |Tr U|² (Σ_{ij} (U E_ij U†)_ij = Tr U · conj Tr U);
on the traceless complement of CI it is |Tr U|² − 1. -/
theorem adjoint_character {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ) :
    ∑ i, ∑ j, (U * Matrix.single i j (1:ℂ) * Uᴴ : Matrix n n ℂ) i j = U.trace * star U.trace := by
  have key : ∀ i j, (U * Matrix.single i j (1:ℂ) * Uᴴ : Matrix n n ℂ) i j = U i i * star (U j j) := by
    intro i j
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single j]
    · simp [Matrix.mul_apply, Matrix.single_apply]
    · intro b _ hb
      rw [Matrix.mul_apply]
      apply mul_eq_zero_of_left
      apply Finset.sum_eq_zero; intro x _
      rw [Matrix.single_apply, if_neg (fun h => hb h.2.symm), mul_zero]
    · simp
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => key i j))]
  simp only [Matrix.trace, Matrix.diag, star_sum, Finset.sum_mul_sum]

/-- C10-41: Δ(U) = 2(1 − (3 + t)/12) = (3/2)(1 − t/9) = (4/3)(1 − (t − 1)/8), t = |Tr U|², hence
κ_open ΣΔ = β_adj Σ(1 − χ₈/8) with β_adj = (4/3)κ_open; and |Tr(ωU)|² = |Tr U|² for |ω| = 1. -/
theorem wilson_coefficient (t κ : ℝ) :
    2 * (1 - (3 + t) / 12) = (3/2) * (1 - t / 9) ∧ (3/2) * (1 - t / 9) = (4/3) * (1 - (t - 1) / 8) ∧
      κ * ((4/3) * (1 - (t - 1) / 8)) = ((4/3) * κ) * (1 - (t - 1) / 8) := by
  refine ⟨by ring, by ring, by ring⟩

theorem center_invariance (ω T : ℂ) (hω : ω * star ω = 1) :
    (ω * T) * star (ω * T) = T * star T := by
  rw [star_mul', show ω * T * (star ω * star T) = (ω * star ω) * (T * star T) by ring, hω, one_mul]

/-! ### Kraus pairs and the averaged colour channel (C10-42, C10-43, C10-45, C10-46, C10-47) -/

section Kraus
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- C10-42: with orthogonal projectors P₁ + P₂ = I, K := (6/7)P₁ + P₂ = (20/21)((9/10)P₁ + (21/20)P₂)
and L := (√13/7)P₁ satisfy K*K + L*L = I; the scale 20/21 is the largest s with s·21/20 ≤ 1. -/
theorem throughput_pair (Q1 Q2 : Matrix n n ℂ) (h1 : Q1 * Q1 = Q1) (h2 : Q2 * Q2 = Q2) (h12 : Q1 * Q2 = 0)
    (h21 : Q2 * Q1 = 0) (hs : Q1 + Q2 = 1) :
    ((20/21 : ℂ) • ((9/10 : ℂ) • Q1 + (21/20 : ℂ) • Q2) = (6/7 : ℂ) • Q1 + Q2) ∧
      ((6/7 : ℂ) • Q1 + Q2) * ((6/7 : ℂ) • Q1 + Q2) +
        ((Real.sqrt 13 / 7 : ℝ) : ℂ) • Q1 * (((Real.sqrt 13 / 7 : ℝ) : ℂ) • Q1) = 1 := by
  constructor
  · rw [smul_add, smul_smul, smul_smul]; norm_num
  · have h13 : ((Real.sqrt 13 / 7 : ℝ) : ℂ) * ((Real.sqrt 13 / 7 : ℝ) : ℂ) = 13 / 49 := by
      rw [← Complex.ofReal_mul, div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]; push_cast; norm_num
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, h1, h2, h12, h21,
      smul_zero, add_zero, zero_add, smul_smul, h13]
    rw [← hs]; module

theorem throughput_max (s : ℝ) (hs : 0 < s) : s * (21/20) ≤ 1 ↔ s ≤ 20/21 := by
  constructor <;> intro h <;> linarith

/-- C10-43: for a Hermitian idempotent P, K_P = I − P/7 and L_P = (√13/7)P give K*K + L*L = I. -/
theorem rotated_kraus (P : Matrix n n ℂ) (hP : P * P = P) (hh : Pᴴ = P) :
    (1 - (1/7 : ℂ) • P)ᴴ * (1 - (1/7 : ℂ) • P) +
      (((Real.sqrt 13 / 7 : ℝ) : ℂ) • P)ᴴ * (((Real.sqrt 13 / 7 : ℝ) : ℂ) • P) = 1 := by
  have h13 : ((Real.sqrt 13 / 7 : ℝ) : ℂ) * ((Real.sqrt 13 / 7 : ℝ) : ℂ) = 13 / 49 := by
    rw [← Complex.ofReal_mul, div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]; push_cast; norm_num
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hh,
    Complex.star_def, Complex.conj_ofReal, map_div₀, map_one]
  rw [show (starRingEnd ℂ) 7 = 7 by rw [show (7:ℂ) = ((7:ℝ):ℂ) by push_cast; rfl, Complex.conj_ofReal]]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    hP, smul_smul, h13]
  module

/-- C10-45: averaging K_P X K_P* + L_P X L_P* with E[P] = I/3 and E[PXP] = (X + Tr X·I)/12 gives
(13/14)X + (1/42)Tr X·I; so t₈ = 13/14. -/
theorem averaged_channel (X : Matrix n n ℂ) :
    X - (1/7 : ℂ) • (X * ((1/3 : ℂ) • 1) + ((1/3 : ℂ) • 1) * X) +
        ((1/49 : ℂ) + 13/49) • ((1/12 : ℂ) • (X + X.trace • (1 : Matrix n n ℂ))) =
      (13/14 : ℂ) • X + (1/42 : ℂ) • (X.trace • (1 : Matrix n n ℂ)) := by
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_add, smul_smul]
  module

/-- C10-46: if the generators satisfy the completeness relations Σ_a T^a T^a = (4/3)I and
Σ_a T^a X T^a = ½(Tr X·I − X/3), then Σ_a [T^a,[T^a,X]] = 3X − Tr X·I (so 3X on traceless X, 0 on I). -/
theorem adjoint_casimir (T : Fin 8 → Matrix n n ℂ) (X : Matrix n n ℂ)
    (hTT : ∑ a, T a * T a = (4/3 : ℂ) • (1 : Matrix n n ℂ))
    (hTXT : ∑ a, T a * X * T a = (1/2 : ℂ) • (X.trace • (1 : Matrix n n ℂ) - (1/3 : ℂ) • X)) :
    ∑ a, (T a * (T a * X - X * T a) - (T a * X - X * T a) * T a) = 3 • X - X.trace • (1 : Matrix n n ℂ) := by
  have e : ∀ a, T a * (T a * X - X * T a) - (T a * X - X * T a) * T a =
      (T a * T a) * X - (2:ℂ) • (T a * X * T a) + X * (T a * T a) := by
    intro a; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, two_smul]; abel
  rw [Finset.sum_congr rfl (fun a _ => e a), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.smul_sum, hTT, hTXT]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_sub, smul_smul]
  rw [show (3 : ℕ) • X = (3 : ℂ) • X by norm_cast]
  module

theorem t8_exponent (τ : ℝ) (hτ : τ ≠ 0) :
    Real.exp (τ * (-(Real.log (14/13) / (3 * τ)) * 3)) = 13/14 := by
  rw [show τ * (-(Real.log (14/13) / (3 * τ)) * 3) = -Real.log (14/13) by field_simp]
  rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

end Kraus

/-- ln(14/13) = 0.0741079721…, from the alternating series of −ln(1 − 1/14). -/
theorem log_14_13 : 0.07410797215 < Real.log (14/13) ∧ Real.log (14/13) < 0.07410797216 := by
  have e : Real.log (14/13) = -Real.log (1 - 1/14) := by
    rw [show (1:ℝ) - 1/14 = (14/13)⁻¹ by norm_num, Real.log_inv, neg_neg]
  have hs := Real.abs_log_sub_add_sum_range_le (show |(1/14 : ℝ)| < 1 by norm_num) 10
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  rw [abs_le] at hs
  rw [e]
  constructor <;> norm_num <;> linarith [hs.1, hs.2]

/-- C10-47, C10-53: g²_{HK,step} = (2/3)ln(14/13) = 0.0494053148, and g²_{graph,HK} = 2√6 times it
= (4√6/3) ln(14/13) = 0.2420356…. -/
theorem heat_kernel_couplings :
    0.0494053147 < (2/3) * Real.log (14/13) ∧ (2/3) * Real.log (14/13) < 0.0494053148 ∧
      0.242035 < 2 * Real.sqrt 6 * ((2/3) * Real.log (14/13)) ∧
      2 * Real.sqrt 6 * ((2/3) * Real.log (14/13)) < 0.242036 := by
  obtain ⟨a, b⟩ := log_14_13
  have s1 : (2.449489742 : ℝ) < Real.sqrt 6 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s2 : Real.sqrt 6 < 2.449489743 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  refine ⟨by linarith, by linarith, by nlinarith, by nlinarith⟩

/-! ### Diamond lattice (C10-48, C10-50) and isotropy (C10-52), colour/shell commutation (C10-54) -/

/-- Tetrahedral bond vectors scaled by √3. -/
def tet : Fin 4 → Fin 3 → ℤ := ![![1, 1, 1], ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]

/-- C10-48: the diamond graph has no non-backtracking closed walk of length 2 or 4 (alternating
+n_i, −n_j steps with consecutive bonds distinct), and has one of length 6: girth 6. -/
theorem diamond_girth :
    (∀ i j : Fin 4, i ≠ j → ∃ c, tet i c - tet j c ≠ 0) ∧
    (∀ i1 j1 i2 j2 : Fin 4, i1 ≠ j1 → j1 ≠ i2 → i2 ≠ j2 → j2 ≠ i1 →
      ∃ c, tet i1 c - tet j1 c + tet i2 c - tet j2 c ≠ 0) ∧
    (∃ i1 j1 i2 j2 i3 j3 : Fin 4, i1 ≠ j1 ∧ j1 ≠ i2 ∧ i2 ≠ j2 ∧ j2 ≠ i3 ∧ i3 ≠ j3 ∧ j3 ≠ i1 ∧
      ∀ c, tet i1 c - tet j1 c + tet i2 c - tet j2 c + tet i3 c - tet j3 c = 0) := by
  refine ⟨by decide, by decide, ⟨0, 1, 2, 0, 1, 2, by decide⟩⟩

/-- In D × ℤ a spatial bond, a temporal step, the reversed bond and the reversed temporal step form a
4-cycle. -/
theorem diamond_time_square (i : Fin 4) :
    (∀ c, tet i c - tet i c = 0) ∧ (1 : ℤ) - 1 = 0 := ⟨fun c => sub_self _, sub_self _⟩

/-- C10-50: a_k = d(n₁ − n_{k+1}) has det = 16 in √3-units, so |det(a₁,a₂,a₃)| = 16d³/(3√3) and the
volume per site (two sites per cell) is 8d³/(3√3). -/
theorem diamond_cell :
    Matrix.det (Matrix.of fun k c => tet 0 c - tet (k.succ) c : Matrix (Fin 3) (Fin 3) ℤ) = 16 ∧
      ∀ d : ℝ, 16 * d ^ 3 / (Real.sqrt 3) ^ 3 = 16 * d ^ 3 / (3 * Real.sqrt 3) ∧
        (16 * d ^ 3 / (3 * Real.sqrt 3)) / 2 = 8 * d ^ 3 / (3 * Real.sqrt 3) := by
  refine ⟨by decide, fun d => ⟨?_, by ring⟩⟩
  rw [show (Real.sqrt 3) ^ 3 = Real.sqrt 3 ^ 2 * Real.sqrt 3 by ring, Real.sq_sqrt (by norm_num)]

/-- C10-52: g_E² = g_M² iff r = (4/3)√(1+ρ), and then g_iso² = 2√(3(1+ρ)) t_s; at ρ = 1,
r = 4√2/3 and g_iso²/t_s = 2√6. -/
theorem isotropy {ρ r t : ℝ} (hρ : 0 ≤ 1 + ρ) (hr : 0 < r) :
    (8 * Real.sqrt 3 / (3 * r) * (1 + ρ) * t = 3 * Real.sqrt 3 / 2 * r * t ∧ t ≠ 0 →
      r = 4 / 3 * Real.sqrt (1 + ρ)) ∧
    (r = 4 / 3 * Real.sqrt (1 + ρ) → 3 * Real.sqrt 3 / 2 * r * t = 2 * Real.sqrt (3 * (1 + ρ)) * t) := by
  have h3 : 0 < Real.sqrt 3 := by positivity
  constructor
  · rintro ⟨h, ht⟩
    have hr2 : r ^ 2 = 16 / 9 * (1 + ρ) := by
      field_simp at h
      nlinarith [h]
    have : r = Real.sqrt (16 / 9 * (1 + ρ)) := by
      rw [← hr2, Real.sqrt_sq hr.le]
    rw [this, Real.sqrt_mul (by norm_num), show Real.sqrt (16/9) = 4/3 by
      rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]; norm_num]
  · intro h; rw [h, Real.sqrt_mul (by norm_num) (1 + ρ)]; ring

theorem isotropy_rho_one :
    4 / 3 * Real.sqrt (1 + 1) = 4 * Real.sqrt 2 / 3 ∧ 2 * Real.sqrt (3 * (1 + 1)) = 2 * Real.sqrt 6 := by
  constructor <;> norm_num; ring

/-- C10-54: [K² ⊗ I₃, I ⊗ T^a] = 0. -/
theorem color_shell_commute {s : Type*} [Fintype s] [DecidableEq s] (K : Matrix s s ℂ)
    (T : Matrix (Fin 3) (Fin 3) ℂ) :
    (K ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)) * ((1 : Matrix s s ℂ) ⊗ₖ T) =
      ((1 : Matrix s s ℂ) ⊗ₖ T) * (K ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]; simp

/-- C10-34 (b): U and e^{iθ}U give the same conjugation channel. -/
theorem projective_channel {n : Type*} [Fintype n] [DecidableEq n] (U X : Matrix n n ℂ) (θ : ℝ) :
    (Complex.exp (θ * Complex.I) • U) * X * (Complex.exp (θ * Complex.I) • U)ᴴ = U * X * Uᴴ := by
  have hc : Complex.exp (θ * Complex.I) * star (Complex.exp (θ * Complex.I)) = 1 := by
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]; simp [Complex.conj_ofReal]
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm, hc,
    one_smul]

end Entropic.AppIJ
