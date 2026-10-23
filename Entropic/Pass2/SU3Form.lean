import Mathlib.Tactic

/-! Second pass, chunk 15: C10-38. A quadratic form on su(3) (traceless Hermitian 3 × 3 matrices) that is
invariant under conjugation by three unitaries (a cyclic permutation, diag(i, 1, 1) and a rational rotation
in the 12-plane) is a multiple of Tr(X²). Invariance under all of U(3) is a stronger hypothesis.

Coordinates: X(v) = Σ_k v_k B_k with B the real basis of off-diagonal symmetric, off-diagonal
antisymmetric-imaginary, diag(1, −1, 0) and diag(1, 1, −2); Ad_U is the matrix of X ↦ U X U* in
these coordinates (`conj_coords`), and Tr(X(v) X(w)) = vᵀ G w with G = diag(2, 2, 2, 2, 2, 2, 2, 6). -/

namespace Entropic.Pass2.SU3Form
open Matrix Complex

noncomputable section

def B : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ := ![
  !![0, 1, 0; 1, 0, 0; 0, 0, 0], !![0, -I, 0; I, 0, 0; 0, 0, 0],
  !![0, 0, 1; 0, 0, 0; 1, 0, 0], !![0, 0, -I; 0, 0, 0; I, 0, 0],
  !![0, 0, 0; 0, 0, 1; 0, 1, 0], !![0, 0, 0; 0, 0, -I; 0, I, 0],
  !![1, 0, 0; 0, -1, 0; 0, 0, 0], !![1, 0, 0; 0, 1, 0; 0, 0, -2]]

def Xv (v : Fin 8 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ := ∑ k, (v k : ℂ) • B k

def Uc : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]
def Ud : Matrix (Fin 3) (Fin 3) ℂ := !![I, 0, 0; 0, 1, 0; 0, 0, 1]
def Ur : Matrix (Fin 3) (Fin 3) ℂ := !![3/5, -4/5, 0; 4/5, 3/5, 0; 0, 0, 1]

def AdC : Matrix (Fin 8) (Fin 8) ℝ := Matrix.of ![![(0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (-1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-1:ℝ), (0:ℝ), (0:ℝ)], ![(1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-1:ℝ)/2), ((-3:ℝ)/2)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((1:ℝ)/2), ((-1:ℝ)/2)]]
def AdD : Matrix (Fin 8) (Fin 8) ℝ := Matrix.of ![![(0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(-1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (-1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ)]]
def AdR : Matrix (Fin 8) (Fin 8) ℝ := Matrix.of ![![((-7:ℝ)/25), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((24:ℝ)/25), (0:ℝ)], ![(0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), ((3:ℝ)/5), (0:ℝ), ((-4:ℝ)/5), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), ((3:ℝ)/5), (0:ℝ), ((-4:ℝ)/5), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), ((4:ℝ)/5), (0:ℝ), ((3:ℝ)/5), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), ((4:ℝ)/5), (0:ℝ), ((3:ℝ)/5), (0:ℝ), (0:ℝ)], ![((-24:ℝ)/25), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-7:ℝ)/25), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ)]]
def Gm : Matrix (Fin 8) (Fin 8) ℝ := diagonal ![2, 2, 2, 2, 2, 2, 2, 6]

set_option maxHeartbeats 0 in
/-- The coordinate matrices are the adjoint actions: U X(v) U* = X(Ad_U v). -/
theorem conj_coords (v : Fin 8 → ℝ) :
    Uc * Xv v * Ucᴴ = Xv (AdC *ᵥ v) ∧ Ud * Xv v * Udᴴ = Xv (AdD *ᵥ v) ∧ Ur * Xv v * Urᴴ = Xv (AdR *ᵥ v) := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Xv, B, Uc, Ud, Ur, AdC, AdD, AdR, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.mulVec, dotProduct,
      Matrix.conjTranspose_apply, Matrix.sum_apply, map_ofNat, map_div₀, map_inv₀, map_neg] <;> ring_nf <;> (try simp [I_sq]) <;> (try push_cast) <;> (try ring_nf)

set_option maxHeartbeats 0 in
/-- Tr(X(v) X(w)) = vᵀ G w. -/
theorem trace_form (v w : Fin 8 → ℝ) : (Xv v * Xv w).trace = ((v ⬝ᵥ (Gm *ᵥ w) : ℝ) : ℂ) := by
  simp [Xv, B, Gm, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.mulVec, dotProduct,
    Matrix.sum_apply, Matrix.diagonal_apply]
  ring_nf; simp [I_sq]; push_cast; ring_nf

set_option maxHeartbeats 0 in
/-- C10-38 (matrix form): a symmetric M with Ad_Uᵀ M Ad_U = M for the three unitaries is (M₀₀/2)·G. -/
theorem invariant_form_unique (M : Matrix (Fin 8) (Fin 8) ℝ) (hS : Mᵀ = M)
    (hC : AdCᵀ * M * AdC = M) (hD : AdDᵀ * M * AdD = M) (hR : AdRᵀ * M * AdR = M) :
    M = (M 0 0 / 2) • Gm := by
  have f_0_1 : M 0 1 = 0 := by
      have q0 := congrFun (congrFun hR 0) 1
      have q1 := congrFun (congrFun hD 6) 1
      have q2 := congrFun (congrFun hD 6) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-25:ℝ)/32)) * q0 + (((3:ℝ)/8)) * q1 + (((3:ℝ)/8)) * q2
  have f_0_2 : M 0 2 = 0 := by
      have q0 := congrFun (congrFun hD 0) 2
      have q1 := congrFun (congrFun hD 2) 5
      have q2 := congrFun (congrFun hC 2) 5
      have q3 := congrFun (congrFun hC 3) 5
      have q4 := congrFun (congrFun hD 0) 3
      have q5 := congrFun (congrFun hD 2) 4
      have q6 := congrFun (congrFun hC 2) 4
      have q7 := congrFun (congrFun hC 3) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((-1:ℝ)/2)) * q1 + (((1:ℝ)/2)) * q2 + (((1:ℝ)/2)) * q3 + (((-1:ℝ)/2)) * q4 + (((-1:ℝ)/2)) * q5 + (((1:ℝ)/2)) * q6 + (((1:ℝ)/2)) * q7
  have f_0_3 : M 0 3 = 0 := by
      have q0 := congrFun (congrFun hD 0) 3
      have q1 := congrFun (congrFun hD 2) 4
      have q2 := congrFun (congrFun hC 2) 4
      have q3 := congrFun (congrFun hC 3) 4
      have q4 := congrFun (congrFun hD 0) 2
      have q5 := congrFun (congrFun hD 2) 5
      have q6 := congrFun (congrFun hC 2) 5
      have q7 := congrFun (congrFun hC 3) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((-1:ℝ)/2)) * q1 + (((1:ℝ)/2)) * q2 + (((1:ℝ)/2)) * q3 + (((1:ℝ)/2)) * q4 + (((1:ℝ)/2)) * q5 + (((-1:ℝ)/2)) * q6 + (((-1:ℝ)/2)) * q7
  have f_0_4 : M 0 4 = 0 := by
      have q0 := congrFun (congrFun hD 0) 4
      have q1 := congrFun (congrFun hD 1) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((1:ℝ)/2)) * q1
  have f_0_5 : M 0 5 = 0 := by
      have q0 := congrFun (congrFun hD 0) 5
      have q1 := congrFun (congrFun hD 1) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((1:ℝ)/2)) * q1
  have f_0_6 : M 0 6 = 0 := by
      have q0 := congrFun (congrFun hD 0) 6
      have q1 := congrFun (congrFun hD 1) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((1:ℝ)/2)) * q1
  have f_0_7 : M 0 7 = 0 := by
      have q0 := congrFun (congrFun hD 0) 7
      have q1 := congrFun (congrFun hD 1) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((1:ℝ)/2)) * q1
  have f_1_0 : M 1 0 = 0 := by
      have q0 := congrFun (congrFun hR 0) 1
      have q1 := congrFun (congrFun hD 0) 1
      have q2 := congrFun (congrFun hD 6) 1
      have q3 := congrFun (congrFun hD 6) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((25:ℝ)/32)) * q0 + ((-1:ℝ)) * q1 + (((-3:ℝ)/8)) * q2 + (((-3:ℝ)/8)) * q3
  have f_1_1 : M 1 1 = ((1:ℝ)) * M 0 0 := by
      have q0 := congrFun (congrFun hD 0) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) ((1:ℝ)) * q0
  have f_1_2 : M 1 2 = 0 := by
      have q0 := congrFun (congrFun hD 2) 4
      have q1 := congrFun (congrFun hC 2) 4
      have q2 := congrFun (congrFun hC 3) 4
      have q3 := congrFun (congrFun hD 0) 2
      have q4 := congrFun (congrFun hD 2) 5
      have q5 := congrFun (congrFun hC 2) 5
      have q6 := congrFun (congrFun hC 3) 5
      have q7 := congrFun (congrFun hD 0) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((1:ℝ)/2)) * q0 + (((-1:ℝ)/2)) * q1 + (((-1:ℝ)/2)) * q2 + (((-1:ℝ)/2)) * q3 + (((-1:ℝ)/2)) * q4 + (((1:ℝ)/2)) * q5 + (((1:ℝ)/2)) * q6 + (((-1:ℝ)/2)) * q7
  have f_1_3 : M 1 3 = 0 := by
      have q0 := congrFun (congrFun hD 2) 5
      have q1 := congrFun (congrFun hC 2) 5
      have q2 := congrFun (congrFun hC 3) 5
      have q3 := congrFun (congrFun hD 0) 3
      have q4 := congrFun (congrFun hD 2) 4
      have q5 := congrFun (congrFun hC 2) 4
      have q6 := congrFun (congrFun hC 3) 4
      have q7 := congrFun (congrFun hD 0) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((1:ℝ)/2)) * q1 + (((1:ℝ)/2)) * q2 + (((-1:ℝ)/2)) * q3 + (((-1:ℝ)/2)) * q4 + (((1:ℝ)/2)) * q5 + (((1:ℝ)/2)) * q6 + (((1:ℝ)/2)) * q7
  have f_1_4 : M 1 4 = 0 := by
      have q0 := congrFun (congrFun hD 1) 4
      have q1 := congrFun (congrFun hD 0) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((-1:ℝ)/2)) * q1
  have f_1_5 : M 1 5 = 0 := by
      have q0 := congrFun (congrFun hD 1) 5
      have q1 := congrFun (congrFun hD 0) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((-1:ℝ)/2)) * q1
  have f_1_6 : M 1 6 = 0 := by
      have q0 := congrFun (congrFun hD 1) 6
      have q1 := congrFun (congrFun hD 0) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((-1:ℝ)/2)) * q1
  have f_1_7 : M 1 7 = 0 := by
      have q0 := congrFun (congrFun hD 1) 7
      have q1 := congrFun (congrFun hD 0) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((-1:ℝ)/2)) * q1
  have f_2_0 : M 2 0 = 0 := by
      have q0 := congrFun (congrFun hC 2) 0
      have q1 := congrFun (congrFun hD 0) 4
      have q2 := congrFun (congrFun hD 1) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) ((-1:ℝ)) * q0 + (((-1:ℝ)/2)) * q1 + (((1:ℝ)/2)) * q2
  have f_2_1 : M 2 1 = 0 := by
      have q0 := congrFun (congrFun hC 2) 1
      have q1 := congrFun (congrFun hD 0) 5
      have q2 := congrFun (congrFun hD 1) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) ((-1:ℝ)) * q0 + (((-1:ℝ)/2)) * q1 + (((1:ℝ)/2)) * q2
  have f_2_2 : M 2 2 = ((1:ℝ)) * M 0 0 := by
      have q0 := congrFun (congrFun hC 2) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) ((-1:ℝ)) * q0
  have f_2_3 : M 2 3 = 0 := by
      have q0 := congrFun (congrFun hC 2) 3
      have q1 := congrFun (congrFun hR 0) 1
      have q2 := congrFun (congrFun hD 6) 1
      have q3 := congrFun (congrFun hD 6) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) ((-1:ℝ)) * q0 + (((25:ℝ)/32)) * q1 + (((-3:ℝ)/8)) * q2 + (((-3:ℝ)/8)) * q3
  have f_2_4 : M 2 4 = 0 := by
      have q0 := congrFun (congrFun hC 2) 4
      have q1 := congrFun (congrFun hD 0) 2
      have q2 := congrFun (congrFun hD 2) 5
      have q3 := congrFun (congrFun hC 2) 5
      have q4 := congrFun (congrFun hC 3) 5
      have q5 := congrFun (congrFun hD 0) 3
      have q6 := congrFun (congrFun hD 2) 4
      have q7 := congrFun (congrFun hC 3) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((-1:ℝ)/2)) * q1 + (((-1:ℝ)/2)) * q2 + (((1:ℝ)/2)) * q3 + (((1:ℝ)/2)) * q4 + (((-1:ℝ)/2)) * q5 + (((-1:ℝ)/2)) * q6 + (((1:ℝ)/2)) * q7
  have f_2_5 : M 2 5 = 0 := by
      have q0 := congrFun (congrFun hC 2) 5
      have q1 := congrFun (congrFun hD 0) 3
      have q2 := congrFun (congrFun hD 2) 4
      have q3 := congrFun (congrFun hC 2) 4
      have q4 := congrFun (congrFun hC 3) 4
      have q5 := congrFun (congrFun hD 0) 2
      have q6 := congrFun (congrFun hD 2) 5
      have q7 := congrFun (congrFun hC 3) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((1:ℝ)/2)) * q1 + (((1:ℝ)/2)) * q2 + (((-1:ℝ)/2)) * q3 + (((-1:ℝ)/2)) * q4 + (((-1:ℝ)/2)) * q5 + (((-1:ℝ)/2)) * q6 + (((1:ℝ)/2)) * q7
  have f_2_6 : M 2 6 = 0 := by
      have q0 := congrFun (congrFun hD 2) 6
      have q1 := congrFun (congrFun hD 3) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((1:ℝ)/2)) * q1
  have f_2_7 : M 2 7 = 0 := by
      have q0 := congrFun (congrFun hD 2) 7
      have q1 := congrFun (congrFun hD 3) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((1:ℝ)/2)) * q1
  have f_3_0 : M 3 0 = 0 := by
      have q0 := congrFun (congrFun hC 3) 0
      have q1 := congrFun (congrFun hD 1) 4
      have q2 := congrFun (congrFun hD 0) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) ((-1:ℝ)) * q0 + (((1:ℝ)/2)) * q1 + (((1:ℝ)/2)) * q2
  have f_3_1 : M 3 1 = 0 := by
      have q0 := congrFun (congrFun hC 3) 1
      have q1 := congrFun (congrFun hD 1) 5
      have q2 := congrFun (congrFun hD 0) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) ((-1:ℝ)) * q0 + (((1:ℝ)/2)) * q1 + (((1:ℝ)/2)) * q2
  have f_3_2 : M 3 2 = 0 := by
      have q0 := congrFun (congrFun hC 3) 2
      have q1 := congrFun (congrFun hR 0) 1
      have q2 := congrFun (congrFun hD 0) 1
      have q3 := congrFun (congrFun hD 6) 1
      have q4 := congrFun (congrFun hD 6) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) ((-1:ℝ)) * q0 + (((-25:ℝ)/32)) * q1 + ((1:ℝ)) * q2 + (((3:ℝ)/8)) * q3 + (((3:ℝ)/8)) * q4
  have f_3_3 : M 3 3 = ((1:ℝ)) * M 0 0 := by
      have q0 := congrFun (congrFun hC 3) 3
      have q1 := congrFun (congrFun hD 0) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) ((-1:ℝ)) * q0 + ((1:ℝ)) * q1
  have f_3_4 : M 3 4 = 0 := by
      have q0 := congrFun (congrFun hD 2) 4
      have q1 := congrFun (congrFun hC 2) 4
      have q2 := congrFun (congrFun hD 0) 2
      have q3 := congrFun (congrFun hD 2) 5
      have q4 := congrFun (congrFun hC 2) 5
      have q5 := congrFun (congrFun hC 3) 5
      have q6 := congrFun (congrFun hD 0) 3
      have q7 := congrFun (congrFun hC 3) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((1:ℝ)/2)) * q1 + (((1:ℝ)/2)) * q2 + (((1:ℝ)/2)) * q3 + (((-1:ℝ)/2)) * q4 + (((-1:ℝ)/2)) * q5 + (((1:ℝ)/2)) * q6 + (((-1:ℝ)/2)) * q7
  have f_3_5 : M 3 5 = 0 := by
      have q0 := congrFun (congrFun hC 3) 5
      have q1 := congrFun (congrFun hD 2) 5
      have q2 := congrFun (congrFun hC 2) 5
      have q3 := congrFun (congrFun hD 0) 3
      have q4 := congrFun (congrFun hD 2) 4
      have q5 := congrFun (congrFun hC 2) 4
      have q6 := congrFun (congrFun hC 3) 4
      have q7 := congrFun (congrFun hD 0) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((-1:ℝ)/2)) * q1 + (((1:ℝ)/2)) * q2 + (((-1:ℝ)/2)) * q3 + (((-1:ℝ)/2)) * q4 + (((1:ℝ)/2)) * q5 + (((1:ℝ)/2)) * q6 + (((1:ℝ)/2)) * q7
  have f_3_6 : M 3 6 = 0 := by
      have q0 := congrFun (congrFun hD 3) 6
      have q1 := congrFun (congrFun hD 2) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((-1:ℝ)/2)) * q1
  have f_3_7 : M 3 7 = 0 := by
      have q0 := congrFun (congrFun hD 3) 7
      have q1 := congrFun (congrFun hD 2) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((-1:ℝ)/2)) * q1
  have f_4_2 : M 4 2 = 0 := by
      have q0 := congrFun (congrFun hD 0) 4
      have q1 := congrFun (congrFun hC 0) 4
      have q2 := congrFun (congrFun hD 1) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + ((1:ℝ)) * q1 + (((1:ℝ)/2)) * q2
  have f_4_3 : M 4 3 = 0 := by
      have q0 := congrFun (congrFun hD 0) 5
      have q1 := congrFun (congrFun hC 0) 5
      have q2 := congrFun (congrFun hD 1) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((1:ℝ)/2)) * q0 + ((-1:ℝ)) * q1 + (((-1:ℝ)/2)) * q2
  have f_4_4 : M 4 4 = ((1:ℝ)) * M 0 0 := by
      have q0 := congrFun (congrFun hC 0) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) ((1:ℝ)) * q0
  have f_4_5 : M 4 5 = 0 := by
      have q0 := congrFun (congrFun hC 0) 1
      have q1 := congrFun (congrFun hR 0) 1
      have q2 := congrFun (congrFun hD 6) 1
      have q3 := congrFun (congrFun hD 6) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) ((1:ℝ)) * q0 + (((-25:ℝ)/32)) * q1 + (((3:ℝ)/8)) * q2 + (((3:ℝ)/8)) * q3
  have f_4_6 : M 4 6 = 0 := by
      have q0 := congrFun (congrFun hC 0) 6
      have q1 := congrFun (congrFun hD 0) 6
      have q2 := congrFun (congrFun hD 1) 6
      have q3 := congrFun (congrFun hR 2) 7
      have q4 := congrFun (congrFun hD 2) 7
      have q5 := congrFun (congrFun hD 3) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) ((-2:ℝ)) * q0 + ((1:ℝ)) * q1 + ((-1:ℝ)) * q2 + (((5:ℝ)/4)) * q3 + (((-1:ℝ)/4)) * q4 + (((1:ℝ)/4)) * q5
  have f_4_7 : M 4 7 = 0 := by
      have q0 := congrFun (congrFun hR 2) 7
      have q1 := congrFun (congrFun hD 2) 7
      have q2 := congrFun (congrFun hD 3) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((5:ℝ)/4)) * q0 + (((-1:ℝ)/4)) * q1 + (((1:ℝ)/4)) * q2
  have f_5_2 : M 5 2 = 0 := by
      have q0 := congrFun (congrFun hD 1) 4
      have q1 := congrFun (congrFun hC 1) 4
      have q2 := congrFun (congrFun hD 0) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + ((1:ℝ)) * q1 + (((-1:ℝ)/2)) * q2
  have f_5_3 : M 5 3 = 0 := by
      have q0 := congrFun (congrFun hD 1) 5
      have q1 := congrFun (congrFun hC 1) 5
      have q2 := congrFun (congrFun hD 0) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((1:ℝ)/2)) * q0 + ((-1:ℝ)) * q1 + (((1:ℝ)/2)) * q2
  have f_5_4 : M 5 4 = 0 := by
      have q0 := congrFun (congrFun hR 0) 1
      have q1 := congrFun (congrFun hD 0) 1
      have q2 := congrFun (congrFun hC 1) 0
      have q3 := congrFun (congrFun hD 6) 1
      have q4 := congrFun (congrFun hD 6) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((25:ℝ)/32)) * q0 + ((-1:ℝ)) * q1 + ((1:ℝ)) * q2 + (((-3:ℝ)/8)) * q3 + (((-3:ℝ)/8)) * q4
  have f_5_5 : M 5 5 = ((1:ℝ)) * M 0 0 := by
      have q0 := congrFun (congrFun hD 0) 0
      have q1 := congrFun (congrFun hC 1) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) ((1:ℝ)) * q0 + ((1:ℝ)) * q1
  have f_5_6 : M 5 6 = 0 := by
      have q0 := congrFun (congrFun hC 1) 6
      have q1 := congrFun (congrFun hD 1) 6
      have q2 := congrFun (congrFun hD 0) 6
      have q3 := congrFun (congrFun hR 3) 7
      have q4 := congrFun (congrFun hD 3) 7
      have q5 := congrFun (congrFun hD 2) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) ((-2:ℝ)) * q0 + ((1:ℝ)) * q1 + ((1:ℝ)) * q2 + (((5:ℝ)/4)) * q3 + (((-1:ℝ)/4)) * q4 + (((-1:ℝ)/4)) * q5
  have f_5_7 : M 5 7 = 0 := by
      have q0 := congrFun (congrFun hR 3) 7
      have q1 := congrFun (congrFun hD 3) 7
      have q2 := congrFun (congrFun hD 2) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((5:ℝ)/4)) * q0 + (((-1:ℝ)/4)) * q1 + (((-1:ℝ)/4)) * q2
  have f_6_0 : M 6 0 = 0 := by
      have q0 := congrFun (congrFun hD 6) 0
      have q1 := congrFun (congrFun hD 6) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((1:ℝ)/2)) * q1
  have f_6_1 : M 6 1 = 0 := by
      have q0 := congrFun (congrFun hD 6) 1
      have q1 := congrFun (congrFun hD 6) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((-1:ℝ)/2)) * q1
  have f_6_2 : M 6 2 = 0 := by
      have q0 := congrFun (congrFun hD 6) 2
      have q1 := congrFun (congrFun hD 6) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((1:ℝ)/2)) * q1
  have f_6_3 : M 6 3 = 0 := by
      have q0 := congrFun (congrFun hD 6) 3
      have q1 := congrFun (congrFun hD 6) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((-1:ℝ)/2)) * q1
  have f_6_4 : M 6 4 = 0 := by
      have q0 := congrFun (congrFun hC 0) 6
      have q1 := congrFun (congrFun hD 0) 6
      have q2 := congrFun (congrFun hD 1) 6
      have q3 := congrFun (congrFun hS 4) 6
      have q4 := congrFun (congrFun hR 2) 7
      have q5 := congrFun (congrFun hD 2) 7
      have q6 := congrFun (congrFun hD 3) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) ((-2:ℝ)) * q0 + ((1:ℝ)) * q1 + ((-1:ℝ)) * q2 + ((1:ℝ)) * q3 + (((5:ℝ)/4)) * q4 + (((-1:ℝ)/4)) * q5 + (((1:ℝ)/4)) * q6
  have f_6_5 : M 6 5 = 0 := by
      have q0 := congrFun (congrFun hC 1) 6
      have q1 := congrFun (congrFun hD 1) 6
      have q2 := congrFun (congrFun hD 0) 6
      have q3 := congrFun (congrFun hS 5) 6
      have q4 := congrFun (congrFun hR 3) 7
      have q5 := congrFun (congrFun hD 3) 7
      have q6 := congrFun (congrFun hD 2) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) ((-2:ℝ)) * q0 + ((1:ℝ)) * q1 + ((1:ℝ)) * q2 + ((1:ℝ)) * q3 + (((5:ℝ)/4)) * q4 + (((-1:ℝ)/4)) * q5 + (((-1:ℝ)/4)) * q6
  have f_6_6 : M 6 6 = ((1:ℝ)) * M 0 0 := by
      have q0 := congrFun (congrFun hR 0) 0
      have q1 := congrFun (congrFun hD 0) 6
      have q2 := congrFun (congrFun hD 1) 6
      have q3 := congrFun (congrFun hD 6) 0
      have q4 := congrFun (congrFun hD 6) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((625:ℝ)/576)) * q0 + (((7:ℝ)/48)) * q1 + (((-7:ℝ)/48)) * q2 + (((7:ℝ)/48)) * q3 + (((-7:ℝ)/48)) * q4
  have f_6_7 : M 6 7 = 0 := by
      have q0 := congrFun (congrFun hR 0) 7
      have q1 := congrFun (congrFun hD 0) 7
      have q2 := congrFun (congrFun hD 1) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-25:ℝ)/24)) * q0 + (((2:ℝ)/3)) * q1 + (((-2:ℝ)/3)) * q2
  have f_7_0 : M 7 0 = 0 := by
      have q0 := congrFun (congrFun hD 7) 0
      have q1 := congrFun (congrFun hD 7) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((1:ℝ)/2)) * q1
  have f_7_1 : M 7 1 = 0 := by
      have q0 := congrFun (congrFun hD 7) 1
      have q1 := congrFun (congrFun hD 7) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((-1:ℝ)/2)) * q1
  have f_7_2 : M 7 2 = 0 := by
      have q0 := congrFun (congrFun hD 7) 2
      have q1 := congrFun (congrFun hD 7) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((1:ℝ)/2)) * q1
  have f_7_3 : M 7 3 = 0 := by
      have q0 := congrFun (congrFun hD 7) 3
      have q1 := congrFun (congrFun hD 7) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-1:ℝ)/2)) * q0 + (((-1:ℝ)/2)) * q1
  have f_7_4 : M 7 4 = 0 := by
      have q0 := congrFun (congrFun hR 7) 2
      have q1 := congrFun (congrFun hD 7) 2
      have q2 := congrFun (congrFun hD 7) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((5:ℝ)/4)) * q0 + (((-1:ℝ)/4)) * q1 + (((1:ℝ)/4)) * q2
  have f_7_5 : M 7 5 = 0 := by
      have q0 := congrFun (congrFun hR 7) 3
      have q1 := congrFun (congrFun hD 7) 3
      have q2 := congrFun (congrFun hD 7) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((5:ℝ)/4)) * q0 + (((-1:ℝ)/4)) * q1 + (((-1:ℝ)/4)) * q2
  have f_7_6 : M 7 6 = 0 := by
      have q0 := congrFun (congrFun hR 7) 0
      have q1 := congrFun (congrFun hD 7) 0
      have q2 := congrFun (congrFun hD 7) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) (((-25:ℝ)/24)) * q0 + (((2:ℝ)/3)) * q1 + (((-2:ℝ)/3)) * q2
  have f_4_0 : M 4 0 = 0 := by
      have q0 := congrFun (congrFun hC 0) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) ((1:ℝ)) * q0 + ((1:ℝ)) * f_0_2
  have f_4_1 : M 4 1 = 0 := by
      have q0 := congrFun (congrFun hC 0) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) ((-1:ℝ)) * q0 + ((-1:ℝ)) * f_0_3
  have f_5_0 : M 5 0 = 0 := by
      have q0 := congrFun (congrFun hC 1) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) ((1:ℝ)) * q0 + ((1:ℝ)) * f_1_2
  have f_5_1 : M 5 1 = 0 := by
      have q0 := congrFun (congrFun hC 1) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) ((-1:ℝ)) * q0 + ((-1:ℝ)) * f_1_3
  have f_7_7 : M 7 7 = ((3:ℝ)) * M 0 0 := by
      have q1 := congrFun (congrFun hC 6) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, AdC, AdD, AdR] <;> ring_nf)) ((3:ℝ)) * f_6_6 + ((4:ℝ)) * q1 + ((1:ℝ)) * f_6_7 + ((1:ℝ)) * f_7_6
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Gm, Matrix.smul_apply, Matrix.diagonal_apply, f_0_1, f_0_2, f_0_3, f_0_4, f_0_5, f_0_6, f_0_7, f_1_0, f_1_1, f_1_2, f_1_3, f_1_4, f_1_5, f_1_6, f_1_7, f_2_0, f_2_1, f_2_2, f_2_3, f_2_4, f_2_5, f_2_6, f_2_7, f_3_0, f_3_1, f_3_2, f_3_3, f_3_4, f_3_5, f_3_6, f_3_7, f_4_2, f_4_3, f_4_4, f_4_5, f_4_6, f_4_7, f_5_2, f_5_3, f_5_4, f_5_5, f_5_6, f_5_7, f_6_0, f_6_1, f_6_2, f_6_3, f_6_4, f_6_5, f_6_6, f_6_7, f_7_0, f_7_1, f_7_2, f_7_3, f_7_4, f_7_5, f_7_6, f_4_0, f_4_1, f_5_0, f_5_1, f_7_7] <;> ring

/-- Polarization: equal quadratic forms of two symmetric matrices force equality. -/
theorem polarize (S T : Matrix (Fin 8) (Fin 8) ℝ) (hS : Sᵀ = S) (hT : Tᵀ = T)
    (h : ∀ v, v ⬝ᵥ (S *ᵥ v) = v ⬝ᵥ (T *ᵥ v)) : S = T := by
  ext i j
  have hi := h (Pi.single i 1); have hj := h (Pi.single j 1); have hij := h (Pi.single i 1 + Pi.single j 1)
  simp [Matrix.mulVec_add, Matrix.add_mulVec, dotProduct_add, add_dotProduct, Matrix.mulVec_single,
    dotProduct_single, single_dotProduct] at hi hj hij
  have sij : S j i = S i j := by simpa [Matrix.transpose_apply] using congrFun (congrFun hS i) j
  have tij : T j i = T i j := by simpa [Matrix.transpose_apply] using congrFun (congrFun hT i) j
  linarith

/-- C10-38: a quadratic form q(X(v)) = vᵀ M v (M symmetric) on su(3), invariant under X ↦ U X U* for
U = Uc, Ud, Ur, is c · Tr(X²) with c = M₀₀/2. -/
theorem su3_invariant_form (M : Matrix (Fin 8) (Fin 8) ℝ) (hS : Mᵀ = M)
    (hinv : ∀ v, (AdC *ᵥ v) ⬝ᵥ (M *ᵥ (AdC *ᵥ v)) = v ⬝ᵥ (M *ᵥ v) ∧
      (AdD *ᵥ v) ⬝ᵥ (M *ᵥ (AdD *ᵥ v)) = v ⬝ᵥ (M *ᵥ v) ∧ (AdR *ᵥ v) ⬝ᵥ (M *ᵥ (AdR *ᵥ v)) = v ⬝ᵥ (M *ᵥ v)) :
    ∀ v, ((v ⬝ᵥ (M *ᵥ v) : ℝ) : ℂ) = ((M 0 0 / 2 : ℝ) : ℂ) * (Xv v * Xv v).trace := by
  have key : ∀ A : Matrix (Fin 8) (Fin 8) ℝ, (∀ v, (A *ᵥ v) ⬝ᵥ (M *ᵥ (A *ᵥ v)) = v ⬝ᵥ (M *ᵥ v)) →
      Aᵀ * M * A = M := by
    intro A hA
    apply polarize _ _ (by rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hS,
      Matrix.mul_assoc]) hS
    intro v
    rw [← hA v, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hM := invariant_form_unique M hS (key _ (fun v => (hinv v).1)) (key _ (fun v => (hinv v).2.1))
    (key _ (fun v => (hinv v).2.2))
  intro v
  rw [trace_form]
  conv_lhs => rw [hM]
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  push_cast; ring

end

end Entropic.Pass2.SU3Form
