import Mathlib.Tactic

/-! Second pass, chunk 15: C14-73 (a). In the ladder basis of V_{3/2} ⊗ V_{3/2}, a matrix commuting with
H ⊗ J₊, J₊ ⊗ H and J₋ ⊗ J₋ is a scalar; these three lie in the complex span of the nine J_a ⊗ J_b, so
the commutant of {J_a ⊗ J_b} is C·I. -/

namespace Entropic.Pass2.PairGen
open Matrix

def G1 : Matrix (Fin 16) (Fin 16) ℂ := Matrix.of ![![0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def G2 : Matrix (Fin 16) (Fin 16) ℂ := Matrix.of ![![0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def G3 : Matrix (Fin 16) (Fin 16) ℂ := Matrix.of ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- C14-73 (a): the commutant of {J_a ⊗ J_b} in M₁₆ is one-dimensional. -/
theorem bilinear_commutant (X : Matrix (Fin 16) (Fin 16) ℂ) (h1 : X * G1 = G1 * X) (h2 : X * G2 = G2 * X)
    (h3 : X * G3 = G3 * X) : X = X 0 0 • 1 := by
  have f_0_1 : X 0 1 = 0 := by
      have q0 := congrFun (congrFun h1 0) 2
      have q1 := congrFun (congrFun h1 1) 3
      have q2 := congrFun (congrFun h3 7) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0 + ((1:ℂ)/3) * q1 + ((-1:ℂ)/9) * q2
  have f_0_2 : X 0 2 = 0 := by
      have q0 := congrFun (congrFun h1 0) 3
      have q1 := congrFun (congrFun h3 6) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0 + ((-1:ℂ)/12) * q1
  have f_0_3 : X 0 3 = 0 := by
      have q0 := congrFun (congrFun h3 5) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/9) * q0
  have f_0_4 : X 0 4 = 0 := by
      have q0 := congrFun (congrFun h1 0) 5
      have q1 := congrFun (congrFun h3 1) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0 + ((1:ℂ)/3) * q1
  have f_0_5 : X 0 5 = 0 := by
      have q0 := congrFun (congrFun h3 0) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_0_6 : X 0 6 = 0 := by
      have q0 := congrFun (congrFun h3 0) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_0_7 : X 0 7 = 0 := by
      have q0 := congrFun (congrFun h3 0) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_0_8 : X 0 8 = 0 := by
      have q0 := congrFun (congrFun h1 0) 9
      have q1 := congrFun (congrFun h3 1) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0 + ((-1:ℂ)/4) * q1
  have f_0_9 : X 0 9 = 0 := by
      have q0 := congrFun (congrFun h3 0) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_0_10 : X 0 10 = 0 := by
      have q0 := congrFun (congrFun h3 0) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/16) * q0
  have f_0_11 : X 0 11 = 0 := by
      have q0 := congrFun (congrFun h3 0) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_0_12 : X 0 12 = 0 := by
      have q0 := congrFun (congrFun h3 5) 12
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/9) * q0
  have f_0_13 : X 0 13 = 0 := by
      have q0 := congrFun (congrFun h3 0) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_0_14 : X 0 14 = 0 := by
      have q0 := congrFun (congrFun h3 0) 9
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_0_15 : X 0 15 = 0 := by
      have q0 := congrFun (congrFun h3 0) 10
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_1_0 : X 1 0 = 0 := by
      have q0 := congrFun (congrFun h1 0) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_1_1 : X 1 1 = X 0 0 := by
      have q0 := congrFun (congrFun h1 0) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_1_2 : X 1 2 = 0 := by
      have q0 := congrFun (congrFun h1 1) 3
      have q1 := congrFun (congrFun h3 7) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0 + ((-1:ℂ)/9) * q1
  have f_1_3 : X 1 3 = 0 := by
      have q0 := congrFun (congrFun h3 6) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/12) * q0
  have f_1_4 : X 1 4 = 0 := by
      have q0 := congrFun (congrFun h1 0) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_1_5 : X 1 5 = 0 := by
      have q0 := congrFun (congrFun h3 1) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_1_6 : X 1 6 = 0 := by
      have q0 := congrFun (congrFun h3 1) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_1_7 : X 1 7 = 0 := by
      have q0 := congrFun (congrFun h3 1) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_1_8 : X 1 8 = 0 := by
      have q0 := congrFun (congrFun h1 0) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_1_9 : X 1 9 = 0 := by
      have q0 := congrFun (congrFun h3 1) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_1_10 : X 1 10 = 0 := by
      have q0 := congrFun (congrFun h3 1) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/16) * q0
  have f_1_11 : X 1 11 = 0 := by
      have q0 := congrFun (congrFun h3 1) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_1_12 : X 1 12 = 0 := by
      have q0 := congrFun (congrFun h1 0) 12
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_1_13 : X 1 13 = 0 := by
      have q0 := congrFun (congrFun h3 1) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_1_14 : X 1 14 = 0 := by
      have q0 := congrFun (congrFun h3 1) 9
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_1_15 : X 1 15 = 0 := by
      have q0 := congrFun (congrFun h3 1) 10
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_2_0 : X 2 0 = 0 := by
      have q0 := congrFun (congrFun h1 1) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_2_1 : X 2 1 = 0 := by
      have q0 := congrFun (congrFun h1 1) 1
      have q1 := congrFun (congrFun h1 0) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0 + ((-1:ℂ)/3) * q1
  have f_2_2 : X 2 2 = X 0 0 := by
      have q0 := congrFun (congrFun h1 0) 1
      have q1 := congrFun (congrFun h1 1) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0 + ((-1:ℂ)/3) * q1
  have f_2_3 : X 2 3 = 0 := by
      have q0 := congrFun (congrFun h3 7) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/9) * q0
  have f_2_4 : X 2 4 = 0 := by
      have q0 := congrFun (congrFun h1 1) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_2_5 : X 2 5 = 0 := by
      have q0 := congrFun (congrFun h3 2) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_2_6 : X 2 6 = 0 := by
      have q0 := congrFun (congrFun h3 2) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_2_7 : X 2 7 = 0 := by
      have q0 := congrFun (congrFun h3 2) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_2_8 : X 2 8 = 0 := by
      have q0 := congrFun (congrFun h1 1) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_2_9 : X 2 9 = 0 := by
      have q0 := congrFun (congrFun h3 2) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_2_10 : X 2 10 = 0 := by
      have q0 := congrFun (congrFun h3 2) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/16) * q0
  have f_2_11 : X 2 11 = 0 := by
      have q0 := congrFun (congrFun h3 2) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_2_12 : X 2 12 = 0 := by
      have q0 := congrFun (congrFun h1 1) 12
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_2_13 : X 2 13 = 0 := by
      have q0 := congrFun (congrFun h3 2) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_2_14 : X 2 14 = 0 := by
      have q0 := congrFun (congrFun h3 2) 9
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_2_15 : X 2 15 = 0 := by
      have q0 := congrFun (congrFun h3 2) 10
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_3_0 : X 3 0 = 0 := by
      have q0 := congrFun (congrFun h1 2) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_3_1 : X 3 1 = 0 := by
      have q0 := congrFun (congrFun h1 3) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_3_2 : X 3 2 = 0 := by
      have q0 := congrFun (congrFun h1 3) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_3_3 : X 3 3 = X 0 0 := by
      have q0 := congrFun (congrFun h1 0) 1
      have q1 := congrFun (congrFun h1 1) 2
      have q2 := congrFun (congrFun h1 2) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0 + ((-1:ℂ)/3) * q1 + ((-1:ℂ)/3) * q2
  have f_3_4 : X 3 4 = 0 := by
      have q0 := congrFun (congrFun h1 2) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_3_5 : X 3 5 = 0 := by
      have q0 := congrFun (congrFun h1 3) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_3_6 : X 3 6 = 0 := by
      have q0 := congrFun (congrFun h1 3) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_3_7 : X 3 7 = 0 := by
      have q0 := congrFun (congrFun h3 3) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_3_8 : X 3 8 = 0 := by
      have q0 := congrFun (congrFun h1 2) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_3_9 : X 3 9 = 0 := by
      have q0 := congrFun (congrFun h1 3) 10
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_3_10 : X 3 10 = 0 := by
      have q0 := congrFun (congrFun h1 3) 11
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_3_11 : X 3 11 = 0 := by
      have q0 := congrFun (congrFun h3 3) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_3_12 : X 3 12 = 0 := by
      have q0 := congrFun (congrFun h1 2) 12
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_3_13 : X 3 13 = 0 := by
      have q0 := congrFun (congrFun h1 3) 14
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_3_14 : X 3 14 = 0 := by
      have q0 := congrFun (congrFun h1 3) 15
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_3_15 : X 3 15 = 0 := by
      have q0 := congrFun (congrFun h3 3) 10
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_4_0 : X 4 0 = 0 := by
      have q0 := congrFun (congrFun h2 0) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_4_1 : X 4 1 = 0 := by
      have q0 := congrFun (congrFun h2 0) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_4_2 : X 4 2 = 0 := by
      have q0 := congrFun (congrFun h2 0) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_4_3 : X 4 3 = 0 := by
      have q0 := congrFun (congrFun h2 0) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_4_4 : X 4 4 = X 0 0 := by
      have q0 := congrFun (congrFun h2 0) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_4_5 : X 4 5 = 0 := by
      have q0 := congrFun (congrFun h3 4) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_4_6 : X 4 6 = 0 := by
      have q0 := congrFun (congrFun h3 4) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_4_7 : X 4 7 = 0 := by
      have q0 := congrFun (congrFun h3 4) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_4_8 : X 4 8 = 0 := by
      have q0 := congrFun (congrFun h2 0) 8
      have q1 := congrFun (congrFun h1 0) 5
      have q2 := congrFun (congrFun h3 1) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0 + (1:ℂ) * q1 + ((1:ℂ)/3) * q2
  have f_4_9 : X 4 9 = 0 := by
      have q0 := congrFun (congrFun h3 4) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_4_10 : X 4 10 = 0 := by
      have q0 := congrFun (congrFun h3 4) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/16) * q0
  have f_4_11 : X 4 11 = 0 := by
      have q0 := congrFun (congrFun h3 4) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_4_12 : X 4 12 = 0 := by
      have q0 := congrFun (congrFun h3 9) 12
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/12) * q0
  have f_4_13 : X 4 13 = 0 := by
      have q0 := congrFun (congrFun h3 4) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_4_14 : X 4 14 = 0 := by
      have q0 := congrFun (congrFun h3 4) 9
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_4_15 : X 4 15 = 0 := by
      have q0 := congrFun (congrFun h3 4) 10
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_5_0 : X 5 0 = 0 := by
      have q0 := congrFun (congrFun h1 4) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_5_1 : X 5 1 = 0 := by
      have q0 := congrFun (congrFun h2 1) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_5_2 : X 5 2 = 0 := by
      have q0 := congrFun (congrFun h2 1) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_5_3 : X 5 3 = 0 := by
      have q0 := congrFun (congrFun h2 1) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_5_4 : X 5 4 = 0 := by
      have q0 := congrFun (congrFun h1 4) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_5_5 : X 5 5 = X 0 0 := by
      have q0 := congrFun (congrFun h2 0) 4
      have q1 := congrFun (congrFun h1 4) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0 + (-1:ℂ) * q1
  have f_5_6 : X 5 6 = 0 := by
      have q0 := congrFun (congrFun h1 4) 6
      have q1 := congrFun (congrFun h3 4) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0 + ((1:ℂ)/9) * q1
  have f_5_7 : X 5 7 = 0 := by
      have q0 := congrFun (congrFun h3 10) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/16) * q0
  have f_5_8 : X 5 8 = 0 := by
      have q0 := congrFun (congrFun h1 4) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_5_9 : X 5 9 = 0 := by
      have q0 := congrFun (congrFun h2 0) 8
      have q1 := congrFun (congrFun h1 0) 5
      have q2 := congrFun (congrFun h3 1) 0
      have q3 := congrFun (congrFun h1 4) 9
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0 + (-1:ℂ) * q1 + ((-1:ℂ)/3) * q2 + (-1:ℂ) * q3
  have f_5_10 : X 5 10 = 0 := by
      have q0 := congrFun (congrFun h1 4) 10
      have q1 := congrFun (congrFun h3 4) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0 + ((-1:ℂ)/12) * q1
  have f_5_11 : X 5 11 = 0 := by
      have q0 := congrFun (congrFun h3 10) 11
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/16) * q0
  have f_5_12 : X 5 12 = 0 := by
      have q0 := congrFun (congrFun h1 4) 12
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_5_13 : X 5 13 = 0 := by
      have q0 := congrFun (congrFun h3 10) 13
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/16) * q0
  have f_5_14 : X 5 14 = 0 := by
      have q0 := congrFun (congrFun h3 10) 14
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/16) * q0
  have f_5_15 : X 5 15 = 0 := by
      have q0 := congrFun (congrFun h3 10) 15
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/16) * q0
  have f_6_0 : X 6 0 = 0 := by
      have q0 := congrFun (congrFun h1 5) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_6_1 : X 6 1 = 0 := by
      have q0 := congrFun (congrFun h2 2) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_6_2 : X 6 2 = 0 := by
      have q0 := congrFun (congrFun h2 2) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_6_3 : X 6 3 = 0 := by
      have q0 := congrFun (congrFun h2 2) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_6_4 : X 6 4 = 0 := by
      have q0 := congrFun (congrFun h1 5) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_6_5 : X 6 5 = 0 := by
      have q0 := congrFun (congrFun h1 5) 5
      have q1 := congrFun (congrFun h1 4) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0 + (-1:ℂ) * q1
  have f_6_6 : X 6 6 = X 0 0 := by
      have q0 := congrFun (congrFun h2 0) 4
      have q1 := congrFun (congrFun h1 4) 5
      have q2 := congrFun (congrFun h1 5) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0 + (-1:ℂ) * q1 + (-1:ℂ) * q2
  have f_6_7 : X 6 7 = 0 := by
      have q0 := congrFun (congrFun h3 11) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/12) * q0
  have f_6_8 : X 6 8 = 0 := by
      have q0 := congrFun (congrFun h1 5) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_6_9 : X 6 9 = 0 := by
      have q0 := congrFun (congrFun h1 5) 9
      have q1 := congrFun (congrFun h1 4) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0 + (1:ℂ) * q1
  have f_6_10 : X 6 10 = 0 := by
      have q0 := congrFun (congrFun h2 0) 8
      have q1 := congrFun (congrFun h1 0) 5
      have q2 := congrFun (congrFun h3 1) 0
      have q3 := congrFun (congrFun h1 4) 9
      have q4 := congrFun (congrFun h1 5) 10
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0 + (1:ℂ) * q1 + ((1:ℂ)/3) * q2 + (1:ℂ) * q3 + (-1:ℂ) * q4
  have f_6_11 : X 6 11 = 0 := by
      have q0 := congrFun (congrFun h3 11) 11
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/12) * q0
  have f_6_12 : X 6 12 = 0 := by
      have q0 := congrFun (congrFun h1 5) 12
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_6_13 : X 6 13 = 0 := by
      have q0 := congrFun (congrFun h3 11) 13
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/12) * q0
  have f_6_14 : X 6 14 = 0 := by
      have q0 := congrFun (congrFun h3 11) 14
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/12) * q0
  have f_6_15 : X 6 15 = 0 := by
      have q0 := congrFun (congrFun h3 11) 15
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/12) * q0
  have f_7_0 : X 7 0 = 0 := by
      have q0 := congrFun (congrFun h1 6) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_7_1 : X 7 1 = 0 := by
      have q0 := congrFun (congrFun h1 7) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_7_2 : X 7 2 = 0 := by
      have q0 := congrFun (congrFun h1 7) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_7_3 : X 7 3 = 0 := by
      have q0 := congrFun (congrFun h2 3) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_7_4 : X 7 4 = 0 := by
      have q0 := congrFun (congrFun h1 6) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_7_5 : X 7 5 = 0 := by
      have q0 := congrFun (congrFun h1 7) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_7_6 : X 7 6 = 0 := by
      have q0 := congrFun (congrFun h1 7) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_7_7 : X 7 7 = X 0 0 := by
      have q0 := congrFun (congrFun h2 0) 4
      have q1 := congrFun (congrFun h1 4) 5
      have q2 := congrFun (congrFun h1 5) 6
      have q3 := congrFun (congrFun h1 6) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0 + (-1:ℂ) * q1 + (-1:ℂ) * q2 + (-1:ℂ) * q3
  have f_7_8 : X 7 8 = 0 := by
      have q0 := congrFun (congrFun h1 6) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_7_9 : X 7 9 = 0 := by
      have q0 := congrFun (congrFun h1 7) 10
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_7_10 : X 7 10 = 0 := by
      have q0 := congrFun (congrFun h1 7) 11
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_7_11 : X 7 11 = 0 := by
      have q0 := congrFun (congrFun h2 0) 8
      have q1 := congrFun (congrFun h1 0) 5
      have q2 := congrFun (congrFun h3 1) 0
      have q3 := congrFun (congrFun h1 4) 9
      have q4 := congrFun (congrFun h1 5) 10
      have q5 := congrFun (congrFun h1 6) 11
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0 + (-1:ℂ) * q1 + ((-1:ℂ)/3) * q2 + (-1:ℂ) * q3 + (1:ℂ) * q4 + (-1:ℂ) * q5
  have f_7_12 : X 7 12 = 0 := by
      have q0 := congrFun (congrFun h1 6) 12
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_7_13 : X 7 13 = 0 := by
      have q0 := congrFun (congrFun h1 7) 14
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_7_14 : X 7 14 = 0 := by
      have q0 := congrFun (congrFun h1 7) 15
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_7_15 : X 7 15 = 0 := by
      have q0 := congrFun (congrFun h1 6) 15
      have q1 := congrFun (congrFun h3 11) 14
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0 + ((1:ℂ)/4) * q1
  have f_8_0 : X 8 0 = 0 := by
      have q0 := congrFun (congrFun h2 4) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_8_1 : X 8 1 = 0 := by
      have q0 := congrFun (congrFun h2 4) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_8_2 : X 8 2 = 0 := by
      have q0 := congrFun (congrFun h2 4) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_8_3 : X 8 3 = 0 := by
      have q0 := congrFun (congrFun h2 4) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_8_4 : X 8 4 = 0 := by
      have q0 := congrFun (congrFun h2 4) 4
      have q1 := congrFun (congrFun h2 0) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0 + ((-1:ℂ)/3) * q1
  have f_8_5 : X 8 5 = 0 := by
      have q0 := congrFun (congrFun h3 8) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_8_6 : X 8 6 = 0 := by
      have q0 := congrFun (congrFun h3 8) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_8_7 : X 8 7 = 0 := by
      have q0 := congrFun (congrFun h3 8) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_8_8 : X 8 8 = X 0 0 := by
      have q0 := congrFun (congrFun h2 0) 4
      have q1 := congrFun (congrFun h2 4) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0 + ((-1:ℂ)/3) * q1
  have f_8_9 : X 8 9 = 0 := by
      have q0 := congrFun (congrFun h3 8) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_8_10 : X 8 10 = 0 := by
      have q0 := congrFun (congrFun h3 8) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/16) * q0
  have f_8_11 : X 8 11 = 0 := by
      have q0 := congrFun (congrFun h3 8) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_8_12 : X 8 12 = 0 := by
      have q0 := congrFun (congrFun h3 13) 12
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/9) * q0
  have f_8_13 : X 8 13 = 0 := by
      have q0 := congrFun (congrFun h3 8) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_8_14 : X 8 14 = 0 := by
      have q0 := congrFun (congrFun h3 8) 9
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_8_15 : X 8 15 = 0 := by
      have q0 := congrFun (congrFun h3 8) 10
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_9_0 : X 9 0 = 0 := by
      have q0 := congrFun (congrFun h1 8) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_9_1 : X 9 1 = 0 := by
      have q0 := congrFun (congrFun h2 5) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_9_2 : X 9 2 = 0 := by
      have q0 := congrFun (congrFun h2 5) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_9_3 : X 9 3 = 0 := by
      have q0 := congrFun (congrFun h2 5) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_9_4 : X 9 4 = 0 := by
      have q0 := congrFun (congrFun h1 8) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_9_5 : X 9 5 = 0 := by
      have q0 := congrFun (congrFun h2 4) 4
      have q1 := congrFun (congrFun h2 0) 0
      have q2 := congrFun (congrFun h1 8) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0 + ((1:ℂ)/3) * q1 + (1:ℂ) * q2
  have f_9_6 : X 9 6 = 0 := by
      have q0 := congrFun (congrFun h1 8) 6
      have q1 := congrFun (congrFun h3 8) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0 + ((-1:ℂ)/9) * q1
  have f_9_7 : X 9 7 = 0 := by
      have q0 := congrFun (congrFun h3 14) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/12) * q0
  have f_9_8 : X 9 8 = 0 := by
      have q0 := congrFun (congrFun h1 8) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_9_9 : X 9 9 = X 0 0 := by
      have q0 := congrFun (congrFun h2 0) 4
      have q1 := congrFun (congrFun h2 4) 8
      have q2 := congrFun (congrFun h1 8) 9
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0 + ((-1:ℂ)/3) * q1 + (1:ℂ) * q2
  have f_9_10 : X 9 10 = 0 := by
      have q0 := congrFun (congrFun h1 8) 10
      have q1 := congrFun (congrFun h3 8) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0 + ((1:ℂ)/12) * q1
  have f_9_11 : X 9 11 = 0 := by
      have q0 := congrFun (congrFun h3 14) 11
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/12) * q0
  have f_9_12 : X 9 12 = 0 := by
      have q0 := congrFun (congrFun h1 8) 12
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_9_13 : X 9 13 = 0 := by
      have q0 := congrFun (congrFun h3 14) 13
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/12) * q0
  have f_9_14 : X 9 14 = 0 := by
      have q0 := congrFun (congrFun h3 14) 14
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/12) * q0
  have f_9_15 : X 9 15 = 0 := by
      have q0 := congrFun (congrFun h3 14) 15
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/12) * q0
  have f_10_0 : X 10 0 = 0 := by
      have q0 := congrFun (congrFun h1 9) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_10_1 : X 10 1 = 0 := by
      have q0 := congrFun (congrFun h2 6) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_10_2 : X 10 2 = 0 := by
      have q0 := congrFun (congrFun h2 6) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_10_3 : X 10 3 = 0 := by
      have q0 := congrFun (congrFun h2 6) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_10_4 : X 10 4 = 0 := by
      have q0 := congrFun (congrFun h1 9) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_10_5 : X 10 5 = 0 := by
      have q0 := congrFun (congrFun h1 9) 5
      have q1 := congrFun (congrFun h1 8) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0 + (-1:ℂ) * q1
  have f_10_6 : X 10 6 = 0 := by
      have q0 := congrFun (congrFun h2 4) 4
      have q1 := congrFun (congrFun h2 0) 0
      have q2 := congrFun (congrFun h1 8) 5
      have q3 := congrFun (congrFun h1 9) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0 + ((-1:ℂ)/3) * q1 + (-1:ℂ) * q2 + (1:ℂ) * q3
  have f_10_7 : X 10 7 = 0 := by
      have q0 := congrFun (congrFun h3 15) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/9) * q0
  have f_10_8 : X 10 8 = 0 := by
      have q0 := congrFun (congrFun h1 9) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_10_9 : X 10 9 = 0 := by
      have q0 := congrFun (congrFun h1 9) 9
      have q1 := congrFun (congrFun h1 8) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0 + (1:ℂ) * q1
  have f_10_10 : X 10 10 = X 0 0 := by
      have q0 := congrFun (congrFun h2 0) 4
      have q1 := congrFun (congrFun h2 4) 8
      have q2 := congrFun (congrFun h1 8) 9
      have q3 := congrFun (congrFun h1 9) 10
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0 + ((-1:ℂ)/3) * q1 + (1:ℂ) * q2 + (1:ℂ) * q3
  have f_10_11 : X 10 11 = 0 := by
      have q0 := congrFun (congrFun h3 15) 11
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/9) * q0
  have f_10_12 : X 10 12 = 0 := by
      have q0 := congrFun (congrFun h1 9) 12
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_10_13 : X 10 13 = 0 := by
      have q0 := congrFun (congrFun h3 15) 13
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/9) * q0
  have f_10_14 : X 10 14 = 0 := by
      have q0 := congrFun (congrFun h3 15) 14
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/9) * q0
  have f_10_15 : X 10 15 = 0 := by
      have q0 := congrFun (congrFun h3 15) 15
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/9) * q0
  have f_11_0 : X 11 0 = 0 := by
      have q0 := congrFun (congrFun h1 10) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_11_1 : X 11 1 = 0 := by
      have q0 := congrFun (congrFun h1 11) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_11_2 : X 11 2 = 0 := by
      have q0 := congrFun (congrFun h1 11) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_11_3 : X 11 3 = 0 := by
      have q0 := congrFun (congrFun h2 7) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_11_4 : X 11 4 = 0 := by
      have q0 := congrFun (congrFun h1 10) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_11_5 : X 11 5 = 0 := by
      have q0 := congrFun (congrFun h1 11) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_11_6 : X 11 6 = 0 := by
      have q0 := congrFun (congrFun h1 11) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_11_7 : X 11 7 = 0 := by
      have q0 := congrFun (congrFun h2 4) 4
      have q1 := congrFun (congrFun h2 0) 0
      have q2 := congrFun (congrFun h1 8) 5
      have q3 := congrFun (congrFun h1 9) 6
      have q4 := congrFun (congrFun h1 10) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0 + ((1:ℂ)/3) * q1 + (1:ℂ) * q2 + (-1:ℂ) * q3 + (1:ℂ) * q4
  have f_11_8 : X 11 8 = 0 := by
      have q0 := congrFun (congrFun h1 10) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_11_9 : X 11 9 = 0 := by
      have q0 := congrFun (congrFun h1 11) 10
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_11_10 : X 11 10 = 0 := by
      have q0 := congrFun (congrFun h1 11) 11
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_11_11 : X 11 11 = X 0 0 := by
      have q0 := congrFun (congrFun h2 0) 4
      have q1 := congrFun (congrFun h2 4) 8
      have q2 := congrFun (congrFun h1 8) 9
      have q3 := congrFun (congrFun h1 9) 10
      have q4 := congrFun (congrFun h1 10) 11
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0 + ((-1:ℂ)/3) * q1 + (1:ℂ) * q2 + (1:ℂ) * q3 + (1:ℂ) * q4
  have f_11_12 : X 11 12 = 0 := by
      have q0 := congrFun (congrFun h1 10) 12
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_11_13 : X 11 13 = 0 := by
      have q0 := congrFun (congrFun h1 11) 14
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_11_14 : X 11 14 = 0 := by
      have q0 := congrFun (congrFun h1 11) 15
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_11_15 : X 11 15 = 0 := by
      have q0 := congrFun (congrFun h1 10) 15
      have q1 := congrFun (congrFun h3 15) 14
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0 + ((-1:ℂ)/3) * q1
  have f_12_0 : X 12 0 = 0 := by
      have q0 := congrFun (congrFun h2 8) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_12_1 : X 12 1 = 0 := by
      have q0 := congrFun (congrFun h2 8) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_12_2 : X 12 2 = 0 := by
      have q0 := congrFun (congrFun h2 8) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_12_3 : X 12 3 = 0 := by
      have q0 := congrFun (congrFun h2 8) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_12_4 : X 12 4 = 0 := by
      have q0 := congrFun (congrFun h2 12) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_12_5 : X 12 5 = 0 := by
      have q0 := congrFun (congrFun h2 12) 9
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_12_6 : X 12 6 = 0 := by
      have q0 := congrFun (congrFun h2 12) 10
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_12_7 : X 12 7 = 0 := by
      have q0 := congrFun (congrFun h2 12) 11
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_12_8 : X 12 8 = 0 := by
      have q0 := congrFun (congrFun h2 12) 12
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_12_9 : X 12 9 = 0 := by
      have q0 := congrFun (congrFun h2 12) 13
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_12_10 : X 12 10 = 0 := by
      have q0 := congrFun (congrFun h2 12) 14
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_12_11 : X 12 11 = 0 := by
      have q0 := congrFun (congrFun h2 12) 15
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_12_12 : X 12 12 = X 0 0 := by
      have q0 := congrFun (congrFun h2 0) 4
      have q1 := congrFun (congrFun h2 4) 8
      have q2 := congrFun (congrFun h2 8) 12
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0 + ((-1:ℂ)/3) * q1 + ((-1:ℂ)/3) * q2
  have f_12_13 : X 12 13 = 0 := by
      have q0 := congrFun (congrFun h3 12) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_12_14 : X 12 14 = 0 := by
      have q0 := congrFun (congrFun h3 12) 9
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_12_15 : X 12 15 = 0 := by
      have q0 := congrFun (congrFun h3 12) 10
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/9) * q0
  have f_13_0 : X 13 0 = 0 := by
      have q0 := congrFun (congrFun h1 12) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_13_1 : X 13 1 = 0 := by
      have q0 := congrFun (congrFun h2 9) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_13_2 : X 13 2 = 0 := by
      have q0 := congrFun (congrFun h2 9) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_13_3 : X 13 3 = 0 := by
      have q0 := congrFun (congrFun h2 9) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_13_4 : X 13 4 = 0 := by
      have q0 := congrFun (congrFun h1 12) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_13_5 : X 13 5 = 0 := by
      have q0 := congrFun (congrFun h2 13) 9
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_13_6 : X 13 6 = 0 := by
      have q0 := congrFun (congrFun h2 13) 10
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_13_7 : X 13 7 = 0 := by
      have q0 := congrFun (congrFun h2 13) 11
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_13_8 : X 13 8 = 0 := by
      have q0 := congrFun (congrFun h1 12) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_13_9 : X 13 9 = 0 := by
      have q0 := congrFun (congrFun h2 13) 13
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_13_10 : X 13 10 = 0 := by
      have q0 := congrFun (congrFun h2 13) 14
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_13_11 : X 13 11 = 0 := by
      have q0 := congrFun (congrFun h2 13) 15
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_13_12 : X 13 12 = 0 := by
      have q0 := congrFun (congrFun h1 12) 12
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_13_13 : X 13 13 = X 0 0 := by
      have q0 := congrFun (congrFun h2 0) 4
      have q1 := congrFun (congrFun h2 4) 8
      have q2 := congrFun (congrFun h2 8) 12
      have q3 := congrFun (congrFun h1 12) 13
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0 + ((-1:ℂ)/3) * q1 + ((-1:ℂ)/3) * q2 + ((1:ℂ)/3) * q3
  have f_13_14 : X 13 14 = 0 := by
      have q0 := congrFun (congrFun h1 12) 14
      have q1 := congrFun (congrFun h3 12) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0 + ((1:ℂ)/9) * q1
  have f_13_15 : X 13 15 = 0 := by
      have q0 := congrFun (congrFun h1 12) 15
      have q1 := congrFun (congrFun h3 12) 9
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0 + ((1:ℂ)/12) * q1
  have f_14_0 : X 14 0 = 0 := by
      have q0 := congrFun (congrFun h1 13) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_14_1 : X 14 1 = 0 := by
      have q0 := congrFun (congrFun h2 10) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_14_2 : X 14 2 = 0 := by
      have q0 := congrFun (congrFun h2 10) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_14_3 : X 14 3 = 0 := by
      have q0 := congrFun (congrFun h2 10) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_14_4 : X 14 4 = 0 := by
      have q0 := congrFun (congrFun h1 13) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_14_5 : X 14 5 = 0 := by
      have q0 := congrFun (congrFun h2 14) 9
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_14_6 : X 14 6 = 0 := by
      have q0 := congrFun (congrFun h2 14) 10
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_14_7 : X 14 7 = 0 := by
      have q0 := congrFun (congrFun h2 14) 11
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_14_8 : X 14 8 = 0 := by
      have q0 := congrFun (congrFun h1 13) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_14_9 : X 14 9 = 0 := by
      have q0 := congrFun (congrFun h2 14) 13
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_14_10 : X 14 10 = 0 := by
      have q0 := congrFun (congrFun h2 14) 14
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_14_11 : X 14 11 = 0 := by
      have q0 := congrFun (congrFun h2 14) 15
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_14_12 : X 14 12 = 0 := by
      have q0 := congrFun (congrFun h1 13) 12
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_14_13 : X 14 13 = 0 := by
      have q0 := congrFun (congrFun h1 13) 13
      have q1 := congrFun (congrFun h1 12) 12
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0 + ((1:ℂ)/3) * q1
  have f_14_14 : X 14 14 = X 0 0 := by
      have q0 := congrFun (congrFun h2 0) 4
      have q1 := congrFun (congrFun h2 4) 8
      have q2 := congrFun (congrFun h2 8) 12
      have q3 := congrFun (congrFun h1 12) 13
      have q4 := congrFun (congrFun h1 13) 14
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0 + ((-1:ℂ)/3) * q1 + ((-1:ℂ)/3) * q2 + ((1:ℂ)/3) * q3 + ((1:ℂ)/3) * q4
  have f_14_15 : X 14 15 = 0 := by
      have q0 := congrFun (congrFun h1 13) 15
      have q1 := congrFun (congrFun h1 12) 14
      have q2 := congrFun (congrFun h3 12) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0 + ((1:ℂ)/3) * q1 + ((1:ℂ)/9) * q2
  have f_15_0 : X 15 0 = 0 := by
      have q0 := congrFun (congrFun h1 14) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_15_1 : X 15 1 = 0 := by
      have q0 := congrFun (congrFun h1 15) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_15_2 : X 15 2 = 0 := by
      have q0 := congrFun (congrFun h1 15) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_15_3 : X 15 3 = 0 := by
      have q0 := congrFun (congrFun h2 11) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_15_4 : X 15 4 = 0 := by
      have q0 := congrFun (congrFun h1 14) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_15_5 : X 15 5 = 0 := by
      have q0 := congrFun (congrFun h1 15) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_15_6 : X 15 6 = 0 := by
      have q0 := congrFun (congrFun h1 15) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (1:ℂ) * q0
  have f_15_7 : X 15 7 = 0 := by
      have q0 := congrFun (congrFun h2 15) 11
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_15_8 : X 15 8 = 0 := by
      have q0 := congrFun (congrFun h1 14) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_15_9 : X 15 9 = 0 := by
      have q0 := congrFun (congrFun h1 15) 10
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_15_10 : X 15 10 = 0 := by
      have q0 := congrFun (congrFun h1 15) 11
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) (-1:ℂ) * q0
  have f_15_11 : X 15 11 = 0 := by
      have q0 := congrFun (congrFun h2 15) 15
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_15_12 : X 15 12 = 0 := by
      have q0 := congrFun (congrFun h1 14) 12
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((1:ℂ)/3) * q0
  have f_15_13 : X 15 13 = 0 := by
      have q0 := congrFun (congrFun h1 15) 14
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_15_14 : X 15 14 = 0 := by
      have q0 := congrFun (congrFun h1 15) 15
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0
  have f_15_15 : X 15 15 = X 0 0 := by
      have q0 := congrFun (congrFun h2 0) 4
      have q1 := congrFun (congrFun h2 4) 8
      have q2 := congrFun (congrFun h2 8) 12
      have q3 := congrFun (congrFun h1 12) 13
      have q4 := congrFun (congrFun h1 13) 14
      have q5 := congrFun (congrFun h1 14) 15
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, G1, G2, G3] <;> ring_nf)) ((-1:ℂ)/3) * q0 + ((-1:ℂ)/3) * q1 + ((-1:ℂ)/3) * q2 + ((1:ℂ)/3) * q3 + ((1:ℂ)/3) * q4 + ((1:ℂ)/3) * q5
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.one_apply, f_0_1, f_0_2, f_0_3, f_0_4, f_0_5, f_0_6, f_0_7, f_0_8, f_0_9, f_0_10, f_0_11, f_0_12, f_0_13, f_0_14, f_0_15, f_1_0, f_1_1, f_1_2, f_1_3, f_1_4, f_1_5, f_1_6, f_1_7, f_1_8, f_1_9, f_1_10, f_1_11, f_1_12, f_1_13, f_1_14, f_1_15, f_2_0, f_2_1, f_2_2, f_2_3, f_2_4, f_2_5, f_2_6, f_2_7, f_2_8, f_2_9, f_2_10, f_2_11, f_2_12, f_2_13, f_2_14, f_2_15, f_3_0, f_3_1, f_3_2, f_3_3, f_3_4, f_3_5, f_3_6, f_3_7, f_3_8, f_3_9, f_3_10, f_3_11, f_3_12, f_3_13, f_3_14, f_3_15, f_4_0, f_4_1, f_4_2, f_4_3, f_4_4, f_4_5, f_4_6, f_4_7, f_4_8, f_4_9, f_4_10, f_4_11, f_4_12, f_4_13, f_4_14, f_4_15, f_5_0, f_5_1, f_5_2, f_5_3, f_5_4, f_5_5, f_5_6, f_5_7, f_5_8, f_5_9, f_5_10, f_5_11, f_5_12, f_5_13, f_5_14, f_5_15, f_6_0, f_6_1, f_6_2, f_6_3, f_6_4, f_6_5, f_6_6, f_6_7, f_6_8, f_6_9, f_6_10, f_6_11, f_6_12, f_6_13, f_6_14, f_6_15, f_7_0, f_7_1, f_7_2, f_7_3, f_7_4, f_7_5, f_7_6, f_7_7, f_7_8, f_7_9, f_7_10, f_7_11, f_7_12, f_7_13, f_7_14, f_7_15, f_8_0, f_8_1, f_8_2, f_8_3, f_8_4, f_8_5, f_8_6, f_8_7, f_8_8, f_8_9, f_8_10, f_8_11, f_8_12, f_8_13, f_8_14, f_8_15, f_9_0, f_9_1, f_9_2, f_9_3, f_9_4, f_9_5, f_9_6, f_9_7, f_9_8, f_9_9, f_9_10, f_9_11, f_9_12, f_9_13, f_9_14, f_9_15, f_10_0, f_10_1, f_10_2, f_10_3, f_10_4, f_10_5, f_10_6, f_10_7, f_10_8, f_10_9, f_10_10, f_10_11, f_10_12, f_10_13, f_10_14, f_10_15, f_11_0, f_11_1, f_11_2, f_11_3, f_11_4, f_11_5, f_11_6, f_11_7, f_11_8, f_11_9, f_11_10, f_11_11, f_11_12, f_11_13, f_11_14, f_11_15, f_12_0, f_12_1, f_12_2, f_12_3, f_12_4, f_12_5, f_12_6, f_12_7, f_12_8, f_12_9, f_12_10, f_12_11, f_12_12, f_12_13, f_12_14, f_12_15, f_13_0, f_13_1, f_13_2, f_13_3, f_13_4, f_13_5, f_13_6, f_13_7, f_13_8, f_13_9, f_13_10, f_13_11, f_13_12, f_13_13, f_13_14, f_13_15, f_14_0, f_14_1, f_14_2, f_14_3, f_14_4, f_14_5, f_14_6, f_14_7, f_14_8, f_14_9, f_14_10, f_14_11, f_14_12, f_14_13, f_14_14, f_14_15, f_15_0, f_15_1, f_15_2, f_15_3, f_15_4, f_15_5, f_15_6, f_15_7, f_15_8, f_15_9, f_15_10, f_15_11, f_15_12, f_15_13, f_15_14, f_15_15] <;> (try ring_nf)

end Entropic.Pass2.PairGen
