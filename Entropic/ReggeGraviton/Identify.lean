import Entropic.ReggeGraviton.Symbol
import Entropic.ReggeGraviton.Continuum
import Entropic.ReggeGraviton.MomentsA0
import Entropic.ReggeGraviton.MomentsA1
import Entropic.ReggeGraviton.MomentsA2
import Entropic.ReggeGraviton.MomentsA3
import Entropic.ReggeGraviton.MomentsA4
import Entropic.ReggeGraviton.MomentsA5
import Entropic.ReggeGraviton.MomentsB

/-!
# The lattice symbol is the linearized Einstein–Hilbert kernel

`KEH k c d` is the Fourier kernel of the second-order part of `√g R` in the basis of symmetric
matrices `basisM c` (`h = ∑_c h_c basisM c`):

  `(√g R)⁽²⁾ = −¼ ∂_λh_μν ∂_λh_μν + ½ (∂_μh_μλ)² − ½ ∂_μh ∂_νh_μν + ¼ (∂_λh)²`.

`symbol_limit`: for every momentum `k` and every pair of metric components,
`ε⁻² Kred(εk) → KEH k` as `ε → 0`. With `Kred` the Hessian of `∑_t A_t ε_t`, this is the statement
`∑_t A_t ε_t = ½ ∫ √g R` at quadratic order, with no free normalization.
-/

open Complex Filter Topology

namespace Entropic.ReggeGraviton

attribute [local irreducible] typ base hz simplexData hzL

theorem momA2_comm (c d : Fin 10) (i l : Fin 4) : momA2 c d i l = momA2 c d l i := by
  simp only [momA2]
  congr 1; funext a ba b bb x; ring


theorem momB0_all : ∀ c' j, momB0 c' j = 0 := by
  intro c' j
  fin_cases c' <;> fin_cases j
  · exact momB0_0_0
  · exact momB0_0_1
  · exact momB0_0_2
  · exact momB0_0_3
  · exact momB0_1_0
  · exact momB0_1_1
  · exact momB0_1_2
  · exact momB0_1_3
  · exact momB0_2_0
  · exact momB0_2_1
  · exact momB0_2_2
  · exact momB0_2_3
  · exact momB0_3_0
  · exact momB0_3_1
  · exact momB0_3_2
  · exact momB0_3_3
  · exact momB0_4_0
  · exact momB0_4_1
  · exact momB0_4_2
  · exact momB0_4_3
  · exact momB0_5_0
  · exact momB0_5_1
  · exact momB0_5_2
  · exact momB0_5_3
  · exact momB0_6_0
  · exact momB0_6_1
  · exact momB0_6_2
  · exact momB0_6_3
  · exact momB0_7_0
  · exact momB0_7_1
  · exact momB0_7_2
  · exact momB0_7_3
  · exact momB0_8_0
  · exact momB0_8_1
  · exact momB0_8_2
  · exact momB0_8_3
  · exact momB0_9_0
  · exact momB0_9_1
  · exact momB0_9_2
  · exact momB0_9_3

theorem Lval_eq_0_0 (k : Fin 4 → ℝ) : Lval 0 0 k = (KEH k 0 0 : ℂ) := by
  have a00 : momA2 0 0 0 0 = 0 := momA2_0_0_0_0
  have a01 : momA2 0 0 0 1 = 0 := momA2_0_0_0_1
  have a02 : momA2 0 0 0 2 = 0 := momA2_0_0_0_2
  have a03 : momA2 0 0 0 3 = 0 := momA2_0_0_0_3
  have a10 : momA2 0 0 1 0 = 0 := by rw [momA2_comm]; exact momA2_0_0_0_1
  have a11 : momA2 0 0 1 1 = 0 := momA2_0_0_1_1
  have a12 : momA2 0 0 1 2 = 0 := momA2_0_0_1_2
  have a13 : momA2 0 0 1 3 = 0 := momA2_0_0_1_3
  have a20 : momA2 0 0 2 0 = 0 := by rw [momA2_comm]; exact momA2_0_0_0_2
  have a21 : momA2 0 0 2 1 = 0 := by rw [momA2_comm]; exact momA2_0_0_1_2
  have a22 : momA2 0 0 2 2 = 0 := momA2_0_0_2_2
  have a23 : momA2 0 0 2 3 = 0 := momA2_0_0_2_3
  have a30 : momA2 0 0 3 0 = 0 := by rw [momA2_comm]; exact momA2_0_0_0_3
  have a31 : momA2 0 0 3 1 = 0 := by rw [momA2_comm]; exact momA2_0_0_1_3
  have a32 : momA2 0 0 3 2 = 0 := by rw [momA2_comm]; exact momA2_0_0_2_3
  have a33 : momA2 0 0 3 3 = 0 := momA2_0_0_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_0_0_0, momB1_0_0_1, momB1_0_0_2, momB1_0_0_3, momB1_0_1_0, momB1_0_1_1, momB1_0_1_2, momB1_0_1_3, momB1_0_2_0, momB1_0_2_1, momB1_0_2_2, momB1_0_2_3, momB1_0_3_0, momB1_0_3_1, momB1_0_3_2, momB1_0_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_0_0 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 0 0 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 0 0 : ℂ)) := by
  rw [← Lval_eq_0_0]
  refine Kred_limit 0 0 k momA0_0_0 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_0_0_0
  · exact momA1_0_0_1
  · exact momA1_0_0_2
  · exact momA1_0_0_3

theorem Lval_eq_0_1 (k : Fin 4 → ℝ) : Lval 0 1 k = (KEH k 0 1 : ℂ) := by
  have a00 : momA2 0 1 0 0 = 0 := momA2_0_1_0_0
  have a01 : momA2 0 1 0 1 = 0 := momA2_0_1_0_1
  have a02 : momA2 0 1 0 2 = 0 := momA2_0_1_0_2
  have a03 : momA2 0 1 0 3 = 0 := momA2_0_1_0_3
  have a10 : momA2 0 1 1 0 = 0 := by rw [momA2_comm]; exact momA2_0_1_0_1
  have a11 : momA2 0 1 1 1 = 0 := momA2_0_1_1_1
  have a12 : momA2 0 1 1 2 = 0 := momA2_0_1_1_2
  have a13 : momA2 0 1 1 3 = 0 := momA2_0_1_1_3
  have a20 : momA2 0 1 2 0 = 0 := by rw [momA2_comm]; exact momA2_0_1_0_2
  have a21 : momA2 0 1 2 1 = 0 := by rw [momA2_comm]; exact momA2_0_1_1_2
  have a22 : momA2 0 1 2 2 = 0 := momA2_0_1_2_2
  have a23 : momA2 0 1 2 3 = 0 := momA2_0_1_2_3
  have a30 : momA2 0 1 3 0 = 0 := by rw [momA2_comm]; exact momA2_0_1_0_3
  have a31 : momA2 0 1 3 1 = 0 := by rw [momA2_comm]; exact momA2_0_1_1_3
  have a32 : momA2 0 1 3 2 = 0 := by rw [momA2_comm]; exact momA2_0_1_2_3
  have a33 : momA2 0 1 3 3 = 0 := momA2_0_1_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_0_0_0, momB1_0_0_1, momB1_0_0_2, momB1_0_0_3, momB1_0_1_0, momB1_0_1_1, momB1_0_1_2, momB1_0_1_3, momB1_0_2_0, momB1_0_2_1, momB1_0_2_2, momB1_0_2_3, momB1_0_3_0, momB1_0_3_1, momB1_0_3_2, momB1_0_3_3, momB1_1_0_0, momB1_1_0_1, momB1_1_0_2, momB1_1_0_3, momB1_1_1_0, momB1_1_1_1, momB1_1_1_2, momB1_1_1_3, momB1_1_2_0, momB1_1_2_1, momB1_1_2_2, momB1_1_2_3, momB1_1_3_0, momB1_1_3_1, momB1_1_3_2, momB1_1_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_0_1 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 0 1 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 0 1 : ℂ)) := by
  rw [← Lval_eq_0_1]
  refine Kred_limit 0 1 k momA0_0_1 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_0_1_0
  · exact momA1_0_1_1
  · exact momA1_0_1_2
  · exact momA1_0_1_3

theorem Lval_eq_0_2 (k : Fin 4 → ℝ) : Lval 0 2 k = (KEH k 0 2 : ℂ) := by
  have a00 : momA2 0 2 0 0 = 0 := momA2_0_2_0_0
  have a01 : momA2 0 2 0 1 = 0 := momA2_0_2_0_1
  have a02 : momA2 0 2 0 2 = 0 := momA2_0_2_0_2
  have a03 : momA2 0 2 0 3 = 0 := momA2_0_2_0_3
  have a10 : momA2 0 2 1 0 = 0 := by rw [momA2_comm]; exact momA2_0_2_0_1
  have a11 : momA2 0 2 1 1 = 0 := momA2_0_2_1_1
  have a12 : momA2 0 2 1 2 = 0 := momA2_0_2_1_2
  have a13 : momA2 0 2 1 3 = 0 := momA2_0_2_1_3
  have a20 : momA2 0 2 2 0 = 0 := by rw [momA2_comm]; exact momA2_0_2_0_2
  have a21 : momA2 0 2 2 1 = 0 := by rw [momA2_comm]; exact momA2_0_2_1_2
  have a22 : momA2 0 2 2 2 = 0 := momA2_0_2_2_2
  have a23 : momA2 0 2 2 3 = 0 := momA2_0_2_2_3
  have a30 : momA2 0 2 3 0 = 0 := by rw [momA2_comm]; exact momA2_0_2_0_3
  have a31 : momA2 0 2 3 1 = 0 := by rw [momA2_comm]; exact momA2_0_2_1_3
  have a32 : momA2 0 2 3 2 = 0 := by rw [momA2_comm]; exact momA2_0_2_2_3
  have a33 : momA2 0 2 3 3 = 0 := momA2_0_2_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_0_0_0, momB1_0_0_1, momB1_0_0_2, momB1_0_0_3, momB1_0_1_0, momB1_0_1_1, momB1_0_1_2, momB1_0_1_3, momB1_0_2_0, momB1_0_2_1, momB1_0_2_2, momB1_0_2_3, momB1_0_3_0, momB1_0_3_1, momB1_0_3_2, momB1_0_3_3, momB1_2_0_0, momB1_2_0_1, momB1_2_0_2, momB1_2_0_3, momB1_2_1_0, momB1_2_1_1, momB1_2_1_2, momB1_2_1_3, momB1_2_2_0, momB1_2_2_1, momB1_2_2_2, momB1_2_2_3, momB1_2_3_0, momB1_2_3_1, momB1_2_3_2, momB1_2_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_0_2 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 0 2 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 0 2 : ℂ)) := by
  rw [← Lval_eq_0_2]
  refine Kred_limit 0 2 k momA0_0_2 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_0_2_0
  · exact momA1_0_2_1
  · exact momA1_0_2_2
  · exact momA1_0_2_3

theorem Lval_eq_0_3 (k : Fin 4 → ℝ) : Lval 0 3 k = (KEH k 0 3 : ℂ) := by
  have a00 : momA2 0 3 0 0 = 0 := momA2_0_3_0_0
  have a01 : momA2 0 3 0 1 = 0 := momA2_0_3_0_1
  have a02 : momA2 0 3 0 2 = 0 := momA2_0_3_0_2
  have a03 : momA2 0 3 0 3 = 0 := momA2_0_3_0_3
  have a10 : momA2 0 3 1 0 = 0 := by rw [momA2_comm]; exact momA2_0_3_0_1
  have a11 : momA2 0 3 1 1 = 0 := momA2_0_3_1_1
  have a12 : momA2 0 3 1 2 = 0 := momA2_0_3_1_2
  have a13 : momA2 0 3 1 3 = 0 := momA2_0_3_1_3
  have a20 : momA2 0 3 2 0 = 0 := by rw [momA2_comm]; exact momA2_0_3_0_2
  have a21 : momA2 0 3 2 1 = 0 := by rw [momA2_comm]; exact momA2_0_3_1_2
  have a22 : momA2 0 3 2 2 = 0 := momA2_0_3_2_2
  have a23 : momA2 0 3 2 3 = 0 := momA2_0_3_2_3
  have a30 : momA2 0 3 3 0 = 0 := by rw [momA2_comm]; exact momA2_0_3_0_3
  have a31 : momA2 0 3 3 1 = 0 := by rw [momA2_comm]; exact momA2_0_3_1_3
  have a32 : momA2 0 3 3 2 = 0 := by rw [momA2_comm]; exact momA2_0_3_2_3
  have a33 : momA2 0 3 3 3 = 0 := momA2_0_3_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_0_0_0, momB1_0_0_1, momB1_0_0_2, momB1_0_0_3, momB1_0_1_0, momB1_0_1_1, momB1_0_1_2, momB1_0_1_3, momB1_0_2_0, momB1_0_2_1, momB1_0_2_2, momB1_0_2_3, momB1_0_3_0, momB1_0_3_1, momB1_0_3_2, momB1_0_3_3, momB1_3_0_0, momB1_3_0_1, momB1_3_0_2, momB1_3_0_3, momB1_3_1_0, momB1_3_1_1, momB1_3_1_2, momB1_3_1_3, momB1_3_2_0, momB1_3_2_1, momB1_3_2_2, momB1_3_2_3, momB1_3_3_0, momB1_3_3_1, momB1_3_3_2, momB1_3_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_0_3 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 0 3 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 0 3 : ℂ)) := by
  rw [← Lval_eq_0_3]
  refine Kred_limit 0 3 k momA0_0_3 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_0_3_0
  · exact momA1_0_3_1
  · exact momA1_0_3_2
  · exact momA1_0_3_3

theorem Lval_eq_0_4 (k : Fin 4 → ℝ) : Lval 0 4 k = (KEH k 0 4 : ℂ) := by
  have a00 : momA2 0 4 0 0 = 0 := momA2_0_4_0_0
  have a01 : momA2 0 4 0 1 = 0 := momA2_0_4_0_1
  have a02 : momA2 0 4 0 2 = 0 := momA2_0_4_0_2
  have a03 : momA2 0 4 0 3 = 0 := momA2_0_4_0_3
  have a10 : momA2 0 4 1 0 = 0 := by rw [momA2_comm]; exact momA2_0_4_0_1
  have a11 : momA2 0 4 1 1 = 0 := momA2_0_4_1_1
  have a12 : momA2 0 4 1 2 = 0 := momA2_0_4_1_2
  have a13 : momA2 0 4 1 3 = 0 := momA2_0_4_1_3
  have a20 : momA2 0 4 2 0 = 0 := by rw [momA2_comm]; exact momA2_0_4_0_2
  have a21 : momA2 0 4 2 1 = 0 := by rw [momA2_comm]; exact momA2_0_4_1_2
  have a22 : momA2 0 4 2 2 = -96 := momA2_0_4_2_2
  have a23 : momA2 0 4 2 3 = 0 := momA2_0_4_2_3
  have a30 : momA2 0 4 3 0 = 0 := by rw [momA2_comm]; exact momA2_0_4_0_3
  have a31 : momA2 0 4 3 1 = 0 := by rw [momA2_comm]; exact momA2_0_4_1_3
  have a32 : momA2 0 4 3 2 = 0 := by rw [momA2_comm]; exact momA2_0_4_2_3
  have a33 : momA2 0 4 3 3 = -96 := momA2_0_4_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_0_0_0, momB1_0_0_1, momB1_0_0_2, momB1_0_0_3, momB1_0_1_0, momB1_0_1_1, momB1_0_1_2, momB1_0_1_3, momB1_0_2_0, momB1_0_2_1, momB1_0_2_2, momB1_0_2_3, momB1_0_3_0, momB1_0_3_1, momB1_0_3_2, momB1_0_3_3, momB1_4_0_0, momB1_4_0_1, momB1_4_0_2, momB1_4_0_3, momB1_4_1_0, momB1_4_1_1, momB1_4_1_2, momB1_4_1_3, momB1_4_2_0, momB1_4_2_1, momB1_4_2_2, momB1_4_2_3, momB1_4_3_0, momB1_4_3_1, momB1_4_3_2, momB1_4_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_0_4 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 0 4 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 0 4 : ℂ)) := by
  rw [← Lval_eq_0_4]
  refine Kred_limit 0 4 k momA0_0_4 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_0_4_0
  · exact momA1_0_4_1
  · exact momA1_0_4_2
  · exact momA1_0_4_3

theorem Lval_eq_0_5 (k : Fin 4 → ℝ) : Lval 0 5 k = (KEH k 0 5 : ℂ) := by
  have a00 : momA2 0 5 0 0 = 0 := momA2_0_5_0_0
  have a01 : momA2 0 5 0 1 = 0 := momA2_0_5_0_1
  have a02 : momA2 0 5 0 2 = 0 := momA2_0_5_0_2
  have a03 : momA2 0 5 0 3 = 0 := momA2_0_5_0_3
  have a10 : momA2 0 5 1 0 = 0 := by rw [momA2_comm]; exact momA2_0_5_0_1
  have a11 : momA2 0 5 1 1 = 0 := momA2_0_5_1_1
  have a12 : momA2 0 5 1 2 = 96 := momA2_0_5_1_2
  have a13 : momA2 0 5 1 3 = 0 := momA2_0_5_1_3
  have a20 : momA2 0 5 2 0 = 0 := by rw [momA2_comm]; exact momA2_0_5_0_2
  have a21 : momA2 0 5 2 1 = 96 := by rw [momA2_comm]; exact momA2_0_5_1_2
  have a22 : momA2 0 5 2 2 = 0 := momA2_0_5_2_2
  have a23 : momA2 0 5 2 3 = 0 := momA2_0_5_2_3
  have a30 : momA2 0 5 3 0 = 0 := by rw [momA2_comm]; exact momA2_0_5_0_3
  have a31 : momA2 0 5 3 1 = 0 := by rw [momA2_comm]; exact momA2_0_5_1_3
  have a32 : momA2 0 5 3 2 = 0 := by rw [momA2_comm]; exact momA2_0_5_2_3
  have a33 : momA2 0 5 3 3 = 0 := momA2_0_5_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_0_0_0, momB1_0_0_1, momB1_0_0_2, momB1_0_0_3, momB1_0_1_0, momB1_0_1_1, momB1_0_1_2, momB1_0_1_3, momB1_0_2_0, momB1_0_2_1, momB1_0_2_2, momB1_0_2_3, momB1_0_3_0, momB1_0_3_1, momB1_0_3_2, momB1_0_3_3, momB1_5_0_0, momB1_5_0_1, momB1_5_0_2, momB1_5_0_3, momB1_5_1_0, momB1_5_1_1, momB1_5_1_2, momB1_5_1_3, momB1_5_2_0, momB1_5_2_1, momB1_5_2_2, momB1_5_2_3, momB1_5_3_0, momB1_5_3_1, momB1_5_3_2, momB1_5_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_0_5 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 0 5 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 0 5 : ℂ)) := by
  rw [← Lval_eq_0_5]
  refine Kred_limit 0 5 k momA0_0_5 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_0_5_0
  · exact momA1_0_5_1
  · exact momA1_0_5_2
  · exact momA1_0_5_3

theorem Lval_eq_0_6 (k : Fin 4 → ℝ) : Lval 0 6 k = (KEH k 0 6 : ℂ) := by
  have a00 : momA2 0 6 0 0 = 0 := momA2_0_6_0_0
  have a01 : momA2 0 6 0 1 = 0 := momA2_0_6_0_1
  have a02 : momA2 0 6 0 2 = 0 := momA2_0_6_0_2
  have a03 : momA2 0 6 0 3 = 0 := momA2_0_6_0_3
  have a10 : momA2 0 6 1 0 = 0 := by rw [momA2_comm]; exact momA2_0_6_0_1
  have a11 : momA2 0 6 1 1 = 0 := momA2_0_6_1_1
  have a12 : momA2 0 6 1 2 = 0 := momA2_0_6_1_2
  have a13 : momA2 0 6 1 3 = 96 := momA2_0_6_1_3
  have a20 : momA2 0 6 2 0 = 0 := by rw [momA2_comm]; exact momA2_0_6_0_2
  have a21 : momA2 0 6 2 1 = 0 := by rw [momA2_comm]; exact momA2_0_6_1_2
  have a22 : momA2 0 6 2 2 = 0 := momA2_0_6_2_2
  have a23 : momA2 0 6 2 3 = 0 := momA2_0_6_2_3
  have a30 : momA2 0 6 3 0 = 0 := by rw [momA2_comm]; exact momA2_0_6_0_3
  have a31 : momA2 0 6 3 1 = 96 := by rw [momA2_comm]; exact momA2_0_6_1_3
  have a32 : momA2 0 6 3 2 = 0 := by rw [momA2_comm]; exact momA2_0_6_2_3
  have a33 : momA2 0 6 3 3 = 0 := momA2_0_6_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_0_0_0, momB1_0_0_1, momB1_0_0_2, momB1_0_0_3, momB1_0_1_0, momB1_0_1_1, momB1_0_1_2, momB1_0_1_3, momB1_0_2_0, momB1_0_2_1, momB1_0_2_2, momB1_0_2_3, momB1_0_3_0, momB1_0_3_1, momB1_0_3_2, momB1_0_3_3, momB1_6_0_0, momB1_6_0_1, momB1_6_0_2, momB1_6_0_3, momB1_6_1_0, momB1_6_1_1, momB1_6_1_2, momB1_6_1_3, momB1_6_2_0, momB1_6_2_1, momB1_6_2_2, momB1_6_2_3, momB1_6_3_0, momB1_6_3_1, momB1_6_3_2, momB1_6_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_0_6 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 0 6 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 0 6 : ℂ)) := by
  rw [← Lval_eq_0_6]
  refine Kred_limit 0 6 k momA0_0_6 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_0_6_0
  · exact momA1_0_6_1
  · exact momA1_0_6_2
  · exact momA1_0_6_3

theorem Lval_eq_0_7 (k : Fin 4 → ℝ) : Lval 0 7 k = (KEH k 0 7 : ℂ) := by
  have a00 : momA2 0 7 0 0 = 0 := momA2_0_7_0_0
  have a01 : momA2 0 7 0 1 = 0 := momA2_0_7_0_1
  have a02 : momA2 0 7 0 2 = 0 := momA2_0_7_0_2
  have a03 : momA2 0 7 0 3 = 0 := momA2_0_7_0_3
  have a10 : momA2 0 7 1 0 = 0 := by rw [momA2_comm]; exact momA2_0_7_0_1
  have a11 : momA2 0 7 1 1 = -96 := momA2_0_7_1_1
  have a12 : momA2 0 7 1 2 = 0 := momA2_0_7_1_2
  have a13 : momA2 0 7 1 3 = 0 := momA2_0_7_1_3
  have a20 : momA2 0 7 2 0 = 0 := by rw [momA2_comm]; exact momA2_0_7_0_2
  have a21 : momA2 0 7 2 1 = 0 := by rw [momA2_comm]; exact momA2_0_7_1_2
  have a22 : momA2 0 7 2 2 = 0 := momA2_0_7_2_2
  have a23 : momA2 0 7 2 3 = 0 := momA2_0_7_2_3
  have a30 : momA2 0 7 3 0 = 0 := by rw [momA2_comm]; exact momA2_0_7_0_3
  have a31 : momA2 0 7 3 1 = 0 := by rw [momA2_comm]; exact momA2_0_7_1_3
  have a32 : momA2 0 7 3 2 = 0 := by rw [momA2_comm]; exact momA2_0_7_2_3
  have a33 : momA2 0 7 3 3 = -96 := momA2_0_7_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_0_0_0, momB1_0_0_1, momB1_0_0_2, momB1_0_0_3, momB1_0_1_0, momB1_0_1_1, momB1_0_1_2, momB1_0_1_3, momB1_0_2_0, momB1_0_2_1, momB1_0_2_2, momB1_0_2_3, momB1_0_3_0, momB1_0_3_1, momB1_0_3_2, momB1_0_3_3, momB1_7_0_0, momB1_7_0_1, momB1_7_0_2, momB1_7_0_3, momB1_7_1_0, momB1_7_1_1, momB1_7_1_2, momB1_7_1_3, momB1_7_2_0, momB1_7_2_1, momB1_7_2_2, momB1_7_2_3, momB1_7_3_0, momB1_7_3_1, momB1_7_3_2, momB1_7_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_0_7 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 0 7 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 0 7 : ℂ)) := by
  rw [← Lval_eq_0_7]
  refine Kred_limit 0 7 k momA0_0_7 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_0_7_0
  · exact momA1_0_7_1
  · exact momA1_0_7_2
  · exact momA1_0_7_3

theorem Lval_eq_0_8 (k : Fin 4 → ℝ) : Lval 0 8 k = (KEH k 0 8 : ℂ) := by
  have a00 : momA2 0 8 0 0 = 0 := momA2_0_8_0_0
  have a01 : momA2 0 8 0 1 = 0 := momA2_0_8_0_1
  have a02 : momA2 0 8 0 2 = 0 := momA2_0_8_0_2
  have a03 : momA2 0 8 0 3 = 0 := momA2_0_8_0_3
  have a10 : momA2 0 8 1 0 = 0 := by rw [momA2_comm]; exact momA2_0_8_0_1
  have a11 : momA2 0 8 1 1 = 0 := momA2_0_8_1_1
  have a12 : momA2 0 8 1 2 = 0 := momA2_0_8_1_2
  have a13 : momA2 0 8 1 3 = 0 := momA2_0_8_1_3
  have a20 : momA2 0 8 2 0 = 0 := by rw [momA2_comm]; exact momA2_0_8_0_2
  have a21 : momA2 0 8 2 1 = 0 := by rw [momA2_comm]; exact momA2_0_8_1_2
  have a22 : momA2 0 8 2 2 = 0 := momA2_0_8_2_2
  have a23 : momA2 0 8 2 3 = 96 := momA2_0_8_2_3
  have a30 : momA2 0 8 3 0 = 0 := by rw [momA2_comm]; exact momA2_0_8_0_3
  have a31 : momA2 0 8 3 1 = 0 := by rw [momA2_comm]; exact momA2_0_8_1_3
  have a32 : momA2 0 8 3 2 = 96 := by rw [momA2_comm]; exact momA2_0_8_2_3
  have a33 : momA2 0 8 3 3 = 0 := momA2_0_8_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_0_0_0, momB1_0_0_1, momB1_0_0_2, momB1_0_0_3, momB1_0_1_0, momB1_0_1_1, momB1_0_1_2, momB1_0_1_3, momB1_0_2_0, momB1_0_2_1, momB1_0_2_2, momB1_0_2_3, momB1_0_3_0, momB1_0_3_1, momB1_0_3_2, momB1_0_3_3, momB1_8_0_0, momB1_8_0_1, momB1_8_0_2, momB1_8_0_3, momB1_8_1_0, momB1_8_1_1, momB1_8_1_2, momB1_8_1_3, momB1_8_2_0, momB1_8_2_1, momB1_8_2_2, momB1_8_2_3, momB1_8_3_0, momB1_8_3_1, momB1_8_3_2, momB1_8_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_0_8 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 0 8 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 0 8 : ℂ)) := by
  rw [← Lval_eq_0_8]
  refine Kred_limit 0 8 k momA0_0_8 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_0_8_0
  · exact momA1_0_8_1
  · exact momA1_0_8_2
  · exact momA1_0_8_3

theorem Lval_eq_0_9 (k : Fin 4 → ℝ) : Lval 0 9 k = (KEH k 0 9 : ℂ) := by
  have a00 : momA2 0 9 0 0 = 0 := momA2_0_9_0_0
  have a01 : momA2 0 9 0 1 = 0 := momA2_0_9_0_1
  have a02 : momA2 0 9 0 2 = 0 := momA2_0_9_0_2
  have a03 : momA2 0 9 0 3 = 0 := momA2_0_9_0_3
  have a10 : momA2 0 9 1 0 = 0 := by rw [momA2_comm]; exact momA2_0_9_0_1
  have a11 : momA2 0 9 1 1 = -96 := momA2_0_9_1_1
  have a12 : momA2 0 9 1 2 = 0 := momA2_0_9_1_2
  have a13 : momA2 0 9 1 3 = 0 := momA2_0_9_1_3
  have a20 : momA2 0 9 2 0 = 0 := by rw [momA2_comm]; exact momA2_0_9_0_2
  have a21 : momA2 0 9 2 1 = 0 := by rw [momA2_comm]; exact momA2_0_9_1_2
  have a22 : momA2 0 9 2 2 = -96 := momA2_0_9_2_2
  have a23 : momA2 0 9 2 3 = 0 := momA2_0_9_2_3
  have a30 : momA2 0 9 3 0 = 0 := by rw [momA2_comm]; exact momA2_0_9_0_3
  have a31 : momA2 0 9 3 1 = 0 := by rw [momA2_comm]; exact momA2_0_9_1_3
  have a32 : momA2 0 9 3 2 = 0 := by rw [momA2_comm]; exact momA2_0_9_2_3
  have a33 : momA2 0 9 3 3 = 0 := momA2_0_9_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_0_0_0, momB1_0_0_1, momB1_0_0_2, momB1_0_0_3, momB1_0_1_0, momB1_0_1_1, momB1_0_1_2, momB1_0_1_3, momB1_0_2_0, momB1_0_2_1, momB1_0_2_2, momB1_0_2_3, momB1_0_3_0, momB1_0_3_1, momB1_0_3_2, momB1_0_3_3, momB1_9_0_0, momB1_9_0_1, momB1_9_0_2, momB1_9_0_3, momB1_9_1_0, momB1_9_1_1, momB1_9_1_2, momB1_9_1_3, momB1_9_2_0, momB1_9_2_1, momB1_9_2_2, momB1_9_2_3, momB1_9_3_0, momB1_9_3_1, momB1_9_3_2, momB1_9_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_0_9 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 0 9 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 0 9 : ℂ)) := by
  rw [← Lval_eq_0_9]
  refine Kred_limit 0 9 k momA0_0_9 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_0_9_0
  · exact momA1_0_9_1
  · exact momA1_0_9_2
  · exact momA1_0_9_3

theorem Lval_eq_1_1 (k : Fin 4 → ℝ) : Lval 1 1 k = (KEH k 1 1 : ℂ) := by
  have a00 : momA2 1 1 0 0 = 0 := momA2_1_1_0_0
  have a01 : momA2 1 1 0 1 = 0 := momA2_1_1_0_1
  have a02 : momA2 1 1 0 2 = 0 := momA2_1_1_0_2
  have a03 : momA2 1 1 0 3 = 0 := momA2_1_1_0_3
  have a10 : momA2 1 1 1 0 = 0 := by rw [momA2_comm]; exact momA2_1_1_0_1
  have a11 : momA2 1 1 1 1 = 0 := momA2_1_1_1_1
  have a12 : momA2 1 1 1 2 = 0 := momA2_1_1_1_2
  have a13 : momA2 1 1 1 3 = 0 := momA2_1_1_1_3
  have a20 : momA2 1 1 2 0 = 0 := by rw [momA2_comm]; exact momA2_1_1_0_2
  have a21 : momA2 1 1 2 1 = 0 := by rw [momA2_comm]; exact momA2_1_1_1_2
  have a22 : momA2 1 1 2 2 = 192 := momA2_1_1_2_2
  have a23 : momA2 1 1 2 3 = 0 := momA2_1_1_2_3
  have a30 : momA2 1 1 3 0 = 0 := by rw [momA2_comm]; exact momA2_1_1_0_3
  have a31 : momA2 1 1 3 1 = 0 := by rw [momA2_comm]; exact momA2_1_1_1_3
  have a32 : momA2 1 1 3 2 = 0 := by rw [momA2_comm]; exact momA2_1_1_2_3
  have a33 : momA2 1 1 3 3 = 192 := momA2_1_1_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_1_0_0, momB1_1_0_1, momB1_1_0_2, momB1_1_0_3, momB1_1_1_0, momB1_1_1_1, momB1_1_1_2, momB1_1_1_3, momB1_1_2_0, momB1_1_2_1, momB1_1_2_2, momB1_1_2_3, momB1_1_3_0, momB1_1_3_1, momB1_1_3_2, momB1_1_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_1_1 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 1 1 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 1 1 : ℂ)) := by
  rw [← Lval_eq_1_1]
  refine Kred_limit 1 1 k momA0_1_1 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_1_1_0
  · exact momA1_1_1_1
  · exact momA1_1_1_2
  · exact momA1_1_1_3

theorem Lval_eq_1_2 (k : Fin 4 → ℝ) : Lval 1 2 k = (KEH k 1 2 : ℂ) := by
  have a00 : momA2 1 2 0 0 = 0 := momA2_1_2_0_0
  have a01 : momA2 1 2 0 1 = 0 := momA2_1_2_0_1
  have a02 : momA2 1 2 0 2 = 0 := momA2_1_2_0_2
  have a03 : momA2 1 2 0 3 = 0 := momA2_1_2_0_3
  have a10 : momA2 1 2 1 0 = 0 := by rw [momA2_comm]; exact momA2_1_2_0_1
  have a11 : momA2 1 2 1 1 = 0 := momA2_1_2_1_1
  have a12 : momA2 1 2 1 2 = -96 := momA2_1_2_1_2
  have a13 : momA2 1 2 1 3 = 0 := momA2_1_2_1_3
  have a20 : momA2 1 2 2 0 = 0 := by rw [momA2_comm]; exact momA2_1_2_0_2
  have a21 : momA2 1 2 2 1 = -96 := by rw [momA2_comm]; exact momA2_1_2_1_2
  have a22 : momA2 1 2 2 2 = 0 := momA2_1_2_2_2
  have a23 : momA2 1 2 2 3 = 0 := momA2_1_2_2_3
  have a30 : momA2 1 2 3 0 = 0 := by rw [momA2_comm]; exact momA2_1_2_0_3
  have a31 : momA2 1 2 3 1 = 0 := by rw [momA2_comm]; exact momA2_1_2_1_3
  have a32 : momA2 1 2 3 2 = 0 := by rw [momA2_comm]; exact momA2_1_2_2_3
  have a33 : momA2 1 2 3 3 = 0 := momA2_1_2_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_1_0_0, momB1_1_0_1, momB1_1_0_2, momB1_1_0_3, momB1_1_1_0, momB1_1_1_1, momB1_1_1_2, momB1_1_1_3, momB1_1_2_0, momB1_1_2_1, momB1_1_2_2, momB1_1_2_3, momB1_1_3_0, momB1_1_3_1, momB1_1_3_2, momB1_1_3_3, momB1_2_0_0, momB1_2_0_1, momB1_2_0_2, momB1_2_0_3, momB1_2_1_0, momB1_2_1_1, momB1_2_1_2, momB1_2_1_3, momB1_2_2_0, momB1_2_2_1, momB1_2_2_2, momB1_2_2_3, momB1_2_3_0, momB1_2_3_1, momB1_2_3_2, momB1_2_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_1_2 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 1 2 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 1 2 : ℂ)) := by
  rw [← Lval_eq_1_2]
  refine Kred_limit 1 2 k momA0_1_2 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_1_2_0
  · exact momA1_1_2_1
  · exact momA1_1_2_2
  · exact momA1_1_2_3

theorem Lval_eq_1_3 (k : Fin 4 → ℝ) : Lval 1 3 k = (KEH k 1 3 : ℂ) := by
  have a00 : momA2 1 3 0 0 = 0 := momA2_1_3_0_0
  have a01 : momA2 1 3 0 1 = 0 := momA2_1_3_0_1
  have a02 : momA2 1 3 0 2 = 0 := momA2_1_3_0_2
  have a03 : momA2 1 3 0 3 = 0 := momA2_1_3_0_3
  have a10 : momA2 1 3 1 0 = 0 := by rw [momA2_comm]; exact momA2_1_3_0_1
  have a11 : momA2 1 3 1 1 = 0 := momA2_1_3_1_1
  have a12 : momA2 1 3 1 2 = 0 := momA2_1_3_1_2
  have a13 : momA2 1 3 1 3 = -96 := momA2_1_3_1_3
  have a20 : momA2 1 3 2 0 = 0 := by rw [momA2_comm]; exact momA2_1_3_0_2
  have a21 : momA2 1 3 2 1 = 0 := by rw [momA2_comm]; exact momA2_1_3_1_2
  have a22 : momA2 1 3 2 2 = 0 := momA2_1_3_2_2
  have a23 : momA2 1 3 2 3 = 0 := momA2_1_3_2_3
  have a30 : momA2 1 3 3 0 = 0 := by rw [momA2_comm]; exact momA2_1_3_0_3
  have a31 : momA2 1 3 3 1 = -96 := by rw [momA2_comm]; exact momA2_1_3_1_3
  have a32 : momA2 1 3 3 2 = 0 := by rw [momA2_comm]; exact momA2_1_3_2_3
  have a33 : momA2 1 3 3 3 = 0 := momA2_1_3_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_1_0_0, momB1_1_0_1, momB1_1_0_2, momB1_1_0_3, momB1_1_1_0, momB1_1_1_1, momB1_1_1_2, momB1_1_1_3, momB1_1_2_0, momB1_1_2_1, momB1_1_2_2, momB1_1_2_3, momB1_1_3_0, momB1_1_3_1, momB1_1_3_2, momB1_1_3_3, momB1_3_0_0, momB1_3_0_1, momB1_3_0_2, momB1_3_0_3, momB1_3_1_0, momB1_3_1_1, momB1_3_1_2, momB1_3_1_3, momB1_3_2_0, momB1_3_2_1, momB1_3_2_2, momB1_3_2_3, momB1_3_3_0, momB1_3_3_1, momB1_3_3_2, momB1_3_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_1_3 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 1 3 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 1 3 : ℂ)) := by
  rw [← Lval_eq_1_3]
  refine Kred_limit 1 3 k momA0_1_3 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_1_3_0
  · exact momA1_1_3_1
  · exact momA1_1_3_2
  · exact momA1_1_3_3

theorem Lval_eq_1_4 (k : Fin 4 → ℝ) : Lval 1 4 k = (KEH k 1 4 : ℂ) := by
  have a00 : momA2 1 4 0 0 = 0 := momA2_1_4_0_0
  have a01 : momA2 1 4 0 1 = 0 := momA2_1_4_0_1
  have a02 : momA2 1 4 0 2 = 0 := momA2_1_4_0_2
  have a03 : momA2 1 4 0 3 = 0 := momA2_1_4_0_3
  have a10 : momA2 1 4 1 0 = 0 := by rw [momA2_comm]; exact momA2_1_4_0_1
  have a11 : momA2 1 4 1 1 = 0 := momA2_1_4_1_1
  have a12 : momA2 1 4 1 2 = 0 := momA2_1_4_1_2
  have a13 : momA2 1 4 1 3 = 0 := momA2_1_4_1_3
  have a20 : momA2 1 4 2 0 = 0 := by rw [momA2_comm]; exact momA2_1_4_0_2
  have a21 : momA2 1 4 2 1 = 0 := by rw [momA2_comm]; exact momA2_1_4_1_2
  have a22 : momA2 1 4 2 2 = 0 := momA2_1_4_2_2
  have a23 : momA2 1 4 2 3 = 0 := momA2_1_4_2_3
  have a30 : momA2 1 4 3 0 = 0 := by rw [momA2_comm]; exact momA2_1_4_0_3
  have a31 : momA2 1 4 3 1 = 0 := by rw [momA2_comm]; exact momA2_1_4_1_3
  have a32 : momA2 1 4 3 2 = 0 := by rw [momA2_comm]; exact momA2_1_4_2_3
  have a33 : momA2 1 4 3 3 = 0 := momA2_1_4_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_1_0_0, momB1_1_0_1, momB1_1_0_2, momB1_1_0_3, momB1_1_1_0, momB1_1_1_1, momB1_1_1_2, momB1_1_1_3, momB1_1_2_0, momB1_1_2_1, momB1_1_2_2, momB1_1_2_3, momB1_1_3_0, momB1_1_3_1, momB1_1_3_2, momB1_1_3_3, momB1_4_0_0, momB1_4_0_1, momB1_4_0_2, momB1_4_0_3, momB1_4_1_0, momB1_4_1_1, momB1_4_1_2, momB1_4_1_3, momB1_4_2_0, momB1_4_2_1, momB1_4_2_2, momB1_4_2_3, momB1_4_3_0, momB1_4_3_1, momB1_4_3_2, momB1_4_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_1_4 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 1 4 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 1 4 : ℂ)) := by
  rw [← Lval_eq_1_4]
  refine Kred_limit 1 4 k momA0_1_4 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_1_4_0
  · exact momA1_1_4_1
  · exact momA1_1_4_2
  · exact momA1_1_4_3

theorem Lval_eq_1_5 (k : Fin 4 → ℝ) : Lval 1 5 k = (KEH k 1 5 : ℂ) := by
  have a00 : momA2 1 5 0 0 = 0 := momA2_1_5_0_0
  have a01 : momA2 1 5 0 1 = 0 := momA2_1_5_0_1
  have a02 : momA2 1 5 0 2 = -96 := momA2_1_5_0_2
  have a03 : momA2 1 5 0 3 = 0 := momA2_1_5_0_3
  have a10 : momA2 1 5 1 0 = 0 := by rw [momA2_comm]; exact momA2_1_5_0_1
  have a11 : momA2 1 5 1 1 = 0 := momA2_1_5_1_1
  have a12 : momA2 1 5 1 2 = 0 := momA2_1_5_1_2
  have a13 : momA2 1 5 1 3 = 0 := momA2_1_5_1_3
  have a20 : momA2 1 5 2 0 = -96 := by rw [momA2_comm]; exact momA2_1_5_0_2
  have a21 : momA2 1 5 2 1 = 0 := by rw [momA2_comm]; exact momA2_1_5_1_2
  have a22 : momA2 1 5 2 2 = 0 := momA2_1_5_2_2
  have a23 : momA2 1 5 2 3 = 0 := momA2_1_5_2_3
  have a30 : momA2 1 5 3 0 = 0 := by rw [momA2_comm]; exact momA2_1_5_0_3
  have a31 : momA2 1 5 3 1 = 0 := by rw [momA2_comm]; exact momA2_1_5_1_3
  have a32 : momA2 1 5 3 2 = 0 := by rw [momA2_comm]; exact momA2_1_5_2_3
  have a33 : momA2 1 5 3 3 = 0 := momA2_1_5_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_1_0_0, momB1_1_0_1, momB1_1_0_2, momB1_1_0_3, momB1_1_1_0, momB1_1_1_1, momB1_1_1_2, momB1_1_1_3, momB1_1_2_0, momB1_1_2_1, momB1_1_2_2, momB1_1_2_3, momB1_1_3_0, momB1_1_3_1, momB1_1_3_2, momB1_1_3_3, momB1_5_0_0, momB1_5_0_1, momB1_5_0_2, momB1_5_0_3, momB1_5_1_0, momB1_5_1_1, momB1_5_1_2, momB1_5_1_3, momB1_5_2_0, momB1_5_2_1, momB1_5_2_2, momB1_5_2_3, momB1_5_3_0, momB1_5_3_1, momB1_5_3_2, momB1_5_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_1_5 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 1 5 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 1 5 : ℂ)) := by
  rw [← Lval_eq_1_5]
  refine Kred_limit 1 5 k momA0_1_5 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_1_5_0
  · exact momA1_1_5_1
  · exact momA1_1_5_2
  · exact momA1_1_5_3

theorem Lval_eq_1_6 (k : Fin 4 → ℝ) : Lval 1 6 k = (KEH k 1 6 : ℂ) := by
  have a00 : momA2 1 6 0 0 = 0 := momA2_1_6_0_0
  have a01 : momA2 1 6 0 1 = 0 := momA2_1_6_0_1
  have a02 : momA2 1 6 0 2 = 0 := momA2_1_6_0_2
  have a03 : momA2 1 6 0 3 = -96 := momA2_1_6_0_3
  have a10 : momA2 1 6 1 0 = 0 := by rw [momA2_comm]; exact momA2_1_6_0_1
  have a11 : momA2 1 6 1 1 = 0 := momA2_1_6_1_1
  have a12 : momA2 1 6 1 2 = 0 := momA2_1_6_1_2
  have a13 : momA2 1 6 1 3 = 0 := momA2_1_6_1_3
  have a20 : momA2 1 6 2 0 = 0 := by rw [momA2_comm]; exact momA2_1_6_0_2
  have a21 : momA2 1 6 2 1 = 0 := by rw [momA2_comm]; exact momA2_1_6_1_2
  have a22 : momA2 1 6 2 2 = 0 := momA2_1_6_2_2
  have a23 : momA2 1 6 2 3 = 0 := momA2_1_6_2_3
  have a30 : momA2 1 6 3 0 = -96 := by rw [momA2_comm]; exact momA2_1_6_0_3
  have a31 : momA2 1 6 3 1 = 0 := by rw [momA2_comm]; exact momA2_1_6_1_3
  have a32 : momA2 1 6 3 2 = 0 := by rw [momA2_comm]; exact momA2_1_6_2_3
  have a33 : momA2 1 6 3 3 = 0 := momA2_1_6_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_1_0_0, momB1_1_0_1, momB1_1_0_2, momB1_1_0_3, momB1_1_1_0, momB1_1_1_1, momB1_1_1_2, momB1_1_1_3, momB1_1_2_0, momB1_1_2_1, momB1_1_2_2, momB1_1_2_3, momB1_1_3_0, momB1_1_3_1, momB1_1_3_2, momB1_1_3_3, momB1_6_0_0, momB1_6_0_1, momB1_6_0_2, momB1_6_0_3, momB1_6_1_0, momB1_6_1_1, momB1_6_1_2, momB1_6_1_3, momB1_6_2_0, momB1_6_2_1, momB1_6_2_2, momB1_6_2_3, momB1_6_3_0, momB1_6_3_1, momB1_6_3_2, momB1_6_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_1_6 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 1 6 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 1 6 : ℂ)) := by
  rw [← Lval_eq_1_6]
  refine Kred_limit 1 6 k momA0_1_6 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_1_6_0
  · exact momA1_1_6_1
  · exact momA1_1_6_2
  · exact momA1_1_6_3

theorem Lval_eq_1_7 (k : Fin 4 → ℝ) : Lval 1 7 k = (KEH k 1 7 : ℂ) := by
  have a00 : momA2 1 7 0 0 = 0 := momA2_1_7_0_0
  have a01 : momA2 1 7 0 1 = 96 := momA2_1_7_0_1
  have a02 : momA2 1 7 0 2 = 0 := momA2_1_7_0_2
  have a03 : momA2 1 7 0 3 = 0 := momA2_1_7_0_3
  have a10 : momA2 1 7 1 0 = 96 := by rw [momA2_comm]; exact momA2_1_7_0_1
  have a11 : momA2 1 7 1 1 = 0 := momA2_1_7_1_1
  have a12 : momA2 1 7 1 2 = 0 := momA2_1_7_1_2
  have a13 : momA2 1 7 1 3 = 0 := momA2_1_7_1_3
  have a20 : momA2 1 7 2 0 = 0 := by rw [momA2_comm]; exact momA2_1_7_0_2
  have a21 : momA2 1 7 2 1 = 0 := by rw [momA2_comm]; exact momA2_1_7_1_2
  have a22 : momA2 1 7 2 2 = 0 := momA2_1_7_2_2
  have a23 : momA2 1 7 2 3 = 0 := momA2_1_7_2_3
  have a30 : momA2 1 7 3 0 = 0 := by rw [momA2_comm]; exact momA2_1_7_0_3
  have a31 : momA2 1 7 3 1 = 0 := by rw [momA2_comm]; exact momA2_1_7_1_3
  have a32 : momA2 1 7 3 2 = 0 := by rw [momA2_comm]; exact momA2_1_7_2_3
  have a33 : momA2 1 7 3 3 = 0 := momA2_1_7_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_1_0_0, momB1_1_0_1, momB1_1_0_2, momB1_1_0_3, momB1_1_1_0, momB1_1_1_1, momB1_1_1_2, momB1_1_1_3, momB1_1_2_0, momB1_1_2_1, momB1_1_2_2, momB1_1_2_3, momB1_1_3_0, momB1_1_3_1, momB1_1_3_2, momB1_1_3_3, momB1_7_0_0, momB1_7_0_1, momB1_7_0_2, momB1_7_0_3, momB1_7_1_0, momB1_7_1_1, momB1_7_1_2, momB1_7_1_3, momB1_7_2_0, momB1_7_2_1, momB1_7_2_2, momB1_7_2_3, momB1_7_3_0, momB1_7_3_1, momB1_7_3_2, momB1_7_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_1_7 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 1 7 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 1 7 : ℂ)) := by
  rw [← Lval_eq_1_7]
  refine Kred_limit 1 7 k momA0_1_7 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_1_7_0
  · exact momA1_1_7_1
  · exact momA1_1_7_2
  · exact momA1_1_7_3

theorem Lval_eq_1_8 (k : Fin 4 → ℝ) : Lval 1 8 k = (KEH k 1 8 : ℂ) := by
  have a00 : momA2 1 8 0 0 = 0 := momA2_1_8_0_0
  have a01 : momA2 1 8 0 1 = 0 := momA2_1_8_0_1
  have a02 : momA2 1 8 0 2 = 0 := momA2_1_8_0_2
  have a03 : momA2 1 8 0 3 = 0 := momA2_1_8_0_3
  have a10 : momA2 1 8 1 0 = 0 := by rw [momA2_comm]; exact momA2_1_8_0_1
  have a11 : momA2 1 8 1 1 = 0 := momA2_1_8_1_1
  have a12 : momA2 1 8 1 2 = 0 := momA2_1_8_1_2
  have a13 : momA2 1 8 1 3 = 0 := momA2_1_8_1_3
  have a20 : momA2 1 8 2 0 = 0 := by rw [momA2_comm]; exact momA2_1_8_0_2
  have a21 : momA2 1 8 2 1 = 0 := by rw [momA2_comm]; exact momA2_1_8_1_2
  have a22 : momA2 1 8 2 2 = 0 := momA2_1_8_2_2
  have a23 : momA2 1 8 2 3 = 0 := momA2_1_8_2_3
  have a30 : momA2 1 8 3 0 = 0 := by rw [momA2_comm]; exact momA2_1_8_0_3
  have a31 : momA2 1 8 3 1 = 0 := by rw [momA2_comm]; exact momA2_1_8_1_3
  have a32 : momA2 1 8 3 2 = 0 := by rw [momA2_comm]; exact momA2_1_8_2_3
  have a33 : momA2 1 8 3 3 = 0 := momA2_1_8_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_1_0_0, momB1_1_0_1, momB1_1_0_2, momB1_1_0_3, momB1_1_1_0, momB1_1_1_1, momB1_1_1_2, momB1_1_1_3, momB1_1_2_0, momB1_1_2_1, momB1_1_2_2, momB1_1_2_3, momB1_1_3_0, momB1_1_3_1, momB1_1_3_2, momB1_1_3_3, momB1_8_0_0, momB1_8_0_1, momB1_8_0_2, momB1_8_0_3, momB1_8_1_0, momB1_8_1_1, momB1_8_1_2, momB1_8_1_3, momB1_8_2_0, momB1_8_2_1, momB1_8_2_2, momB1_8_2_3, momB1_8_3_0, momB1_8_3_1, momB1_8_3_2, momB1_8_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_1_8 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 1 8 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 1 8 : ℂ)) := by
  rw [← Lval_eq_1_8]
  refine Kred_limit 1 8 k momA0_1_8 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_1_8_0
  · exact momA1_1_8_1
  · exact momA1_1_8_2
  · exact momA1_1_8_3

theorem Lval_eq_1_9 (k : Fin 4 → ℝ) : Lval 1 9 k = (KEH k 1 9 : ℂ) := by
  have a00 : momA2 1 9 0 0 = 0 := momA2_1_9_0_0
  have a01 : momA2 1 9 0 1 = 96 := momA2_1_9_0_1
  have a02 : momA2 1 9 0 2 = 0 := momA2_1_9_0_2
  have a03 : momA2 1 9 0 3 = 0 := momA2_1_9_0_3
  have a10 : momA2 1 9 1 0 = 96 := by rw [momA2_comm]; exact momA2_1_9_0_1
  have a11 : momA2 1 9 1 1 = 0 := momA2_1_9_1_1
  have a12 : momA2 1 9 1 2 = 0 := momA2_1_9_1_2
  have a13 : momA2 1 9 1 3 = 0 := momA2_1_9_1_3
  have a20 : momA2 1 9 2 0 = 0 := by rw [momA2_comm]; exact momA2_1_9_0_2
  have a21 : momA2 1 9 2 1 = 0 := by rw [momA2_comm]; exact momA2_1_9_1_2
  have a22 : momA2 1 9 2 2 = 0 := momA2_1_9_2_2
  have a23 : momA2 1 9 2 3 = 0 := momA2_1_9_2_3
  have a30 : momA2 1 9 3 0 = 0 := by rw [momA2_comm]; exact momA2_1_9_0_3
  have a31 : momA2 1 9 3 1 = 0 := by rw [momA2_comm]; exact momA2_1_9_1_3
  have a32 : momA2 1 9 3 2 = 0 := by rw [momA2_comm]; exact momA2_1_9_2_3
  have a33 : momA2 1 9 3 3 = 0 := momA2_1_9_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_1_0_0, momB1_1_0_1, momB1_1_0_2, momB1_1_0_3, momB1_1_1_0, momB1_1_1_1, momB1_1_1_2, momB1_1_1_3, momB1_1_2_0, momB1_1_2_1, momB1_1_2_2, momB1_1_2_3, momB1_1_3_0, momB1_1_3_1, momB1_1_3_2, momB1_1_3_3, momB1_9_0_0, momB1_9_0_1, momB1_9_0_2, momB1_9_0_3, momB1_9_1_0, momB1_9_1_1, momB1_9_1_2, momB1_9_1_3, momB1_9_2_0, momB1_9_2_1, momB1_9_2_2, momB1_9_2_3, momB1_9_3_0, momB1_9_3_1, momB1_9_3_2, momB1_9_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_1_9 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 1 9 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 1 9 : ℂ)) := by
  rw [← Lval_eq_1_9]
  refine Kred_limit 1 9 k momA0_1_9 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_1_9_0
  · exact momA1_1_9_1
  · exact momA1_1_9_2
  · exact momA1_1_9_3

theorem Lval_eq_2_2 (k : Fin 4 → ℝ) : Lval 2 2 k = (KEH k 2 2 : ℂ) := by
  have a00 : momA2 2 2 0 0 = 0 := momA2_2_2_0_0
  have a01 : momA2 2 2 0 1 = 0 := momA2_2_2_0_1
  have a02 : momA2 2 2 0 2 = 0 := momA2_2_2_0_2
  have a03 : momA2 2 2 0 3 = 0 := momA2_2_2_0_3
  have a10 : momA2 2 2 1 0 = 0 := by rw [momA2_comm]; exact momA2_2_2_0_1
  have a11 : momA2 2 2 1 1 = 192 := momA2_2_2_1_1
  have a12 : momA2 2 2 1 2 = 0 := momA2_2_2_1_2
  have a13 : momA2 2 2 1 3 = 0 := momA2_2_2_1_3
  have a20 : momA2 2 2 2 0 = 0 := by rw [momA2_comm]; exact momA2_2_2_0_2
  have a21 : momA2 2 2 2 1 = 0 := by rw [momA2_comm]; exact momA2_2_2_1_2
  have a22 : momA2 2 2 2 2 = 0 := momA2_2_2_2_2
  have a23 : momA2 2 2 2 3 = 0 := momA2_2_2_2_3
  have a30 : momA2 2 2 3 0 = 0 := by rw [momA2_comm]; exact momA2_2_2_0_3
  have a31 : momA2 2 2 3 1 = 0 := by rw [momA2_comm]; exact momA2_2_2_1_3
  have a32 : momA2 2 2 3 2 = 0 := by rw [momA2_comm]; exact momA2_2_2_2_3
  have a33 : momA2 2 2 3 3 = 192 := momA2_2_2_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_2_0_0, momB1_2_0_1, momB1_2_0_2, momB1_2_0_3, momB1_2_1_0, momB1_2_1_1, momB1_2_1_2, momB1_2_1_3, momB1_2_2_0, momB1_2_2_1, momB1_2_2_2, momB1_2_2_3, momB1_2_3_0, momB1_2_3_1, momB1_2_3_2, momB1_2_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_2_2 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 2 2 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 2 2 : ℂ)) := by
  rw [← Lval_eq_2_2]
  refine Kred_limit 2 2 k momA0_2_2 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_2_2_0
  · exact momA1_2_2_1
  · exact momA1_2_2_2
  · exact momA1_2_2_3

theorem Lval_eq_2_3 (k : Fin 4 → ℝ) : Lval 2 3 k = (KEH k 2 3 : ℂ) := by
  have a00 : momA2 2 3 0 0 = 0 := momA2_2_3_0_0
  have a01 : momA2 2 3 0 1 = 0 := momA2_2_3_0_1
  have a02 : momA2 2 3 0 2 = 0 := momA2_2_3_0_2
  have a03 : momA2 2 3 0 3 = 0 := momA2_2_3_0_3
  have a10 : momA2 2 3 1 0 = 0 := by rw [momA2_comm]; exact momA2_2_3_0_1
  have a11 : momA2 2 3 1 1 = 0 := momA2_2_3_1_1
  have a12 : momA2 2 3 1 2 = 0 := momA2_2_3_1_2
  have a13 : momA2 2 3 1 3 = 0 := momA2_2_3_1_3
  have a20 : momA2 2 3 2 0 = 0 := by rw [momA2_comm]; exact momA2_2_3_0_2
  have a21 : momA2 2 3 2 1 = 0 := by rw [momA2_comm]; exact momA2_2_3_1_2
  have a22 : momA2 2 3 2 2 = 0 := momA2_2_3_2_2
  have a23 : momA2 2 3 2 3 = -96 := momA2_2_3_2_3
  have a30 : momA2 2 3 3 0 = 0 := by rw [momA2_comm]; exact momA2_2_3_0_3
  have a31 : momA2 2 3 3 1 = 0 := by rw [momA2_comm]; exact momA2_2_3_1_3
  have a32 : momA2 2 3 3 2 = -96 := by rw [momA2_comm]; exact momA2_2_3_2_3
  have a33 : momA2 2 3 3 3 = 0 := momA2_2_3_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_2_0_0, momB1_2_0_1, momB1_2_0_2, momB1_2_0_3, momB1_2_1_0, momB1_2_1_1, momB1_2_1_2, momB1_2_1_3, momB1_2_2_0, momB1_2_2_1, momB1_2_2_2, momB1_2_2_3, momB1_2_3_0, momB1_2_3_1, momB1_2_3_2, momB1_2_3_3, momB1_3_0_0, momB1_3_0_1, momB1_3_0_2, momB1_3_0_3, momB1_3_1_0, momB1_3_1_1, momB1_3_1_2, momB1_3_1_3, momB1_3_2_0, momB1_3_2_1, momB1_3_2_2, momB1_3_2_3, momB1_3_3_0, momB1_3_3_1, momB1_3_3_2, momB1_3_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_2_3 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 2 3 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 2 3 : ℂ)) := by
  rw [← Lval_eq_2_3]
  refine Kred_limit 2 3 k momA0_2_3 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_2_3_0
  · exact momA1_2_3_1
  · exact momA1_2_3_2
  · exact momA1_2_3_3

theorem Lval_eq_2_4 (k : Fin 4 → ℝ) : Lval 2 4 k = (KEH k 2 4 : ℂ) := by
  have a00 : momA2 2 4 0 0 = 0 := momA2_2_4_0_0
  have a01 : momA2 2 4 0 1 = 0 := momA2_2_4_0_1
  have a02 : momA2 2 4 0 2 = 96 := momA2_2_4_0_2
  have a03 : momA2 2 4 0 3 = 0 := momA2_2_4_0_3
  have a10 : momA2 2 4 1 0 = 0 := by rw [momA2_comm]; exact momA2_2_4_0_1
  have a11 : momA2 2 4 1 1 = 0 := momA2_2_4_1_1
  have a12 : momA2 2 4 1 2 = 0 := momA2_2_4_1_2
  have a13 : momA2 2 4 1 3 = 0 := momA2_2_4_1_3
  have a20 : momA2 2 4 2 0 = 96 := by rw [momA2_comm]; exact momA2_2_4_0_2
  have a21 : momA2 2 4 2 1 = 0 := by rw [momA2_comm]; exact momA2_2_4_1_2
  have a22 : momA2 2 4 2 2 = 0 := momA2_2_4_2_2
  have a23 : momA2 2 4 2 3 = 0 := momA2_2_4_2_3
  have a30 : momA2 2 4 3 0 = 0 := by rw [momA2_comm]; exact momA2_2_4_0_3
  have a31 : momA2 2 4 3 1 = 0 := by rw [momA2_comm]; exact momA2_2_4_1_3
  have a32 : momA2 2 4 3 2 = 0 := by rw [momA2_comm]; exact momA2_2_4_2_3
  have a33 : momA2 2 4 3 3 = 0 := momA2_2_4_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_2_0_0, momB1_2_0_1, momB1_2_0_2, momB1_2_0_3, momB1_2_1_0, momB1_2_1_1, momB1_2_1_2, momB1_2_1_3, momB1_2_2_0, momB1_2_2_1, momB1_2_2_2, momB1_2_2_3, momB1_2_3_0, momB1_2_3_1, momB1_2_3_2, momB1_2_3_3, momB1_4_0_0, momB1_4_0_1, momB1_4_0_2, momB1_4_0_3, momB1_4_1_0, momB1_4_1_1, momB1_4_1_2, momB1_4_1_3, momB1_4_2_0, momB1_4_2_1, momB1_4_2_2, momB1_4_2_3, momB1_4_3_0, momB1_4_3_1, momB1_4_3_2, momB1_4_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_2_4 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 2 4 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 2 4 : ℂ)) := by
  rw [← Lval_eq_2_4]
  refine Kred_limit 2 4 k momA0_2_4 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_2_4_0
  · exact momA1_2_4_1
  · exact momA1_2_4_2
  · exact momA1_2_4_3

theorem Lval_eq_2_5 (k : Fin 4 → ℝ) : Lval 2 5 k = (KEH k 2 5 : ℂ) := by
  have a00 : momA2 2 5 0 0 = 0 := momA2_2_5_0_0
  have a01 : momA2 2 5 0 1 = -96 := momA2_2_5_0_1
  have a02 : momA2 2 5 0 2 = 0 := momA2_2_5_0_2
  have a03 : momA2 2 5 0 3 = 0 := momA2_2_5_0_3
  have a10 : momA2 2 5 1 0 = -96 := by rw [momA2_comm]; exact momA2_2_5_0_1
  have a11 : momA2 2 5 1 1 = 0 := momA2_2_5_1_1
  have a12 : momA2 2 5 1 2 = 0 := momA2_2_5_1_2
  have a13 : momA2 2 5 1 3 = 0 := momA2_2_5_1_3
  have a20 : momA2 2 5 2 0 = 0 := by rw [momA2_comm]; exact momA2_2_5_0_2
  have a21 : momA2 2 5 2 1 = 0 := by rw [momA2_comm]; exact momA2_2_5_1_2
  have a22 : momA2 2 5 2 2 = 0 := momA2_2_5_2_2
  have a23 : momA2 2 5 2 3 = 0 := momA2_2_5_2_3
  have a30 : momA2 2 5 3 0 = 0 := by rw [momA2_comm]; exact momA2_2_5_0_3
  have a31 : momA2 2 5 3 1 = 0 := by rw [momA2_comm]; exact momA2_2_5_1_3
  have a32 : momA2 2 5 3 2 = 0 := by rw [momA2_comm]; exact momA2_2_5_2_3
  have a33 : momA2 2 5 3 3 = 0 := momA2_2_5_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_2_0_0, momB1_2_0_1, momB1_2_0_2, momB1_2_0_3, momB1_2_1_0, momB1_2_1_1, momB1_2_1_2, momB1_2_1_3, momB1_2_2_0, momB1_2_2_1, momB1_2_2_2, momB1_2_2_3, momB1_2_3_0, momB1_2_3_1, momB1_2_3_2, momB1_2_3_3, momB1_5_0_0, momB1_5_0_1, momB1_5_0_2, momB1_5_0_3, momB1_5_1_0, momB1_5_1_1, momB1_5_1_2, momB1_5_1_3, momB1_5_2_0, momB1_5_2_1, momB1_5_2_2, momB1_5_2_3, momB1_5_3_0, momB1_5_3_1, momB1_5_3_2, momB1_5_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_2_5 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 2 5 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 2 5 : ℂ)) := by
  rw [← Lval_eq_2_5]
  refine Kred_limit 2 5 k momA0_2_5 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_2_5_0
  · exact momA1_2_5_1
  · exact momA1_2_5_2
  · exact momA1_2_5_3

theorem Lval_eq_2_6 (k : Fin 4 → ℝ) : Lval 2 6 k = (KEH k 2 6 : ℂ) := by
  have a00 : momA2 2 6 0 0 = 0 := momA2_2_6_0_0
  have a01 : momA2 2 6 0 1 = 0 := momA2_2_6_0_1
  have a02 : momA2 2 6 0 2 = 0 := momA2_2_6_0_2
  have a03 : momA2 2 6 0 3 = 0 := momA2_2_6_0_3
  have a10 : momA2 2 6 1 0 = 0 := by rw [momA2_comm]; exact momA2_2_6_0_1
  have a11 : momA2 2 6 1 1 = 0 := momA2_2_6_1_1
  have a12 : momA2 2 6 1 2 = 0 := momA2_2_6_1_2
  have a13 : momA2 2 6 1 3 = 0 := momA2_2_6_1_3
  have a20 : momA2 2 6 2 0 = 0 := by rw [momA2_comm]; exact momA2_2_6_0_2
  have a21 : momA2 2 6 2 1 = 0 := by rw [momA2_comm]; exact momA2_2_6_1_2
  have a22 : momA2 2 6 2 2 = 0 := momA2_2_6_2_2
  have a23 : momA2 2 6 2 3 = 0 := momA2_2_6_2_3
  have a30 : momA2 2 6 3 0 = 0 := by rw [momA2_comm]; exact momA2_2_6_0_3
  have a31 : momA2 2 6 3 1 = 0 := by rw [momA2_comm]; exact momA2_2_6_1_3
  have a32 : momA2 2 6 3 2 = 0 := by rw [momA2_comm]; exact momA2_2_6_2_3
  have a33 : momA2 2 6 3 3 = 0 := momA2_2_6_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_2_0_0, momB1_2_0_1, momB1_2_0_2, momB1_2_0_3, momB1_2_1_0, momB1_2_1_1, momB1_2_1_2, momB1_2_1_3, momB1_2_2_0, momB1_2_2_1, momB1_2_2_2, momB1_2_2_3, momB1_2_3_0, momB1_2_3_1, momB1_2_3_2, momB1_2_3_3, momB1_6_0_0, momB1_6_0_1, momB1_6_0_2, momB1_6_0_3, momB1_6_1_0, momB1_6_1_1, momB1_6_1_2, momB1_6_1_3, momB1_6_2_0, momB1_6_2_1, momB1_6_2_2, momB1_6_2_3, momB1_6_3_0, momB1_6_3_1, momB1_6_3_2, momB1_6_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_2_6 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 2 6 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 2 6 : ℂ)) := by
  rw [← Lval_eq_2_6]
  refine Kred_limit 2 6 k momA0_2_6 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_2_6_0
  · exact momA1_2_6_1
  · exact momA1_2_6_2
  · exact momA1_2_6_3

theorem Lval_eq_2_7 (k : Fin 4 → ℝ) : Lval 2 7 k = (KEH k 2 7 : ℂ) := by
  have a00 : momA2 2 7 0 0 = 0 := momA2_2_7_0_0
  have a01 : momA2 2 7 0 1 = 0 := momA2_2_7_0_1
  have a02 : momA2 2 7 0 2 = 0 := momA2_2_7_0_2
  have a03 : momA2 2 7 0 3 = 0 := momA2_2_7_0_3
  have a10 : momA2 2 7 1 0 = 0 := by rw [momA2_comm]; exact momA2_2_7_0_1
  have a11 : momA2 2 7 1 1 = 0 := momA2_2_7_1_1
  have a12 : momA2 2 7 1 2 = 0 := momA2_2_7_1_2
  have a13 : momA2 2 7 1 3 = 0 := momA2_2_7_1_3
  have a20 : momA2 2 7 2 0 = 0 := by rw [momA2_comm]; exact momA2_2_7_0_2
  have a21 : momA2 2 7 2 1 = 0 := by rw [momA2_comm]; exact momA2_2_7_1_2
  have a22 : momA2 2 7 2 2 = 0 := momA2_2_7_2_2
  have a23 : momA2 2 7 2 3 = 0 := momA2_2_7_2_3
  have a30 : momA2 2 7 3 0 = 0 := by rw [momA2_comm]; exact momA2_2_7_0_3
  have a31 : momA2 2 7 3 1 = 0 := by rw [momA2_comm]; exact momA2_2_7_1_3
  have a32 : momA2 2 7 3 2 = 0 := by rw [momA2_comm]; exact momA2_2_7_2_3
  have a33 : momA2 2 7 3 3 = 0 := momA2_2_7_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_2_0_0, momB1_2_0_1, momB1_2_0_2, momB1_2_0_3, momB1_2_1_0, momB1_2_1_1, momB1_2_1_2, momB1_2_1_3, momB1_2_2_0, momB1_2_2_1, momB1_2_2_2, momB1_2_2_3, momB1_2_3_0, momB1_2_3_1, momB1_2_3_2, momB1_2_3_3, momB1_7_0_0, momB1_7_0_1, momB1_7_0_2, momB1_7_0_3, momB1_7_1_0, momB1_7_1_1, momB1_7_1_2, momB1_7_1_3, momB1_7_2_0, momB1_7_2_1, momB1_7_2_2, momB1_7_2_3, momB1_7_3_0, momB1_7_3_1, momB1_7_3_2, momB1_7_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_2_7 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 2 7 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 2 7 : ℂ)) := by
  rw [← Lval_eq_2_7]
  refine Kred_limit 2 7 k momA0_2_7 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_2_7_0
  · exact momA1_2_7_1
  · exact momA1_2_7_2
  · exact momA1_2_7_3

theorem Lval_eq_2_8 (k : Fin 4 → ℝ) : Lval 2 8 k = (KEH k 2 8 : ℂ) := by
  have a00 : momA2 2 8 0 0 = 0 := momA2_2_8_0_0
  have a01 : momA2 2 8 0 1 = 0 := momA2_2_8_0_1
  have a02 : momA2 2 8 0 2 = 0 := momA2_2_8_0_2
  have a03 : momA2 2 8 0 3 = -96 := momA2_2_8_0_3
  have a10 : momA2 2 8 1 0 = 0 := by rw [momA2_comm]; exact momA2_2_8_0_1
  have a11 : momA2 2 8 1 1 = 0 := momA2_2_8_1_1
  have a12 : momA2 2 8 1 2 = 0 := momA2_2_8_1_2
  have a13 : momA2 2 8 1 3 = 0 := momA2_2_8_1_3
  have a20 : momA2 2 8 2 0 = 0 := by rw [momA2_comm]; exact momA2_2_8_0_2
  have a21 : momA2 2 8 2 1 = 0 := by rw [momA2_comm]; exact momA2_2_8_1_2
  have a22 : momA2 2 8 2 2 = 0 := momA2_2_8_2_2
  have a23 : momA2 2 8 2 3 = 0 := momA2_2_8_2_3
  have a30 : momA2 2 8 3 0 = -96 := by rw [momA2_comm]; exact momA2_2_8_0_3
  have a31 : momA2 2 8 3 1 = 0 := by rw [momA2_comm]; exact momA2_2_8_1_3
  have a32 : momA2 2 8 3 2 = 0 := by rw [momA2_comm]; exact momA2_2_8_2_3
  have a33 : momA2 2 8 3 3 = 0 := momA2_2_8_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_2_0_0, momB1_2_0_1, momB1_2_0_2, momB1_2_0_3, momB1_2_1_0, momB1_2_1_1, momB1_2_1_2, momB1_2_1_3, momB1_2_2_0, momB1_2_2_1, momB1_2_2_2, momB1_2_2_3, momB1_2_3_0, momB1_2_3_1, momB1_2_3_2, momB1_2_3_3, momB1_8_0_0, momB1_8_0_1, momB1_8_0_2, momB1_8_0_3, momB1_8_1_0, momB1_8_1_1, momB1_8_1_2, momB1_8_1_3, momB1_8_2_0, momB1_8_2_1, momB1_8_2_2, momB1_8_2_3, momB1_8_3_0, momB1_8_3_1, momB1_8_3_2, momB1_8_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_2_8 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 2 8 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 2 8 : ℂ)) := by
  rw [← Lval_eq_2_8]
  refine Kred_limit 2 8 k momA0_2_8 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_2_8_0
  · exact momA1_2_8_1
  · exact momA1_2_8_2
  · exact momA1_2_8_3

theorem Lval_eq_2_9 (k : Fin 4 → ℝ) : Lval 2 9 k = (KEH k 2 9 : ℂ) := by
  have a00 : momA2 2 9 0 0 = 0 := momA2_2_9_0_0
  have a01 : momA2 2 9 0 1 = 0 := momA2_2_9_0_1
  have a02 : momA2 2 9 0 2 = 96 := momA2_2_9_0_2
  have a03 : momA2 2 9 0 3 = 0 := momA2_2_9_0_3
  have a10 : momA2 2 9 1 0 = 0 := by rw [momA2_comm]; exact momA2_2_9_0_1
  have a11 : momA2 2 9 1 1 = 0 := momA2_2_9_1_1
  have a12 : momA2 2 9 1 2 = 0 := momA2_2_9_1_2
  have a13 : momA2 2 9 1 3 = 0 := momA2_2_9_1_3
  have a20 : momA2 2 9 2 0 = 96 := by rw [momA2_comm]; exact momA2_2_9_0_2
  have a21 : momA2 2 9 2 1 = 0 := by rw [momA2_comm]; exact momA2_2_9_1_2
  have a22 : momA2 2 9 2 2 = 0 := momA2_2_9_2_2
  have a23 : momA2 2 9 2 3 = 0 := momA2_2_9_2_3
  have a30 : momA2 2 9 3 0 = 0 := by rw [momA2_comm]; exact momA2_2_9_0_3
  have a31 : momA2 2 9 3 1 = 0 := by rw [momA2_comm]; exact momA2_2_9_1_3
  have a32 : momA2 2 9 3 2 = 0 := by rw [momA2_comm]; exact momA2_2_9_2_3
  have a33 : momA2 2 9 3 3 = 0 := momA2_2_9_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_2_0_0, momB1_2_0_1, momB1_2_0_2, momB1_2_0_3, momB1_2_1_0, momB1_2_1_1, momB1_2_1_2, momB1_2_1_3, momB1_2_2_0, momB1_2_2_1, momB1_2_2_2, momB1_2_2_3, momB1_2_3_0, momB1_2_3_1, momB1_2_3_2, momB1_2_3_3, momB1_9_0_0, momB1_9_0_1, momB1_9_0_2, momB1_9_0_3, momB1_9_1_0, momB1_9_1_1, momB1_9_1_2, momB1_9_1_3, momB1_9_2_0, momB1_9_2_1, momB1_9_2_2, momB1_9_2_3, momB1_9_3_0, momB1_9_3_1, momB1_9_3_2, momB1_9_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_2_9 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 2 9 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 2 9 : ℂ)) := by
  rw [← Lval_eq_2_9]
  refine Kred_limit 2 9 k momA0_2_9 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_2_9_0
  · exact momA1_2_9_1
  · exact momA1_2_9_2
  · exact momA1_2_9_3

theorem Lval_eq_3_3 (k : Fin 4 → ℝ) : Lval 3 3 k = (KEH k 3 3 : ℂ) := by
  have a00 : momA2 3 3 0 0 = 0 := momA2_3_3_0_0
  have a01 : momA2 3 3 0 1 = 0 := momA2_3_3_0_1
  have a02 : momA2 3 3 0 2 = 0 := momA2_3_3_0_2
  have a03 : momA2 3 3 0 3 = 0 := momA2_3_3_0_3
  have a10 : momA2 3 3 1 0 = 0 := by rw [momA2_comm]; exact momA2_3_3_0_1
  have a11 : momA2 3 3 1 1 = 192 := momA2_3_3_1_1
  have a12 : momA2 3 3 1 2 = 0 := momA2_3_3_1_2
  have a13 : momA2 3 3 1 3 = 0 := momA2_3_3_1_3
  have a20 : momA2 3 3 2 0 = 0 := by rw [momA2_comm]; exact momA2_3_3_0_2
  have a21 : momA2 3 3 2 1 = 0 := by rw [momA2_comm]; exact momA2_3_3_1_2
  have a22 : momA2 3 3 2 2 = 192 := momA2_3_3_2_2
  have a23 : momA2 3 3 2 3 = 0 := momA2_3_3_2_3
  have a30 : momA2 3 3 3 0 = 0 := by rw [momA2_comm]; exact momA2_3_3_0_3
  have a31 : momA2 3 3 3 1 = 0 := by rw [momA2_comm]; exact momA2_3_3_1_3
  have a32 : momA2 3 3 3 2 = 0 := by rw [momA2_comm]; exact momA2_3_3_2_3
  have a33 : momA2 3 3 3 3 = 0 := momA2_3_3_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_3_0_0, momB1_3_0_1, momB1_3_0_2, momB1_3_0_3, momB1_3_1_0, momB1_3_1_1, momB1_3_1_2, momB1_3_1_3, momB1_3_2_0, momB1_3_2_1, momB1_3_2_2, momB1_3_2_3, momB1_3_3_0, momB1_3_3_1, momB1_3_3_2, momB1_3_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_3_3 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 3 3 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 3 3 : ℂ)) := by
  rw [← Lval_eq_3_3]
  refine Kred_limit 3 3 k momA0_3_3 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_3_3_0
  · exact momA1_3_3_1
  · exact momA1_3_3_2
  · exact momA1_3_3_3

theorem Lval_eq_3_4 (k : Fin 4 → ℝ) : Lval 3 4 k = (KEH k 3 4 : ℂ) := by
  have a00 : momA2 3 4 0 0 = 0 := momA2_3_4_0_0
  have a01 : momA2 3 4 0 1 = 0 := momA2_3_4_0_1
  have a02 : momA2 3 4 0 2 = 0 := momA2_3_4_0_2
  have a03 : momA2 3 4 0 3 = 96 := momA2_3_4_0_3
  have a10 : momA2 3 4 1 0 = 0 := by rw [momA2_comm]; exact momA2_3_4_0_1
  have a11 : momA2 3 4 1 1 = 0 := momA2_3_4_1_1
  have a12 : momA2 3 4 1 2 = 0 := momA2_3_4_1_2
  have a13 : momA2 3 4 1 3 = 0 := momA2_3_4_1_3
  have a20 : momA2 3 4 2 0 = 0 := by rw [momA2_comm]; exact momA2_3_4_0_2
  have a21 : momA2 3 4 2 1 = 0 := by rw [momA2_comm]; exact momA2_3_4_1_2
  have a22 : momA2 3 4 2 2 = 0 := momA2_3_4_2_2
  have a23 : momA2 3 4 2 3 = 0 := momA2_3_4_2_3
  have a30 : momA2 3 4 3 0 = 96 := by rw [momA2_comm]; exact momA2_3_4_0_3
  have a31 : momA2 3 4 3 1 = 0 := by rw [momA2_comm]; exact momA2_3_4_1_3
  have a32 : momA2 3 4 3 2 = 0 := by rw [momA2_comm]; exact momA2_3_4_2_3
  have a33 : momA2 3 4 3 3 = 0 := momA2_3_4_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_3_0_0, momB1_3_0_1, momB1_3_0_2, momB1_3_0_3, momB1_3_1_0, momB1_3_1_1, momB1_3_1_2, momB1_3_1_3, momB1_3_2_0, momB1_3_2_1, momB1_3_2_2, momB1_3_2_3, momB1_3_3_0, momB1_3_3_1, momB1_3_3_2, momB1_3_3_3, momB1_4_0_0, momB1_4_0_1, momB1_4_0_2, momB1_4_0_3, momB1_4_1_0, momB1_4_1_1, momB1_4_1_2, momB1_4_1_3, momB1_4_2_0, momB1_4_2_1, momB1_4_2_2, momB1_4_2_3, momB1_4_3_0, momB1_4_3_1, momB1_4_3_2, momB1_4_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_3_4 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 3 4 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 3 4 : ℂ)) := by
  rw [← Lval_eq_3_4]
  refine Kred_limit 3 4 k momA0_3_4 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_3_4_0
  · exact momA1_3_4_1
  · exact momA1_3_4_2
  · exact momA1_3_4_3

theorem Lval_eq_3_5 (k : Fin 4 → ℝ) : Lval 3 5 k = (KEH k 3 5 : ℂ) := by
  have a00 : momA2 3 5 0 0 = 0 := momA2_3_5_0_0
  have a01 : momA2 3 5 0 1 = 0 := momA2_3_5_0_1
  have a02 : momA2 3 5 0 2 = 0 := momA2_3_5_0_2
  have a03 : momA2 3 5 0 3 = 0 := momA2_3_5_0_3
  have a10 : momA2 3 5 1 0 = 0 := by rw [momA2_comm]; exact momA2_3_5_0_1
  have a11 : momA2 3 5 1 1 = 0 := momA2_3_5_1_1
  have a12 : momA2 3 5 1 2 = 0 := momA2_3_5_1_2
  have a13 : momA2 3 5 1 3 = 0 := momA2_3_5_1_3
  have a20 : momA2 3 5 2 0 = 0 := by rw [momA2_comm]; exact momA2_3_5_0_2
  have a21 : momA2 3 5 2 1 = 0 := by rw [momA2_comm]; exact momA2_3_5_1_2
  have a22 : momA2 3 5 2 2 = 0 := momA2_3_5_2_2
  have a23 : momA2 3 5 2 3 = 0 := momA2_3_5_2_3
  have a30 : momA2 3 5 3 0 = 0 := by rw [momA2_comm]; exact momA2_3_5_0_3
  have a31 : momA2 3 5 3 1 = 0 := by rw [momA2_comm]; exact momA2_3_5_1_3
  have a32 : momA2 3 5 3 2 = 0 := by rw [momA2_comm]; exact momA2_3_5_2_3
  have a33 : momA2 3 5 3 3 = 0 := momA2_3_5_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_3_0_0, momB1_3_0_1, momB1_3_0_2, momB1_3_0_3, momB1_3_1_0, momB1_3_1_1, momB1_3_1_2, momB1_3_1_3, momB1_3_2_0, momB1_3_2_1, momB1_3_2_2, momB1_3_2_3, momB1_3_3_0, momB1_3_3_1, momB1_3_3_2, momB1_3_3_3, momB1_5_0_0, momB1_5_0_1, momB1_5_0_2, momB1_5_0_3, momB1_5_1_0, momB1_5_1_1, momB1_5_1_2, momB1_5_1_3, momB1_5_2_0, momB1_5_2_1, momB1_5_2_2, momB1_5_2_3, momB1_5_3_0, momB1_5_3_1, momB1_5_3_2, momB1_5_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_3_5 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 3 5 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 3 5 : ℂ)) := by
  rw [← Lval_eq_3_5]
  refine Kred_limit 3 5 k momA0_3_5 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_3_5_0
  · exact momA1_3_5_1
  · exact momA1_3_5_2
  · exact momA1_3_5_3

theorem Lval_eq_3_6 (k : Fin 4 → ℝ) : Lval 3 6 k = (KEH k 3 6 : ℂ) := by
  have a00 : momA2 3 6 0 0 = 0 := momA2_3_6_0_0
  have a01 : momA2 3 6 0 1 = -96 := momA2_3_6_0_1
  have a02 : momA2 3 6 0 2 = 0 := momA2_3_6_0_2
  have a03 : momA2 3 6 0 3 = 0 := momA2_3_6_0_3
  have a10 : momA2 3 6 1 0 = -96 := by rw [momA2_comm]; exact momA2_3_6_0_1
  have a11 : momA2 3 6 1 1 = 0 := momA2_3_6_1_1
  have a12 : momA2 3 6 1 2 = 0 := momA2_3_6_1_2
  have a13 : momA2 3 6 1 3 = 0 := momA2_3_6_1_3
  have a20 : momA2 3 6 2 0 = 0 := by rw [momA2_comm]; exact momA2_3_6_0_2
  have a21 : momA2 3 6 2 1 = 0 := by rw [momA2_comm]; exact momA2_3_6_1_2
  have a22 : momA2 3 6 2 2 = 0 := momA2_3_6_2_2
  have a23 : momA2 3 6 2 3 = 0 := momA2_3_6_2_3
  have a30 : momA2 3 6 3 0 = 0 := by rw [momA2_comm]; exact momA2_3_6_0_3
  have a31 : momA2 3 6 3 1 = 0 := by rw [momA2_comm]; exact momA2_3_6_1_3
  have a32 : momA2 3 6 3 2 = 0 := by rw [momA2_comm]; exact momA2_3_6_2_3
  have a33 : momA2 3 6 3 3 = 0 := momA2_3_6_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_3_0_0, momB1_3_0_1, momB1_3_0_2, momB1_3_0_3, momB1_3_1_0, momB1_3_1_1, momB1_3_1_2, momB1_3_1_3, momB1_3_2_0, momB1_3_2_1, momB1_3_2_2, momB1_3_2_3, momB1_3_3_0, momB1_3_3_1, momB1_3_3_2, momB1_3_3_3, momB1_6_0_0, momB1_6_0_1, momB1_6_0_2, momB1_6_0_3, momB1_6_1_0, momB1_6_1_1, momB1_6_1_2, momB1_6_1_3, momB1_6_2_0, momB1_6_2_1, momB1_6_2_2, momB1_6_2_3, momB1_6_3_0, momB1_6_3_1, momB1_6_3_2, momB1_6_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_3_6 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 3 6 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 3 6 : ℂ)) := by
  rw [← Lval_eq_3_6]
  refine Kred_limit 3 6 k momA0_3_6 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_3_6_0
  · exact momA1_3_6_1
  · exact momA1_3_6_2
  · exact momA1_3_6_3

theorem Lval_eq_3_7 (k : Fin 4 → ℝ) : Lval 3 7 k = (KEH k 3 7 : ℂ) := by
  have a00 : momA2 3 7 0 0 = 0 := momA2_3_7_0_0
  have a01 : momA2 3 7 0 1 = 0 := momA2_3_7_0_1
  have a02 : momA2 3 7 0 2 = 0 := momA2_3_7_0_2
  have a03 : momA2 3 7 0 3 = 96 := momA2_3_7_0_3
  have a10 : momA2 3 7 1 0 = 0 := by rw [momA2_comm]; exact momA2_3_7_0_1
  have a11 : momA2 3 7 1 1 = 0 := momA2_3_7_1_1
  have a12 : momA2 3 7 1 2 = 0 := momA2_3_7_1_2
  have a13 : momA2 3 7 1 3 = 0 := momA2_3_7_1_3
  have a20 : momA2 3 7 2 0 = 0 := by rw [momA2_comm]; exact momA2_3_7_0_2
  have a21 : momA2 3 7 2 1 = 0 := by rw [momA2_comm]; exact momA2_3_7_1_2
  have a22 : momA2 3 7 2 2 = 0 := momA2_3_7_2_2
  have a23 : momA2 3 7 2 3 = 0 := momA2_3_7_2_3
  have a30 : momA2 3 7 3 0 = 96 := by rw [momA2_comm]; exact momA2_3_7_0_3
  have a31 : momA2 3 7 3 1 = 0 := by rw [momA2_comm]; exact momA2_3_7_1_3
  have a32 : momA2 3 7 3 2 = 0 := by rw [momA2_comm]; exact momA2_3_7_2_3
  have a33 : momA2 3 7 3 3 = 0 := momA2_3_7_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_3_0_0, momB1_3_0_1, momB1_3_0_2, momB1_3_0_3, momB1_3_1_0, momB1_3_1_1, momB1_3_1_2, momB1_3_1_3, momB1_3_2_0, momB1_3_2_1, momB1_3_2_2, momB1_3_2_3, momB1_3_3_0, momB1_3_3_1, momB1_3_3_2, momB1_3_3_3, momB1_7_0_0, momB1_7_0_1, momB1_7_0_2, momB1_7_0_3, momB1_7_1_0, momB1_7_1_1, momB1_7_1_2, momB1_7_1_3, momB1_7_2_0, momB1_7_2_1, momB1_7_2_2, momB1_7_2_3, momB1_7_3_0, momB1_7_3_1, momB1_7_3_2, momB1_7_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_3_7 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 3 7 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 3 7 : ℂ)) := by
  rw [← Lval_eq_3_7]
  refine Kred_limit 3 7 k momA0_3_7 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_3_7_0
  · exact momA1_3_7_1
  · exact momA1_3_7_2
  · exact momA1_3_7_3

theorem Lval_eq_3_8 (k : Fin 4 → ℝ) : Lval 3 8 k = (KEH k 3 8 : ℂ) := by
  have a00 : momA2 3 8 0 0 = 0 := momA2_3_8_0_0
  have a01 : momA2 3 8 0 1 = 0 := momA2_3_8_0_1
  have a02 : momA2 3 8 0 2 = -96 := momA2_3_8_0_2
  have a03 : momA2 3 8 0 3 = 0 := momA2_3_8_0_3
  have a10 : momA2 3 8 1 0 = 0 := by rw [momA2_comm]; exact momA2_3_8_0_1
  have a11 : momA2 3 8 1 1 = 0 := momA2_3_8_1_1
  have a12 : momA2 3 8 1 2 = 0 := momA2_3_8_1_2
  have a13 : momA2 3 8 1 3 = 0 := momA2_3_8_1_3
  have a20 : momA2 3 8 2 0 = -96 := by rw [momA2_comm]; exact momA2_3_8_0_2
  have a21 : momA2 3 8 2 1 = 0 := by rw [momA2_comm]; exact momA2_3_8_1_2
  have a22 : momA2 3 8 2 2 = 0 := momA2_3_8_2_2
  have a23 : momA2 3 8 2 3 = 0 := momA2_3_8_2_3
  have a30 : momA2 3 8 3 0 = 0 := by rw [momA2_comm]; exact momA2_3_8_0_3
  have a31 : momA2 3 8 3 1 = 0 := by rw [momA2_comm]; exact momA2_3_8_1_3
  have a32 : momA2 3 8 3 2 = 0 := by rw [momA2_comm]; exact momA2_3_8_2_3
  have a33 : momA2 3 8 3 3 = 0 := momA2_3_8_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_3_0_0, momB1_3_0_1, momB1_3_0_2, momB1_3_0_3, momB1_3_1_0, momB1_3_1_1, momB1_3_1_2, momB1_3_1_3, momB1_3_2_0, momB1_3_2_1, momB1_3_2_2, momB1_3_2_3, momB1_3_3_0, momB1_3_3_1, momB1_3_3_2, momB1_3_3_3, momB1_8_0_0, momB1_8_0_1, momB1_8_0_2, momB1_8_0_3, momB1_8_1_0, momB1_8_1_1, momB1_8_1_2, momB1_8_1_3, momB1_8_2_0, momB1_8_2_1, momB1_8_2_2, momB1_8_2_3, momB1_8_3_0, momB1_8_3_1, momB1_8_3_2, momB1_8_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_3_8 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 3 8 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 3 8 : ℂ)) := by
  rw [← Lval_eq_3_8]
  refine Kred_limit 3 8 k momA0_3_8 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_3_8_0
  · exact momA1_3_8_1
  · exact momA1_3_8_2
  · exact momA1_3_8_3

theorem Lval_eq_3_9 (k : Fin 4 → ℝ) : Lval 3 9 k = (KEH k 3 9 : ℂ) := by
  have a00 : momA2 3 9 0 0 = 0 := momA2_3_9_0_0
  have a01 : momA2 3 9 0 1 = 0 := momA2_3_9_0_1
  have a02 : momA2 3 9 0 2 = 0 := momA2_3_9_0_2
  have a03 : momA2 3 9 0 3 = 0 := momA2_3_9_0_3
  have a10 : momA2 3 9 1 0 = 0 := by rw [momA2_comm]; exact momA2_3_9_0_1
  have a11 : momA2 3 9 1 1 = 0 := momA2_3_9_1_1
  have a12 : momA2 3 9 1 2 = 0 := momA2_3_9_1_2
  have a13 : momA2 3 9 1 3 = 0 := momA2_3_9_1_3
  have a20 : momA2 3 9 2 0 = 0 := by rw [momA2_comm]; exact momA2_3_9_0_2
  have a21 : momA2 3 9 2 1 = 0 := by rw [momA2_comm]; exact momA2_3_9_1_2
  have a22 : momA2 3 9 2 2 = 0 := momA2_3_9_2_2
  have a23 : momA2 3 9 2 3 = 0 := momA2_3_9_2_3
  have a30 : momA2 3 9 3 0 = 0 := by rw [momA2_comm]; exact momA2_3_9_0_3
  have a31 : momA2 3 9 3 1 = 0 := by rw [momA2_comm]; exact momA2_3_9_1_3
  have a32 : momA2 3 9 3 2 = 0 := by rw [momA2_comm]; exact momA2_3_9_2_3
  have a33 : momA2 3 9 3 3 = 0 := momA2_3_9_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_3_0_0, momB1_3_0_1, momB1_3_0_2, momB1_3_0_3, momB1_3_1_0, momB1_3_1_1, momB1_3_1_2, momB1_3_1_3, momB1_3_2_0, momB1_3_2_1, momB1_3_2_2, momB1_3_2_3, momB1_3_3_0, momB1_3_3_1, momB1_3_3_2, momB1_3_3_3, momB1_9_0_0, momB1_9_0_1, momB1_9_0_2, momB1_9_0_3, momB1_9_1_0, momB1_9_1_1, momB1_9_1_2, momB1_9_1_3, momB1_9_2_0, momB1_9_2_1, momB1_9_2_2, momB1_9_2_3, momB1_9_3_0, momB1_9_3_1, momB1_9_3_2, momB1_9_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_3_9 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 3 9 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 3 9 : ℂ)) := by
  rw [← Lval_eq_3_9]
  refine Kred_limit 3 9 k momA0_3_9 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_3_9_0
  · exact momA1_3_9_1
  · exact momA1_3_9_2
  · exact momA1_3_9_3

theorem Lval_eq_4_4 (k : Fin 4 → ℝ) : Lval 4 4 k = (KEH k 4 4 : ℂ) := by
  have a00 : momA2 4 4 0 0 = 0 := momA2_4_4_0_0
  have a01 : momA2 4 4 0 1 = 0 := momA2_4_4_0_1
  have a02 : momA2 4 4 0 2 = 0 := momA2_4_4_0_2
  have a03 : momA2 4 4 0 3 = 0 := momA2_4_4_0_3
  have a10 : momA2 4 4 1 0 = 0 := by rw [momA2_comm]; exact momA2_4_4_0_1
  have a11 : momA2 4 4 1 1 = 0 := momA2_4_4_1_1
  have a12 : momA2 4 4 1 2 = 0 := momA2_4_4_1_2
  have a13 : momA2 4 4 1 3 = 0 := momA2_4_4_1_3
  have a20 : momA2 4 4 2 0 = 0 := by rw [momA2_comm]; exact momA2_4_4_0_2
  have a21 : momA2 4 4 2 1 = 0 := by rw [momA2_comm]; exact momA2_4_4_1_2
  have a22 : momA2 4 4 2 2 = 0 := momA2_4_4_2_2
  have a23 : momA2 4 4 2 3 = 0 := momA2_4_4_2_3
  have a30 : momA2 4 4 3 0 = 0 := by rw [momA2_comm]; exact momA2_4_4_0_3
  have a31 : momA2 4 4 3 1 = 0 := by rw [momA2_comm]; exact momA2_4_4_1_3
  have a32 : momA2 4 4 3 2 = 0 := by rw [momA2_comm]; exact momA2_4_4_2_3
  have a33 : momA2 4 4 3 3 = 0 := momA2_4_4_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_4_0_0, momB1_4_0_1, momB1_4_0_2, momB1_4_0_3, momB1_4_1_0, momB1_4_1_1, momB1_4_1_2, momB1_4_1_3, momB1_4_2_0, momB1_4_2_1, momB1_4_2_2, momB1_4_2_3, momB1_4_3_0, momB1_4_3_1, momB1_4_3_2, momB1_4_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_4_4 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 4 4 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 4 4 : ℂ)) := by
  rw [← Lval_eq_4_4]
  refine Kred_limit 4 4 k momA0_4_4 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_4_4_0
  · exact momA1_4_4_1
  · exact momA1_4_4_2
  · exact momA1_4_4_3

theorem Lval_eq_4_5 (k : Fin 4 → ℝ) : Lval 4 5 k = (KEH k 4 5 : ℂ) := by
  have a00 : momA2 4 5 0 0 = 0 := momA2_4_5_0_0
  have a01 : momA2 4 5 0 1 = 0 := momA2_4_5_0_1
  have a02 : momA2 4 5 0 2 = 0 := momA2_4_5_0_2
  have a03 : momA2 4 5 0 3 = 0 := momA2_4_5_0_3
  have a10 : momA2 4 5 1 0 = 0 := by rw [momA2_comm]; exact momA2_4_5_0_1
  have a11 : momA2 4 5 1 1 = 0 := momA2_4_5_1_1
  have a12 : momA2 4 5 1 2 = 0 := momA2_4_5_1_2
  have a13 : momA2 4 5 1 3 = 0 := momA2_4_5_1_3
  have a20 : momA2 4 5 2 0 = 0 := by rw [momA2_comm]; exact momA2_4_5_0_2
  have a21 : momA2 4 5 2 1 = 0 := by rw [momA2_comm]; exact momA2_4_5_1_2
  have a22 : momA2 4 5 2 2 = 0 := momA2_4_5_2_2
  have a23 : momA2 4 5 2 3 = 0 := momA2_4_5_2_3
  have a30 : momA2 4 5 3 0 = 0 := by rw [momA2_comm]; exact momA2_4_5_0_3
  have a31 : momA2 4 5 3 1 = 0 := by rw [momA2_comm]; exact momA2_4_5_1_3
  have a32 : momA2 4 5 3 2 = 0 := by rw [momA2_comm]; exact momA2_4_5_2_3
  have a33 : momA2 4 5 3 3 = 0 := momA2_4_5_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_4_0_0, momB1_4_0_1, momB1_4_0_2, momB1_4_0_3, momB1_4_1_0, momB1_4_1_1, momB1_4_1_2, momB1_4_1_3, momB1_4_2_0, momB1_4_2_1, momB1_4_2_2, momB1_4_2_3, momB1_4_3_0, momB1_4_3_1, momB1_4_3_2, momB1_4_3_3, momB1_5_0_0, momB1_5_0_1, momB1_5_0_2, momB1_5_0_3, momB1_5_1_0, momB1_5_1_1, momB1_5_1_2, momB1_5_1_3, momB1_5_2_0, momB1_5_2_1, momB1_5_2_2, momB1_5_2_3, momB1_5_3_0, momB1_5_3_1, momB1_5_3_2, momB1_5_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_4_5 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 4 5 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 4 5 : ℂ)) := by
  rw [← Lval_eq_4_5]
  refine Kred_limit 4 5 k momA0_4_5 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_4_5_0
  · exact momA1_4_5_1
  · exact momA1_4_5_2
  · exact momA1_4_5_3

theorem Lval_eq_4_6 (k : Fin 4 → ℝ) : Lval 4 6 k = (KEH k 4 6 : ℂ) := by
  have a00 : momA2 4 6 0 0 = 0 := momA2_4_6_0_0
  have a01 : momA2 4 6 0 1 = 0 := momA2_4_6_0_1
  have a02 : momA2 4 6 0 2 = 0 := momA2_4_6_0_2
  have a03 : momA2 4 6 0 3 = 0 := momA2_4_6_0_3
  have a10 : momA2 4 6 1 0 = 0 := by rw [momA2_comm]; exact momA2_4_6_0_1
  have a11 : momA2 4 6 1 1 = 0 := momA2_4_6_1_1
  have a12 : momA2 4 6 1 2 = 0 := momA2_4_6_1_2
  have a13 : momA2 4 6 1 3 = 0 := momA2_4_6_1_3
  have a20 : momA2 4 6 2 0 = 0 := by rw [momA2_comm]; exact momA2_4_6_0_2
  have a21 : momA2 4 6 2 1 = 0 := by rw [momA2_comm]; exact momA2_4_6_1_2
  have a22 : momA2 4 6 2 2 = 0 := momA2_4_6_2_2
  have a23 : momA2 4 6 2 3 = 0 := momA2_4_6_2_3
  have a30 : momA2 4 6 3 0 = 0 := by rw [momA2_comm]; exact momA2_4_6_0_3
  have a31 : momA2 4 6 3 1 = 0 := by rw [momA2_comm]; exact momA2_4_6_1_3
  have a32 : momA2 4 6 3 2 = 0 := by rw [momA2_comm]; exact momA2_4_6_2_3
  have a33 : momA2 4 6 3 3 = 0 := momA2_4_6_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_4_0_0, momB1_4_0_1, momB1_4_0_2, momB1_4_0_3, momB1_4_1_0, momB1_4_1_1, momB1_4_1_2, momB1_4_1_3, momB1_4_2_0, momB1_4_2_1, momB1_4_2_2, momB1_4_2_3, momB1_4_3_0, momB1_4_3_1, momB1_4_3_2, momB1_4_3_3, momB1_6_0_0, momB1_6_0_1, momB1_6_0_2, momB1_6_0_3, momB1_6_1_0, momB1_6_1_1, momB1_6_1_2, momB1_6_1_3, momB1_6_2_0, momB1_6_2_1, momB1_6_2_2, momB1_6_2_3, momB1_6_3_0, momB1_6_3_1, momB1_6_3_2, momB1_6_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_4_6 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 4 6 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 4 6 : ℂ)) := by
  rw [← Lval_eq_4_6]
  refine Kred_limit 4 6 k momA0_4_6 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_4_6_0
  · exact momA1_4_6_1
  · exact momA1_4_6_2
  · exact momA1_4_6_3

theorem Lval_eq_4_7 (k : Fin 4 → ℝ) : Lval 4 7 k = (KEH k 4 7 : ℂ) := by
  have a00 : momA2 4 7 0 0 = -96 := momA2_4_7_0_0
  have a01 : momA2 4 7 0 1 = 0 := momA2_4_7_0_1
  have a02 : momA2 4 7 0 2 = 0 := momA2_4_7_0_2
  have a03 : momA2 4 7 0 3 = 0 := momA2_4_7_0_3
  have a10 : momA2 4 7 1 0 = 0 := by rw [momA2_comm]; exact momA2_4_7_0_1
  have a11 : momA2 4 7 1 1 = 0 := momA2_4_7_1_1
  have a12 : momA2 4 7 1 2 = 0 := momA2_4_7_1_2
  have a13 : momA2 4 7 1 3 = 0 := momA2_4_7_1_3
  have a20 : momA2 4 7 2 0 = 0 := by rw [momA2_comm]; exact momA2_4_7_0_2
  have a21 : momA2 4 7 2 1 = 0 := by rw [momA2_comm]; exact momA2_4_7_1_2
  have a22 : momA2 4 7 2 2 = 0 := momA2_4_7_2_2
  have a23 : momA2 4 7 2 3 = 0 := momA2_4_7_2_3
  have a30 : momA2 4 7 3 0 = 0 := by rw [momA2_comm]; exact momA2_4_7_0_3
  have a31 : momA2 4 7 3 1 = 0 := by rw [momA2_comm]; exact momA2_4_7_1_3
  have a32 : momA2 4 7 3 2 = 0 := by rw [momA2_comm]; exact momA2_4_7_2_3
  have a33 : momA2 4 7 3 3 = -96 := momA2_4_7_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_4_0_0, momB1_4_0_1, momB1_4_0_2, momB1_4_0_3, momB1_4_1_0, momB1_4_1_1, momB1_4_1_2, momB1_4_1_3, momB1_4_2_0, momB1_4_2_1, momB1_4_2_2, momB1_4_2_3, momB1_4_3_0, momB1_4_3_1, momB1_4_3_2, momB1_4_3_3, momB1_7_0_0, momB1_7_0_1, momB1_7_0_2, momB1_7_0_3, momB1_7_1_0, momB1_7_1_1, momB1_7_1_2, momB1_7_1_3, momB1_7_2_0, momB1_7_2_1, momB1_7_2_2, momB1_7_2_3, momB1_7_3_0, momB1_7_3_1, momB1_7_3_2, momB1_7_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_4_7 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 4 7 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 4 7 : ℂ)) := by
  rw [← Lval_eq_4_7]
  refine Kred_limit 4 7 k momA0_4_7 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_4_7_0
  · exact momA1_4_7_1
  · exact momA1_4_7_2
  · exact momA1_4_7_3

theorem Lval_eq_4_8 (k : Fin 4 → ℝ) : Lval 4 8 k = (KEH k 4 8 : ℂ) := by
  have a00 : momA2 4 8 0 0 = 0 := momA2_4_8_0_0
  have a01 : momA2 4 8 0 1 = 0 := momA2_4_8_0_1
  have a02 : momA2 4 8 0 2 = 0 := momA2_4_8_0_2
  have a03 : momA2 4 8 0 3 = 0 := momA2_4_8_0_3
  have a10 : momA2 4 8 1 0 = 0 := by rw [momA2_comm]; exact momA2_4_8_0_1
  have a11 : momA2 4 8 1 1 = 0 := momA2_4_8_1_1
  have a12 : momA2 4 8 1 2 = 0 := momA2_4_8_1_2
  have a13 : momA2 4 8 1 3 = 0 := momA2_4_8_1_3
  have a20 : momA2 4 8 2 0 = 0 := by rw [momA2_comm]; exact momA2_4_8_0_2
  have a21 : momA2 4 8 2 1 = 0 := by rw [momA2_comm]; exact momA2_4_8_1_2
  have a22 : momA2 4 8 2 2 = 0 := momA2_4_8_2_2
  have a23 : momA2 4 8 2 3 = 96 := momA2_4_8_2_3
  have a30 : momA2 4 8 3 0 = 0 := by rw [momA2_comm]; exact momA2_4_8_0_3
  have a31 : momA2 4 8 3 1 = 0 := by rw [momA2_comm]; exact momA2_4_8_1_3
  have a32 : momA2 4 8 3 2 = 96 := by rw [momA2_comm]; exact momA2_4_8_2_3
  have a33 : momA2 4 8 3 3 = 0 := momA2_4_8_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_4_0_0, momB1_4_0_1, momB1_4_0_2, momB1_4_0_3, momB1_4_1_0, momB1_4_1_1, momB1_4_1_2, momB1_4_1_3, momB1_4_2_0, momB1_4_2_1, momB1_4_2_2, momB1_4_2_3, momB1_4_3_0, momB1_4_3_1, momB1_4_3_2, momB1_4_3_3, momB1_8_0_0, momB1_8_0_1, momB1_8_0_2, momB1_8_0_3, momB1_8_1_0, momB1_8_1_1, momB1_8_1_2, momB1_8_1_3, momB1_8_2_0, momB1_8_2_1, momB1_8_2_2, momB1_8_2_3, momB1_8_3_0, momB1_8_3_1, momB1_8_3_2, momB1_8_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_4_8 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 4 8 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 4 8 : ℂ)) := by
  rw [← Lval_eq_4_8]
  refine Kred_limit 4 8 k momA0_4_8 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_4_8_0
  · exact momA1_4_8_1
  · exact momA1_4_8_2
  · exact momA1_4_8_3

theorem Lval_eq_4_9 (k : Fin 4 → ℝ) : Lval 4 9 k = (KEH k 4 9 : ℂ) := by
  have a00 : momA2 4 9 0 0 = -96 := momA2_4_9_0_0
  have a01 : momA2 4 9 0 1 = 0 := momA2_4_9_0_1
  have a02 : momA2 4 9 0 2 = 0 := momA2_4_9_0_2
  have a03 : momA2 4 9 0 3 = 0 := momA2_4_9_0_3
  have a10 : momA2 4 9 1 0 = 0 := by rw [momA2_comm]; exact momA2_4_9_0_1
  have a11 : momA2 4 9 1 1 = 0 := momA2_4_9_1_1
  have a12 : momA2 4 9 1 2 = 0 := momA2_4_9_1_2
  have a13 : momA2 4 9 1 3 = 0 := momA2_4_9_1_3
  have a20 : momA2 4 9 2 0 = 0 := by rw [momA2_comm]; exact momA2_4_9_0_2
  have a21 : momA2 4 9 2 1 = 0 := by rw [momA2_comm]; exact momA2_4_9_1_2
  have a22 : momA2 4 9 2 2 = -96 := momA2_4_9_2_2
  have a23 : momA2 4 9 2 3 = 0 := momA2_4_9_2_3
  have a30 : momA2 4 9 3 0 = 0 := by rw [momA2_comm]; exact momA2_4_9_0_3
  have a31 : momA2 4 9 3 1 = 0 := by rw [momA2_comm]; exact momA2_4_9_1_3
  have a32 : momA2 4 9 3 2 = 0 := by rw [momA2_comm]; exact momA2_4_9_2_3
  have a33 : momA2 4 9 3 3 = 0 := momA2_4_9_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_4_0_0, momB1_4_0_1, momB1_4_0_2, momB1_4_0_3, momB1_4_1_0, momB1_4_1_1, momB1_4_1_2, momB1_4_1_3, momB1_4_2_0, momB1_4_2_1, momB1_4_2_2, momB1_4_2_3, momB1_4_3_0, momB1_4_3_1, momB1_4_3_2, momB1_4_3_3, momB1_9_0_0, momB1_9_0_1, momB1_9_0_2, momB1_9_0_3, momB1_9_1_0, momB1_9_1_1, momB1_9_1_2, momB1_9_1_3, momB1_9_2_0, momB1_9_2_1, momB1_9_2_2, momB1_9_2_3, momB1_9_3_0, momB1_9_3_1, momB1_9_3_2, momB1_9_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_4_9 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 4 9 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 4 9 : ℂ)) := by
  rw [← Lval_eq_4_9]
  refine Kred_limit 4 9 k momA0_4_9 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_4_9_0
  · exact momA1_4_9_1
  · exact momA1_4_9_2
  · exact momA1_4_9_3

theorem Lval_eq_5_5 (k : Fin 4 → ℝ) : Lval 5 5 k = (KEH k 5 5 : ℂ) := by
  have a00 : momA2 5 5 0 0 = 192 := momA2_5_5_0_0
  have a01 : momA2 5 5 0 1 = 0 := momA2_5_5_0_1
  have a02 : momA2 5 5 0 2 = 0 := momA2_5_5_0_2
  have a03 : momA2 5 5 0 3 = 0 := momA2_5_5_0_3
  have a10 : momA2 5 5 1 0 = 0 := by rw [momA2_comm]; exact momA2_5_5_0_1
  have a11 : momA2 5 5 1 1 = 0 := momA2_5_5_1_1
  have a12 : momA2 5 5 1 2 = 0 := momA2_5_5_1_2
  have a13 : momA2 5 5 1 3 = 0 := momA2_5_5_1_3
  have a20 : momA2 5 5 2 0 = 0 := by rw [momA2_comm]; exact momA2_5_5_0_2
  have a21 : momA2 5 5 2 1 = 0 := by rw [momA2_comm]; exact momA2_5_5_1_2
  have a22 : momA2 5 5 2 2 = 0 := momA2_5_5_2_2
  have a23 : momA2 5 5 2 3 = 0 := momA2_5_5_2_3
  have a30 : momA2 5 5 3 0 = 0 := by rw [momA2_comm]; exact momA2_5_5_0_3
  have a31 : momA2 5 5 3 1 = 0 := by rw [momA2_comm]; exact momA2_5_5_1_3
  have a32 : momA2 5 5 3 2 = 0 := by rw [momA2_comm]; exact momA2_5_5_2_3
  have a33 : momA2 5 5 3 3 = 192 := momA2_5_5_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_5_0_0, momB1_5_0_1, momB1_5_0_2, momB1_5_0_3, momB1_5_1_0, momB1_5_1_1, momB1_5_1_2, momB1_5_1_3, momB1_5_2_0, momB1_5_2_1, momB1_5_2_2, momB1_5_2_3, momB1_5_3_0, momB1_5_3_1, momB1_5_3_2, momB1_5_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_5_5 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 5 5 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 5 5 : ℂ)) := by
  rw [← Lval_eq_5_5]
  refine Kred_limit 5 5 k momA0_5_5 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_5_5_0
  · exact momA1_5_5_1
  · exact momA1_5_5_2
  · exact momA1_5_5_3

theorem Lval_eq_5_6 (k : Fin 4 → ℝ) : Lval 5 6 k = (KEH k 5 6 : ℂ) := by
  have a00 : momA2 5 6 0 0 = 0 := momA2_5_6_0_0
  have a01 : momA2 5 6 0 1 = 0 := momA2_5_6_0_1
  have a02 : momA2 5 6 0 2 = 0 := momA2_5_6_0_2
  have a03 : momA2 5 6 0 3 = 0 := momA2_5_6_0_3
  have a10 : momA2 5 6 1 0 = 0 := by rw [momA2_comm]; exact momA2_5_6_0_1
  have a11 : momA2 5 6 1 1 = 0 := momA2_5_6_1_1
  have a12 : momA2 5 6 1 2 = 0 := momA2_5_6_1_2
  have a13 : momA2 5 6 1 3 = 0 := momA2_5_6_1_3
  have a20 : momA2 5 6 2 0 = 0 := by rw [momA2_comm]; exact momA2_5_6_0_2
  have a21 : momA2 5 6 2 1 = 0 := by rw [momA2_comm]; exact momA2_5_6_1_2
  have a22 : momA2 5 6 2 2 = 0 := momA2_5_6_2_2
  have a23 : momA2 5 6 2 3 = -96 := momA2_5_6_2_3
  have a30 : momA2 5 6 3 0 = 0 := by rw [momA2_comm]; exact momA2_5_6_0_3
  have a31 : momA2 5 6 3 1 = 0 := by rw [momA2_comm]; exact momA2_5_6_1_3
  have a32 : momA2 5 6 3 2 = -96 := by rw [momA2_comm]; exact momA2_5_6_2_3
  have a33 : momA2 5 6 3 3 = 0 := momA2_5_6_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_5_0_0, momB1_5_0_1, momB1_5_0_2, momB1_5_0_3, momB1_5_1_0, momB1_5_1_1, momB1_5_1_2, momB1_5_1_3, momB1_5_2_0, momB1_5_2_1, momB1_5_2_2, momB1_5_2_3, momB1_5_3_0, momB1_5_3_1, momB1_5_3_2, momB1_5_3_3, momB1_6_0_0, momB1_6_0_1, momB1_6_0_2, momB1_6_0_3, momB1_6_1_0, momB1_6_1_1, momB1_6_1_2, momB1_6_1_3, momB1_6_2_0, momB1_6_2_1, momB1_6_2_2, momB1_6_2_3, momB1_6_3_0, momB1_6_3_1, momB1_6_3_2, momB1_6_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_5_6 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 5 6 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 5 6 : ℂ)) := by
  rw [← Lval_eq_5_6]
  refine Kred_limit 5 6 k momA0_5_6 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_5_6_0
  · exact momA1_5_6_1
  · exact momA1_5_6_2
  · exact momA1_5_6_3

theorem Lval_eq_5_7 (k : Fin 4 → ℝ) : Lval 5 7 k = (KEH k 5 7 : ℂ) := by
  have a00 : momA2 5 7 0 0 = 0 := momA2_5_7_0_0
  have a01 : momA2 5 7 0 1 = 0 := momA2_5_7_0_1
  have a02 : momA2 5 7 0 2 = 0 := momA2_5_7_0_2
  have a03 : momA2 5 7 0 3 = 0 := momA2_5_7_0_3
  have a10 : momA2 5 7 1 0 = 0 := by rw [momA2_comm]; exact momA2_5_7_0_1
  have a11 : momA2 5 7 1 1 = 0 := momA2_5_7_1_1
  have a12 : momA2 5 7 1 2 = 0 := momA2_5_7_1_2
  have a13 : momA2 5 7 1 3 = 0 := momA2_5_7_1_3
  have a20 : momA2 5 7 2 0 = 0 := by rw [momA2_comm]; exact momA2_5_7_0_2
  have a21 : momA2 5 7 2 1 = 0 := by rw [momA2_comm]; exact momA2_5_7_1_2
  have a22 : momA2 5 7 2 2 = 0 := momA2_5_7_2_2
  have a23 : momA2 5 7 2 3 = 0 := momA2_5_7_2_3
  have a30 : momA2 5 7 3 0 = 0 := by rw [momA2_comm]; exact momA2_5_7_0_3
  have a31 : momA2 5 7 3 1 = 0 := by rw [momA2_comm]; exact momA2_5_7_1_3
  have a32 : momA2 5 7 3 2 = 0 := by rw [momA2_comm]; exact momA2_5_7_2_3
  have a33 : momA2 5 7 3 3 = 0 := momA2_5_7_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_5_0_0, momB1_5_0_1, momB1_5_0_2, momB1_5_0_3, momB1_5_1_0, momB1_5_1_1, momB1_5_1_2, momB1_5_1_3, momB1_5_2_0, momB1_5_2_1, momB1_5_2_2, momB1_5_2_3, momB1_5_3_0, momB1_5_3_1, momB1_5_3_2, momB1_5_3_3, momB1_7_0_0, momB1_7_0_1, momB1_7_0_2, momB1_7_0_3, momB1_7_1_0, momB1_7_1_1, momB1_7_1_2, momB1_7_1_3, momB1_7_2_0, momB1_7_2_1, momB1_7_2_2, momB1_7_2_3, momB1_7_3_0, momB1_7_3_1, momB1_7_3_2, momB1_7_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_5_7 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 5 7 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 5 7 : ℂ)) := by
  rw [← Lval_eq_5_7]
  refine Kred_limit 5 7 k momA0_5_7 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_5_7_0
  · exact momA1_5_7_1
  · exact momA1_5_7_2
  · exact momA1_5_7_3

theorem Lval_eq_5_8 (k : Fin 4 → ℝ) : Lval 5 8 k = (KEH k 5 8 : ℂ) := by
  have a00 : momA2 5 8 0 0 = 0 := momA2_5_8_0_0
  have a01 : momA2 5 8 0 1 = 0 := momA2_5_8_0_1
  have a02 : momA2 5 8 0 2 = 0 := momA2_5_8_0_2
  have a03 : momA2 5 8 0 3 = 0 := momA2_5_8_0_3
  have a10 : momA2 5 8 1 0 = 0 := by rw [momA2_comm]; exact momA2_5_8_0_1
  have a11 : momA2 5 8 1 1 = 0 := momA2_5_8_1_1
  have a12 : momA2 5 8 1 2 = 0 := momA2_5_8_1_2
  have a13 : momA2 5 8 1 3 = -96 := momA2_5_8_1_3
  have a20 : momA2 5 8 2 0 = 0 := by rw [momA2_comm]; exact momA2_5_8_0_2
  have a21 : momA2 5 8 2 1 = 0 := by rw [momA2_comm]; exact momA2_5_8_1_2
  have a22 : momA2 5 8 2 2 = 0 := momA2_5_8_2_2
  have a23 : momA2 5 8 2 3 = 0 := momA2_5_8_2_3
  have a30 : momA2 5 8 3 0 = 0 := by rw [momA2_comm]; exact momA2_5_8_0_3
  have a31 : momA2 5 8 3 1 = -96 := by rw [momA2_comm]; exact momA2_5_8_1_3
  have a32 : momA2 5 8 3 2 = 0 := by rw [momA2_comm]; exact momA2_5_8_2_3
  have a33 : momA2 5 8 3 3 = 0 := momA2_5_8_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_5_0_0, momB1_5_0_1, momB1_5_0_2, momB1_5_0_3, momB1_5_1_0, momB1_5_1_1, momB1_5_1_2, momB1_5_1_3, momB1_5_2_0, momB1_5_2_1, momB1_5_2_2, momB1_5_2_3, momB1_5_3_0, momB1_5_3_1, momB1_5_3_2, momB1_5_3_3, momB1_8_0_0, momB1_8_0_1, momB1_8_0_2, momB1_8_0_3, momB1_8_1_0, momB1_8_1_1, momB1_8_1_2, momB1_8_1_3, momB1_8_2_0, momB1_8_2_1, momB1_8_2_2, momB1_8_2_3, momB1_8_3_0, momB1_8_3_1, momB1_8_3_2, momB1_8_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_5_8 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 5 8 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 5 8 : ℂ)) := by
  rw [← Lval_eq_5_8]
  refine Kred_limit 5 8 k momA0_5_8 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_5_8_0
  · exact momA1_5_8_1
  · exact momA1_5_8_2
  · exact momA1_5_8_3

theorem Lval_eq_5_9 (k : Fin 4 → ℝ) : Lval 5 9 k = (KEH k 5 9 : ℂ) := by
  have a00 : momA2 5 9 0 0 = 0 := momA2_5_9_0_0
  have a01 : momA2 5 9 0 1 = 0 := momA2_5_9_0_1
  have a02 : momA2 5 9 0 2 = 0 := momA2_5_9_0_2
  have a03 : momA2 5 9 0 3 = 0 := momA2_5_9_0_3
  have a10 : momA2 5 9 1 0 = 0 := by rw [momA2_comm]; exact momA2_5_9_0_1
  have a11 : momA2 5 9 1 1 = 0 := momA2_5_9_1_1
  have a12 : momA2 5 9 1 2 = 96 := momA2_5_9_1_2
  have a13 : momA2 5 9 1 3 = 0 := momA2_5_9_1_3
  have a20 : momA2 5 9 2 0 = 0 := by rw [momA2_comm]; exact momA2_5_9_0_2
  have a21 : momA2 5 9 2 1 = 96 := by rw [momA2_comm]; exact momA2_5_9_1_2
  have a22 : momA2 5 9 2 2 = 0 := momA2_5_9_2_2
  have a23 : momA2 5 9 2 3 = 0 := momA2_5_9_2_3
  have a30 : momA2 5 9 3 0 = 0 := by rw [momA2_comm]; exact momA2_5_9_0_3
  have a31 : momA2 5 9 3 1 = 0 := by rw [momA2_comm]; exact momA2_5_9_1_3
  have a32 : momA2 5 9 3 2 = 0 := by rw [momA2_comm]; exact momA2_5_9_2_3
  have a33 : momA2 5 9 3 3 = 0 := momA2_5_9_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_5_0_0, momB1_5_0_1, momB1_5_0_2, momB1_5_0_3, momB1_5_1_0, momB1_5_1_1, momB1_5_1_2, momB1_5_1_3, momB1_5_2_0, momB1_5_2_1, momB1_5_2_2, momB1_5_2_3, momB1_5_3_0, momB1_5_3_1, momB1_5_3_2, momB1_5_3_3, momB1_9_0_0, momB1_9_0_1, momB1_9_0_2, momB1_9_0_3, momB1_9_1_0, momB1_9_1_1, momB1_9_1_2, momB1_9_1_3, momB1_9_2_0, momB1_9_2_1, momB1_9_2_2, momB1_9_2_3, momB1_9_3_0, momB1_9_3_1, momB1_9_3_2, momB1_9_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_5_9 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 5 9 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 5 9 : ℂ)) := by
  rw [← Lval_eq_5_9]
  refine Kred_limit 5 9 k momA0_5_9 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_5_9_0
  · exact momA1_5_9_1
  · exact momA1_5_9_2
  · exact momA1_5_9_3

theorem Lval_eq_6_6 (k : Fin 4 → ℝ) : Lval 6 6 k = (KEH k 6 6 : ℂ) := by
  have a00 : momA2 6 6 0 0 = 192 := momA2_6_6_0_0
  have a01 : momA2 6 6 0 1 = 0 := momA2_6_6_0_1
  have a02 : momA2 6 6 0 2 = 0 := momA2_6_6_0_2
  have a03 : momA2 6 6 0 3 = 0 := momA2_6_6_0_3
  have a10 : momA2 6 6 1 0 = 0 := by rw [momA2_comm]; exact momA2_6_6_0_1
  have a11 : momA2 6 6 1 1 = 0 := momA2_6_6_1_1
  have a12 : momA2 6 6 1 2 = 0 := momA2_6_6_1_2
  have a13 : momA2 6 6 1 3 = 0 := momA2_6_6_1_3
  have a20 : momA2 6 6 2 0 = 0 := by rw [momA2_comm]; exact momA2_6_6_0_2
  have a21 : momA2 6 6 2 1 = 0 := by rw [momA2_comm]; exact momA2_6_6_1_2
  have a22 : momA2 6 6 2 2 = 192 := momA2_6_6_2_2
  have a23 : momA2 6 6 2 3 = 0 := momA2_6_6_2_3
  have a30 : momA2 6 6 3 0 = 0 := by rw [momA2_comm]; exact momA2_6_6_0_3
  have a31 : momA2 6 6 3 1 = 0 := by rw [momA2_comm]; exact momA2_6_6_1_3
  have a32 : momA2 6 6 3 2 = 0 := by rw [momA2_comm]; exact momA2_6_6_2_3
  have a33 : momA2 6 6 3 3 = 0 := momA2_6_6_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_6_0_0, momB1_6_0_1, momB1_6_0_2, momB1_6_0_3, momB1_6_1_0, momB1_6_1_1, momB1_6_1_2, momB1_6_1_3, momB1_6_2_0, momB1_6_2_1, momB1_6_2_2, momB1_6_2_3, momB1_6_3_0, momB1_6_3_1, momB1_6_3_2, momB1_6_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_6_6 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 6 6 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 6 6 : ℂ)) := by
  rw [← Lval_eq_6_6]
  refine Kred_limit 6 6 k momA0_6_6 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_6_6_0
  · exact momA1_6_6_1
  · exact momA1_6_6_2
  · exact momA1_6_6_3

theorem Lval_eq_6_7 (k : Fin 4 → ℝ) : Lval 6 7 k = (KEH k 6 7 : ℂ) := by
  have a00 : momA2 6 7 0 0 = 0 := momA2_6_7_0_0
  have a01 : momA2 6 7 0 1 = 0 := momA2_6_7_0_1
  have a02 : momA2 6 7 0 2 = 0 := momA2_6_7_0_2
  have a03 : momA2 6 7 0 3 = 0 := momA2_6_7_0_3
  have a10 : momA2 6 7 1 0 = 0 := by rw [momA2_comm]; exact momA2_6_7_0_1
  have a11 : momA2 6 7 1 1 = 0 := momA2_6_7_1_1
  have a12 : momA2 6 7 1 2 = 0 := momA2_6_7_1_2
  have a13 : momA2 6 7 1 3 = 96 := momA2_6_7_1_3
  have a20 : momA2 6 7 2 0 = 0 := by rw [momA2_comm]; exact momA2_6_7_0_2
  have a21 : momA2 6 7 2 1 = 0 := by rw [momA2_comm]; exact momA2_6_7_1_2
  have a22 : momA2 6 7 2 2 = 0 := momA2_6_7_2_2
  have a23 : momA2 6 7 2 3 = 0 := momA2_6_7_2_3
  have a30 : momA2 6 7 3 0 = 0 := by rw [momA2_comm]; exact momA2_6_7_0_3
  have a31 : momA2 6 7 3 1 = 96 := by rw [momA2_comm]; exact momA2_6_7_1_3
  have a32 : momA2 6 7 3 2 = 0 := by rw [momA2_comm]; exact momA2_6_7_2_3
  have a33 : momA2 6 7 3 3 = 0 := momA2_6_7_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_6_0_0, momB1_6_0_1, momB1_6_0_2, momB1_6_0_3, momB1_6_1_0, momB1_6_1_1, momB1_6_1_2, momB1_6_1_3, momB1_6_2_0, momB1_6_2_1, momB1_6_2_2, momB1_6_2_3, momB1_6_3_0, momB1_6_3_1, momB1_6_3_2, momB1_6_3_3, momB1_7_0_0, momB1_7_0_1, momB1_7_0_2, momB1_7_0_3, momB1_7_1_0, momB1_7_1_1, momB1_7_1_2, momB1_7_1_3, momB1_7_2_0, momB1_7_2_1, momB1_7_2_2, momB1_7_2_3, momB1_7_3_0, momB1_7_3_1, momB1_7_3_2, momB1_7_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_6_7 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 6 7 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 6 7 : ℂ)) := by
  rw [← Lval_eq_6_7]
  refine Kred_limit 6 7 k momA0_6_7 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_6_7_0
  · exact momA1_6_7_1
  · exact momA1_6_7_2
  · exact momA1_6_7_3

theorem Lval_eq_6_8 (k : Fin 4 → ℝ) : Lval 6 8 k = (KEH k 6 8 : ℂ) := by
  have a00 : momA2 6 8 0 0 = 0 := momA2_6_8_0_0
  have a01 : momA2 6 8 0 1 = 0 := momA2_6_8_0_1
  have a02 : momA2 6 8 0 2 = 0 := momA2_6_8_0_2
  have a03 : momA2 6 8 0 3 = 0 := momA2_6_8_0_3
  have a10 : momA2 6 8 1 0 = 0 := by rw [momA2_comm]; exact momA2_6_8_0_1
  have a11 : momA2 6 8 1 1 = 0 := momA2_6_8_1_1
  have a12 : momA2 6 8 1 2 = -96 := momA2_6_8_1_2
  have a13 : momA2 6 8 1 3 = 0 := momA2_6_8_1_3
  have a20 : momA2 6 8 2 0 = 0 := by rw [momA2_comm]; exact momA2_6_8_0_2
  have a21 : momA2 6 8 2 1 = -96 := by rw [momA2_comm]; exact momA2_6_8_1_2
  have a22 : momA2 6 8 2 2 = 0 := momA2_6_8_2_2
  have a23 : momA2 6 8 2 3 = 0 := momA2_6_8_2_3
  have a30 : momA2 6 8 3 0 = 0 := by rw [momA2_comm]; exact momA2_6_8_0_3
  have a31 : momA2 6 8 3 1 = 0 := by rw [momA2_comm]; exact momA2_6_8_1_3
  have a32 : momA2 6 8 3 2 = 0 := by rw [momA2_comm]; exact momA2_6_8_2_3
  have a33 : momA2 6 8 3 3 = 0 := momA2_6_8_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_6_0_0, momB1_6_0_1, momB1_6_0_2, momB1_6_0_3, momB1_6_1_0, momB1_6_1_1, momB1_6_1_2, momB1_6_1_3, momB1_6_2_0, momB1_6_2_1, momB1_6_2_2, momB1_6_2_3, momB1_6_3_0, momB1_6_3_1, momB1_6_3_2, momB1_6_3_3, momB1_8_0_0, momB1_8_0_1, momB1_8_0_2, momB1_8_0_3, momB1_8_1_0, momB1_8_1_1, momB1_8_1_2, momB1_8_1_3, momB1_8_2_0, momB1_8_2_1, momB1_8_2_2, momB1_8_2_3, momB1_8_3_0, momB1_8_3_1, momB1_8_3_2, momB1_8_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_6_8 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 6 8 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 6 8 : ℂ)) := by
  rw [← Lval_eq_6_8]
  refine Kred_limit 6 8 k momA0_6_8 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_6_8_0
  · exact momA1_6_8_1
  · exact momA1_6_8_2
  · exact momA1_6_8_3

theorem Lval_eq_6_9 (k : Fin 4 → ℝ) : Lval 6 9 k = (KEH k 6 9 : ℂ) := by
  have a00 : momA2 6 9 0 0 = 0 := momA2_6_9_0_0
  have a01 : momA2 6 9 0 1 = 0 := momA2_6_9_0_1
  have a02 : momA2 6 9 0 2 = 0 := momA2_6_9_0_2
  have a03 : momA2 6 9 0 3 = 0 := momA2_6_9_0_3
  have a10 : momA2 6 9 1 0 = 0 := by rw [momA2_comm]; exact momA2_6_9_0_1
  have a11 : momA2 6 9 1 1 = 0 := momA2_6_9_1_1
  have a12 : momA2 6 9 1 2 = 0 := momA2_6_9_1_2
  have a13 : momA2 6 9 1 3 = 0 := momA2_6_9_1_3
  have a20 : momA2 6 9 2 0 = 0 := by rw [momA2_comm]; exact momA2_6_9_0_2
  have a21 : momA2 6 9 2 1 = 0 := by rw [momA2_comm]; exact momA2_6_9_1_2
  have a22 : momA2 6 9 2 2 = 0 := momA2_6_9_2_2
  have a23 : momA2 6 9 2 3 = 0 := momA2_6_9_2_3
  have a30 : momA2 6 9 3 0 = 0 := by rw [momA2_comm]; exact momA2_6_9_0_3
  have a31 : momA2 6 9 3 1 = 0 := by rw [momA2_comm]; exact momA2_6_9_1_3
  have a32 : momA2 6 9 3 2 = 0 := by rw [momA2_comm]; exact momA2_6_9_2_3
  have a33 : momA2 6 9 3 3 = 0 := momA2_6_9_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_6_0_0, momB1_6_0_1, momB1_6_0_2, momB1_6_0_3, momB1_6_1_0, momB1_6_1_1, momB1_6_1_2, momB1_6_1_3, momB1_6_2_0, momB1_6_2_1, momB1_6_2_2, momB1_6_2_3, momB1_6_3_0, momB1_6_3_1, momB1_6_3_2, momB1_6_3_3, momB1_9_0_0, momB1_9_0_1, momB1_9_0_2, momB1_9_0_3, momB1_9_1_0, momB1_9_1_1, momB1_9_1_2, momB1_9_1_3, momB1_9_2_0, momB1_9_2_1, momB1_9_2_2, momB1_9_2_3, momB1_9_3_0, momB1_9_3_1, momB1_9_3_2, momB1_9_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_6_9 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 6 9 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 6 9 : ℂ)) := by
  rw [← Lval_eq_6_9]
  refine Kred_limit 6 9 k momA0_6_9 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_6_9_0
  · exact momA1_6_9_1
  · exact momA1_6_9_2
  · exact momA1_6_9_3

theorem Lval_eq_7_7 (k : Fin 4 → ℝ) : Lval 7 7 k = (KEH k 7 7 : ℂ) := by
  have a00 : momA2 7 7 0 0 = 0 := momA2_7_7_0_0
  have a01 : momA2 7 7 0 1 = 0 := momA2_7_7_0_1
  have a02 : momA2 7 7 0 2 = 0 := momA2_7_7_0_2
  have a03 : momA2 7 7 0 3 = 0 := momA2_7_7_0_3
  have a10 : momA2 7 7 1 0 = 0 := by rw [momA2_comm]; exact momA2_7_7_0_1
  have a11 : momA2 7 7 1 1 = 0 := momA2_7_7_1_1
  have a12 : momA2 7 7 1 2 = 0 := momA2_7_7_1_2
  have a13 : momA2 7 7 1 3 = 0 := momA2_7_7_1_3
  have a20 : momA2 7 7 2 0 = 0 := by rw [momA2_comm]; exact momA2_7_7_0_2
  have a21 : momA2 7 7 2 1 = 0 := by rw [momA2_comm]; exact momA2_7_7_1_2
  have a22 : momA2 7 7 2 2 = 0 := momA2_7_7_2_2
  have a23 : momA2 7 7 2 3 = 0 := momA2_7_7_2_3
  have a30 : momA2 7 7 3 0 = 0 := by rw [momA2_comm]; exact momA2_7_7_0_3
  have a31 : momA2 7 7 3 1 = 0 := by rw [momA2_comm]; exact momA2_7_7_1_3
  have a32 : momA2 7 7 3 2 = 0 := by rw [momA2_comm]; exact momA2_7_7_2_3
  have a33 : momA2 7 7 3 3 = 0 := momA2_7_7_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_7_0_0, momB1_7_0_1, momB1_7_0_2, momB1_7_0_3, momB1_7_1_0, momB1_7_1_1, momB1_7_1_2, momB1_7_1_3, momB1_7_2_0, momB1_7_2_1, momB1_7_2_2, momB1_7_2_3, momB1_7_3_0, momB1_7_3_1, momB1_7_3_2, momB1_7_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_7_7 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 7 7 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 7 7 : ℂ)) := by
  rw [← Lval_eq_7_7]
  refine Kred_limit 7 7 k momA0_7_7 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_7_7_0
  · exact momA1_7_7_1
  · exact momA1_7_7_2
  · exact momA1_7_7_3

theorem Lval_eq_7_8 (k : Fin 4 → ℝ) : Lval 7 8 k = (KEH k 7 8 : ℂ) := by
  have a00 : momA2 7 8 0 0 = 0 := momA2_7_8_0_0
  have a01 : momA2 7 8 0 1 = 0 := momA2_7_8_0_1
  have a02 : momA2 7 8 0 2 = 0 := momA2_7_8_0_2
  have a03 : momA2 7 8 0 3 = 0 := momA2_7_8_0_3
  have a10 : momA2 7 8 1 0 = 0 := by rw [momA2_comm]; exact momA2_7_8_0_1
  have a11 : momA2 7 8 1 1 = 0 := momA2_7_8_1_1
  have a12 : momA2 7 8 1 2 = 0 := momA2_7_8_1_2
  have a13 : momA2 7 8 1 3 = 0 := momA2_7_8_1_3
  have a20 : momA2 7 8 2 0 = 0 := by rw [momA2_comm]; exact momA2_7_8_0_2
  have a21 : momA2 7 8 2 1 = 0 := by rw [momA2_comm]; exact momA2_7_8_1_2
  have a22 : momA2 7 8 2 2 = 0 := momA2_7_8_2_2
  have a23 : momA2 7 8 2 3 = 0 := momA2_7_8_2_3
  have a30 : momA2 7 8 3 0 = 0 := by rw [momA2_comm]; exact momA2_7_8_0_3
  have a31 : momA2 7 8 3 1 = 0 := by rw [momA2_comm]; exact momA2_7_8_1_3
  have a32 : momA2 7 8 3 2 = 0 := by rw [momA2_comm]; exact momA2_7_8_2_3
  have a33 : momA2 7 8 3 3 = 0 := momA2_7_8_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_7_0_0, momB1_7_0_1, momB1_7_0_2, momB1_7_0_3, momB1_7_1_0, momB1_7_1_1, momB1_7_1_2, momB1_7_1_3, momB1_7_2_0, momB1_7_2_1, momB1_7_2_2, momB1_7_2_3, momB1_7_3_0, momB1_7_3_1, momB1_7_3_2, momB1_7_3_3, momB1_8_0_0, momB1_8_0_1, momB1_8_0_2, momB1_8_0_3, momB1_8_1_0, momB1_8_1_1, momB1_8_1_2, momB1_8_1_3, momB1_8_2_0, momB1_8_2_1, momB1_8_2_2, momB1_8_2_3, momB1_8_3_0, momB1_8_3_1, momB1_8_3_2, momB1_8_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_7_8 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 7 8 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 7 8 : ℂ)) := by
  rw [← Lval_eq_7_8]
  refine Kred_limit 7 8 k momA0_7_8 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_7_8_0
  · exact momA1_7_8_1
  · exact momA1_7_8_2
  · exact momA1_7_8_3

theorem Lval_eq_7_9 (k : Fin 4 → ℝ) : Lval 7 9 k = (KEH k 7 9 : ℂ) := by
  have a00 : momA2 7 9 0 0 = -96 := momA2_7_9_0_0
  have a01 : momA2 7 9 0 1 = 0 := momA2_7_9_0_1
  have a02 : momA2 7 9 0 2 = 0 := momA2_7_9_0_2
  have a03 : momA2 7 9 0 3 = 0 := momA2_7_9_0_3
  have a10 : momA2 7 9 1 0 = 0 := by rw [momA2_comm]; exact momA2_7_9_0_1
  have a11 : momA2 7 9 1 1 = -96 := momA2_7_9_1_1
  have a12 : momA2 7 9 1 2 = 0 := momA2_7_9_1_2
  have a13 : momA2 7 9 1 3 = 0 := momA2_7_9_1_3
  have a20 : momA2 7 9 2 0 = 0 := by rw [momA2_comm]; exact momA2_7_9_0_2
  have a21 : momA2 7 9 2 1 = 0 := by rw [momA2_comm]; exact momA2_7_9_1_2
  have a22 : momA2 7 9 2 2 = 0 := momA2_7_9_2_2
  have a23 : momA2 7 9 2 3 = 0 := momA2_7_9_2_3
  have a30 : momA2 7 9 3 0 = 0 := by rw [momA2_comm]; exact momA2_7_9_0_3
  have a31 : momA2 7 9 3 1 = 0 := by rw [momA2_comm]; exact momA2_7_9_1_3
  have a32 : momA2 7 9 3 2 = 0 := by rw [momA2_comm]; exact momA2_7_9_2_3
  have a33 : momA2 7 9 3 3 = 0 := momA2_7_9_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_7_0_0, momB1_7_0_1, momB1_7_0_2, momB1_7_0_3, momB1_7_1_0, momB1_7_1_1, momB1_7_1_2, momB1_7_1_3, momB1_7_2_0, momB1_7_2_1, momB1_7_2_2, momB1_7_2_3, momB1_7_3_0, momB1_7_3_1, momB1_7_3_2, momB1_7_3_3, momB1_9_0_0, momB1_9_0_1, momB1_9_0_2, momB1_9_0_3, momB1_9_1_0, momB1_9_1_1, momB1_9_1_2, momB1_9_1_3, momB1_9_2_0, momB1_9_2_1, momB1_9_2_2, momB1_9_2_3, momB1_9_3_0, momB1_9_3_1, momB1_9_3_2, momB1_9_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_7_9 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 7 9 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 7 9 : ℂ)) := by
  rw [← Lval_eq_7_9]
  refine Kred_limit 7 9 k momA0_7_9 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_7_9_0
  · exact momA1_7_9_1
  · exact momA1_7_9_2
  · exact momA1_7_9_3

theorem Lval_eq_8_8 (k : Fin 4 → ℝ) : Lval 8 8 k = (KEH k 8 8 : ℂ) := by
  have a00 : momA2 8 8 0 0 = 192 := momA2_8_8_0_0
  have a01 : momA2 8 8 0 1 = 0 := momA2_8_8_0_1
  have a02 : momA2 8 8 0 2 = 0 := momA2_8_8_0_2
  have a03 : momA2 8 8 0 3 = 0 := momA2_8_8_0_3
  have a10 : momA2 8 8 1 0 = 0 := by rw [momA2_comm]; exact momA2_8_8_0_1
  have a11 : momA2 8 8 1 1 = 192 := momA2_8_8_1_1
  have a12 : momA2 8 8 1 2 = 0 := momA2_8_8_1_2
  have a13 : momA2 8 8 1 3 = 0 := momA2_8_8_1_3
  have a20 : momA2 8 8 2 0 = 0 := by rw [momA2_comm]; exact momA2_8_8_0_2
  have a21 : momA2 8 8 2 1 = 0 := by rw [momA2_comm]; exact momA2_8_8_1_2
  have a22 : momA2 8 8 2 2 = 0 := momA2_8_8_2_2
  have a23 : momA2 8 8 2 3 = 0 := momA2_8_8_2_3
  have a30 : momA2 8 8 3 0 = 0 := by rw [momA2_comm]; exact momA2_8_8_0_3
  have a31 : momA2 8 8 3 1 = 0 := by rw [momA2_comm]; exact momA2_8_8_1_3
  have a32 : momA2 8 8 3 2 = 0 := by rw [momA2_comm]; exact momA2_8_8_2_3
  have a33 : momA2 8 8 3 3 = 0 := momA2_8_8_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_8_0_0, momB1_8_0_1, momB1_8_0_2, momB1_8_0_3, momB1_8_1_0, momB1_8_1_1, momB1_8_1_2, momB1_8_1_3, momB1_8_2_0, momB1_8_2_1, momB1_8_2_2, momB1_8_2_3, momB1_8_3_0, momB1_8_3_1, momB1_8_3_2, momB1_8_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_8_8 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 8 8 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 8 8 : ℂ)) := by
  rw [← Lval_eq_8_8]
  refine Kred_limit 8 8 k momA0_8_8 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_8_8_0
  · exact momA1_8_8_1
  · exact momA1_8_8_2
  · exact momA1_8_8_3

theorem Lval_eq_8_9 (k : Fin 4 → ℝ) : Lval 8 9 k = (KEH k 8 9 : ℂ) := by
  have a00 : momA2 8 9 0 0 = 0 := momA2_8_9_0_0
  have a01 : momA2 8 9 0 1 = 0 := momA2_8_9_0_1
  have a02 : momA2 8 9 0 2 = 0 := momA2_8_9_0_2
  have a03 : momA2 8 9 0 3 = 0 := momA2_8_9_0_3
  have a10 : momA2 8 9 1 0 = 0 := by rw [momA2_comm]; exact momA2_8_9_0_1
  have a11 : momA2 8 9 1 1 = 0 := momA2_8_9_1_1
  have a12 : momA2 8 9 1 2 = 0 := momA2_8_9_1_2
  have a13 : momA2 8 9 1 3 = 0 := momA2_8_9_1_3
  have a20 : momA2 8 9 2 0 = 0 := by rw [momA2_comm]; exact momA2_8_9_0_2
  have a21 : momA2 8 9 2 1 = 0 := by rw [momA2_comm]; exact momA2_8_9_1_2
  have a22 : momA2 8 9 2 2 = 0 := momA2_8_9_2_2
  have a23 : momA2 8 9 2 3 = 0 := momA2_8_9_2_3
  have a30 : momA2 8 9 3 0 = 0 := by rw [momA2_comm]; exact momA2_8_9_0_3
  have a31 : momA2 8 9 3 1 = 0 := by rw [momA2_comm]; exact momA2_8_9_1_3
  have a32 : momA2 8 9 3 2 = 0 := by rw [momA2_comm]; exact momA2_8_9_2_3
  have a33 : momA2 8 9 3 3 = 0 := momA2_8_9_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_8_0_0, momB1_8_0_1, momB1_8_0_2, momB1_8_0_3, momB1_8_1_0, momB1_8_1_1, momB1_8_1_2, momB1_8_1_3, momB1_8_2_0, momB1_8_2_1, momB1_8_2_2, momB1_8_2_3, momB1_8_3_0, momB1_8_3_1, momB1_8_3_2, momB1_8_3_3, momB1_9_0_0, momB1_9_0_1, momB1_9_0_2, momB1_9_0_3, momB1_9_1_0, momB1_9_1_1, momB1_9_1_2, momB1_9_1_3, momB1_9_2_0, momB1_9_2_1, momB1_9_2_2, momB1_9_2_3, momB1_9_3_0, momB1_9_3_1, momB1_9_3_2, momB1_9_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_8_9 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 8 9 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 8 9 : ℂ)) := by
  rw [← Lval_eq_8_9]
  refine Kred_limit 8 9 k momA0_8_9 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_8_9_0
  · exact momA1_8_9_1
  · exact momA1_8_9_2
  · exact momA1_8_9_3

theorem Lval_eq_9_9 (k : Fin 4 → ℝ) : Lval 9 9 k = (KEH k 9 9 : ℂ) := by
  have a00 : momA2 9 9 0 0 = 0 := momA2_9_9_0_0
  have a01 : momA2 9 9 0 1 = 0 := momA2_9_9_0_1
  have a02 : momA2 9 9 0 2 = 0 := momA2_9_9_0_2
  have a03 : momA2 9 9 0 3 = 0 := momA2_9_9_0_3
  have a10 : momA2 9 9 1 0 = 0 := by rw [momA2_comm]; exact momA2_9_9_0_1
  have a11 : momA2 9 9 1 1 = 0 := momA2_9_9_1_1
  have a12 : momA2 9 9 1 2 = 0 := momA2_9_9_1_2
  have a13 : momA2 9 9 1 3 = 0 := momA2_9_9_1_3
  have a20 : momA2 9 9 2 0 = 0 := by rw [momA2_comm]; exact momA2_9_9_0_2
  have a21 : momA2 9 9 2 1 = 0 := by rw [momA2_comm]; exact momA2_9_9_1_2
  have a22 : momA2 9 9 2 2 = 0 := momA2_9_9_2_2
  have a23 : momA2 9 9 2 3 = 0 := momA2_9_9_2_3
  have a30 : momA2 9 9 3 0 = 0 := by rw [momA2_comm]; exact momA2_9_9_0_3
  have a31 : momA2 9 9 3 1 = 0 := by rw [momA2_comm]; exact momA2_9_9_1_3
  have a32 : momA2 9 9 3 2 = 0 := by rw [momA2_comm]; exact momA2_9_9_2_3
  have a33 : momA2 9 9 3 3 = 0 := momA2_9_9_3_3
  simp only [Lval, m2A, m1B, Fin.sum_univ_four, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22,
    a23, a30, a31, a32, a33, momB1_9_0_0, momB1_9_0_1, momB1_9_0_2, momB1_9_0_3, momB1_9_1_0, momB1_9_1_1, momB1_9_1_2, momB1_9_1_3, momB1_9_2_0, momB1_9_2_1, momB1_9_2_2, momB1_9_2_3, momB1_9_3_0, momB1_9_3_1, momB1_9_3_2, momB1_9_3_3]
  simp only [KEH, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
  norm_num
  try (push_cast; ring)

theorem limit_9_9 (k : Fin 4 → ℝ) :
    Tendsto (fun ε : ℝ => Kred (ε • k) 9 9 / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k 9 9 : ℂ)) := by
  rw [← Lval_eq_9_9]
  refine Kred_limit 9 9 k momA0_9_9 (fun i => ?_) momB0_all
  fin_cases i
  · exact momA1_9_9_0
  · exact momA1_9_9_1
  · exact momA1_9_9_2
  · exact momA1_9_9_3

/-- **Symbol theorem.** For every momentum `k`, `ε⁻² Kred(εk) → KEH k` entrywise as `ε → 0`:
the gauge-reduced quadratic Regge action on the Freudenthal–Kuhn lattice converges to the
linearized Einstein–Hilbert kernel `(√g R)⁽²⁾`. -/
theorem symbol_limit (k : Fin 4 → ℝ) (c d : Fin 10) :
    Tendsto (fun ε : ℝ => Kred (ε • k) c d / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k c d : ℂ)) := by
  have upper : ∀ c d : Fin 10, c ≤ d →
      Tendsto (fun ε : ℝ => Kred (ε • k) c d / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (KEH k c d : ℂ)) := by
    intro c d h
    fin_cases c <;> fin_cases d <;> simp at h
    exacts [limit_0_0 k, limit_0_1 k, limit_0_2 k, limit_0_3 k, limit_0_4 k, limit_0_5 k, limit_0_6 k, limit_0_7 k, limit_0_8 k, limit_0_9 k, limit_1_1 k, limit_1_2 k, limit_1_3 k, limit_1_4 k, limit_1_5 k, limit_1_6 k, limit_1_7 k, limit_1_8 k, limit_1_9 k, limit_2_2 k, limit_2_3 k, limit_2_4 k, limit_2_5 k, limit_2_6 k, limit_2_7 k, limit_2_8 k, limit_2_9 k, limit_3_3 k, limit_3_4 k, limit_3_5 k, limit_3_6 k, limit_3_7 k, limit_3_8 k, limit_3_9 k, limit_4_4 k, limit_4_5 k, limit_4_6 k, limit_4_7 k, limit_4_8 k, limit_4_9 k, limit_5_5 k, limit_5_6 k, limit_5_7 k, limit_5_8 k, limit_5_9 k, limit_6_6 k, limit_6_7 k, limit_6_8 k, limit_6_9 k, limit_7_7 k, limit_7_8 k, limit_7_9 k, limit_8_8 k, limit_8_9 k, limit_9_9 k]
  rcases le_total c d with h | h
  · exact upper c d h
  · have := ((continuous_conj.tendsto _).comp (upper d c h))
    rw [Function.comp_def] at this
    simp only [conj_ofReal, KEH_symm k d c] at this
    refine this.congr fun ε => ?_
    rw [map_div₀, map_pow, conj_ofReal, ← (Kred_herm (ε • k)).apply c d]
    rfl

end Entropic.ReggeGraviton
