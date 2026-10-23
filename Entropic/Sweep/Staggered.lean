import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-! Chunk 14 sweep: C09-65, staggered constraint complex identities.

Operators on the periodic cubic lattice are represented by their Laurent symbols in the shift
variables t = (t_x, t_y, t_z); the transpose of an operator matrix is the matrix transpose of the
symbol evaluated at t⁻¹. Identities are proved for every field K and every nonzero t. -/

namespace Entropic.Sweep.Stag
open Matrix

variable {K : Type*} [Field K] [CharZero K]

def tinv (t : Fin 3 → K) : Fin 3 → K := fun i => (t i)⁻¹
def Dp (t : Fin 3 → K) (i : Fin 3) : K := t i - 1
def Dm (t : Fin 3 → K) (i : Fin 3) : K := 1 - (t i)⁻¹
def Δ (t : Fin 3 → K) : K := Dm t 0 * Dp t 0 + Dm t 1 * Dp t 1 + Dm t 2 * Dp t 2

/-- (Gξ)_ii = 2D_i⁻ξ_i, (Gξ)_ij = D_i⁺ξ_j + D_j⁺ξ_i, rows xx, yy, zz, xy, xz, yz. -/
def G (t : Fin 3 → K) : Matrix (Fin 6) (Fin 3) K :=
  !![2 * Dm t 0, 0, 0; 0, 2 * Dm t 1, 0; 0, 0, 2 * Dm t 2;
     Dp t 1, Dp t 0, 0; Dp t 2, 0, Dp t 0; 0, Dp t 2, Dp t 1]
def Gadj (t : Fin 3 → K) : Matrix (Fin 3) (Fin 6) K := (G (tinv t))ᵀ
def W : Matrix (Fin 6) (Fin 6) K := Matrix.diagonal ![1, 1, 1, 2, 2, 2]
def Winv : Matrix (Fin 6) (Fin 6) K := Matrix.diagonal ![1, 1, 1, 1/2, 1/2, 1/2]
def Tm : Matrix (Fin 1) (Fin 6) K := !![1, 1, 1, 0, 0, 0]
def R (t : Fin 3 → K) : Matrix (Fin 3) (Fin 6) K := (-(1/2 : K)) • (Gadj t * W)
def dv (t : Fin 3 → K) : Matrix (Fin 1) (Fin 3) K := !![Dm t 0, Dm t 1, Dm t 2]
def B (t : Fin 3 → K) : Matrix (Fin 1) (Fin 6) K := dv t * R t
def C (t : Fin 3 → K) : Matrix (Fin 1) (Fin 6) K := B t - Δ t • Tm
def Kl (l : K) : Matrix (Fin 6) (Fin 6) K := Winv - l • (Tmᵀ * Tm)
def L (t : Fin 3 → K) : Matrix (Fin 6) (Fin 6) K :=
  (-Δ t) • W + Δ t • (Tmᵀ * Tm) - (2:K) • ((R (tinv t))ᵀ * R t) - Tmᵀ * B t - (B (tinv t))ᵀ * Tm

variable (t : Fin 3 → K) (h0 : t 0 ≠ 0) (h1 : t 1 ≠ 0) (h2 : t 2 ≠ 0)
include h0 h1 h2

/-- C09-65: C G = 0. -/
theorem CG_zero : C t * G t = 0 := by
  ext i j; fin_cases i; fin_cases j <;>
  simp only [L, C, B, R, Gadj, G, W, Winv, Kl, dv, Tm, Δ, Dp, Dm, tinv, Matrix.mul_apply, Fin.sum_univ_six,
    Fin.sum_univ_three, Fin.sum_univ_one, Matrix.of_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.diagonal_apply, Matrix.zero_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    smul_eq_mul, Fin.isValue, inv_inv] <;>
  simp <;> field_simp <;> ring

set_option maxHeartbeats 4000000 in
/-- C09-65: L G = 0. -/
theorem LG_zero : L t * G t = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
  simp only [L, C, B, R, Gadj, G, W, Winv, Kl, dv, Tm, Δ, Dp, Dm, tinv, Matrix.mul_apply, Fin.sum_univ_six,
    Fin.sum_univ_three, Fin.sum_univ_one, Matrix.of_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.diagonal_apply, Matrix.zero_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    smul_eq_mul, Fin.isValue, inv_inv] <;>
  simp <;> field_simp <;> ring

/-- C09-65: C(2K_λ) + d Gᵀ = 2(2λ − 1)Δ T; at λ = 1/2, C(2K) = −d Gᵀ. -/
theorem CK_lambda (l : K) : C t * ((2:K) • Kl l) + dv t * Gadj t = (2 * (2 * l - 1) * Δ t) • Tm := by
  ext i j; fin_cases i; fin_cases j <;>
  simp only [L, C, B, R, Gadj, G, W, Winv, Kl, dv, Tm, Δ, Dp, Dm, tinv, Matrix.mul_apply, Fin.sum_univ_six,
    Fin.sum_univ_three, Fin.sum_univ_one, Matrix.of_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.diagonal_apply, Matrix.zero_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    smul_eq_mul, Fin.isValue, inv_inv] <;>
  simp <;> field_simp <;> ring

theorem CK_half : C t * ((2:K) • Kl (1/2 : K)) = -(dv t * Gadj t) := by
  have := CK_lambda t h0 h1 h2 (1/2 : K)
  rw [show (2 * (2 * (1/2 : K) - 1) * Δ t) = 0 by ring, zero_smul] at this
  exact eq_neg_of_add_eq_zero_left this

set_option maxHeartbeats 4000000 in
/-- C09-65: L is symmetric: L(t⁻¹)ᵀ = L(t). -/
theorem L_symmetric : (L (tinv t))ᵀ = L t := by
  ext i j; fin_cases i <;> fin_cases j <;>
  simp only [L, C, B, R, Gadj, G, W, Winv, Kl, dv, Tm, Δ, Dp, Dm, tinv, Matrix.mul_apply, Fin.sum_univ_six,
    Fin.sum_univ_three, Fin.sum_univ_one, Matrix.of_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.diagonal_apply, Matrix.zero_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    smul_eq_mul, Fin.isValue, inv_inv] <;>
  simp <;> field_simp <;> ring

end Entropic.Sweep.Stag
