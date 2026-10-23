import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! Chunk 14 sweep: C07-88, Dirac action under discrete frame flips (matrix algebra).

Dirac representation, signature (−,+,+,+), {γ^μ, γ^ν} = −2g^{μν}: γ⁰ = diag(1, 1, −1, −1),
γ^i = [[0, σ_i], [−σ_i, 0]], γ⁵ = iγ⁰γ¹γ²γ³. With ψ' = Sψ and the physical conjugate ψ̄' = ψ'†γ⁰, the
mass term transforms by S†γ⁰S and the kinetic term by S†γ⁰γ^aS. -/

namespace Entropic.Sweep.Dirac
open Matrix Complex

def g0 : Matrix (Fin 4) (Fin 4) ℂ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]
def g1 : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]
def g2 : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, -I; 0, 0, I, 0; 0, I, 0, 0; -I, 0, 0, 0]
def g3 : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0]
def g5 : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
def G : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := ![g0, g1, g2, g3]

macro "mat_tac" : tactic => `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
  simp [G, g0, g1, g2, g3, g5, Matrix.mul_apply, Fin.sum_univ_four, Matrix.conjTranspose_apply]))

set_option maxHeartbeats 2000000 in
theorem clifford : (∀ a b : Fin 4, G a * G b + G b * G a =
    (if a = b then (if a = 0 then (2:ℂ) else -2) else 0) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) := by
  intro a b; fin_cases a <;> fin_cases b <;> mat_tac <;> norm_num

theorem g5_def : g5 = I • (g0 * g1 * g2 * g3) := by mat_tac
theorem g0_sq : g0 * g0 = 1 := by mat_tac
theorem g5_sq : g5 * g5 = 1 := by mat_tac
theorem g5_anti : ∀ a, g5 * G a = -(G a * g5) := by intro a; fin_cases a <;> mat_tac
theorem g5_herm : g5ᴴ = g5 := by mat_tac
theorem g0_herm : g0ᴴ = g0 := by mat_tac

/-- C07-88 (i): parity S = γ⁰: S†γ⁰S = γ⁰ and S†γ⁰γ^aS = Λ^a γ⁰γ^a with Λ = diag(1, −1, −1, −1). -/
theorem parity : g0ᴴ * g0 * g0 = g0 ∧ g0ᴴ * g0 * g0 * g0 = g0 * g0 ∧
    ∀ a : Fin 4, a ≠ 0 → g0ᴴ * g0 * G a * g0 = -(g0 * G a) := by
  refine ⟨by mat_tac, by mat_tac, ?_⟩
  intro a ha; fin_cases a
  · exact absurd rfl ha
  all_goals mat_tac

/-- C07-88 (ii): time flip S = γ⁵γ⁰: S†γ⁰S = −γ⁰ and S†γ⁰γ^aS = −Λ^a γ⁰γ^a with Λ = diag(−1, 1, 1, 1);
with the frame flip e_0 → −e_0 both terms change sign, which the signed volume form det e (odd under T)
compensates. -/
theorem time_flip : (g5 * g0)ᴴ * g0 * (g5 * g0) = -g0 ∧
    (g5 * g0)ᴴ * g0 * g0 * (g5 * g0) = g0 * g0 ∧
    ∀ a : Fin 4, a ≠ 0 → (g5 * g0)ᴴ * g0 * G a * (g5 * g0) = -(g0 * G a) := by
  refine ⟨by mat_tac, by mat_tac, ?_⟩
  intro a ha; fin_cases a
  · exact absurd rfl ha
  all_goals mat_tac

/-- C07-88 (iii): inversion S = γ⁵ with e → −e: S†γ⁰S = −γ⁰ (mass term reversed) and S†γ⁰γ^aS = γ⁰γ^a,
so with e_a^μ → −e_a^μ the kinetic term is reversed as well. -/
theorem inversion : g5ᴴ * g0 * g5 = -g0 ∧ ∀ a, g5ᴴ * g0 * G a * g5 = g0 * G a := by
  refine ⟨by mat_tac, ?_⟩
  intro a; fin_cases a <;> mat_tac

/-- A matrix commuting with γ⁰, …, γ³ is a scalar. -/
theorem comm_scalar (X : Matrix (Fin 4) (Fin 4) ℂ) (h : ∀ a, X * G a = G a * X) : X = X 0 0 • 1 := by
  have E : ∀ a i j, (X * G a) i j = (G a * X) i j := fun a i j => by rw [h a]
  ext i j; fin_cases i <;> fin_cases j
  · simp
  · have e0 := E 1 0 2
    have e1 := E 2 0 2
    simp [G, g0, g1, g2, g3, Matrix.mul_apply, Fin.sum_univ_four] at e0 e1 ⊢
    linear_combination (norm := (ring_nf <;> try simp only [I_sq] <;> ring_nf)) ((1:ℂ)/2) * e0 + (((-1:ℂ)/2) * Complex.I) * e1
  · have e0 := E 0 0 2
    simp [G, g0, g1, g2, g3, Matrix.mul_apply, Fin.sum_univ_four] at e0 ⊢
    linear_combination (norm := (ring_nf <;> try simp only [I_sq] <;> ring_nf)) ((-1:ℂ)/2) * e0
  · have e0 := E 0 0 3
    simp [G, g0, g1, g2, g3, Matrix.mul_apply, Fin.sum_univ_four] at e0 ⊢
    linear_combination (norm := (ring_nf <;> try simp only [I_sq] <;> ring_nf)) ((-1:ℂ)/2) * e0
  · have e0 := E 1 1 3
    have e1 := E 2 1 3
    simp [G, g0, g1, g2, g3, Matrix.mul_apply, Fin.sum_univ_four] at e0 e1 ⊢
    linear_combination (norm := (ring_nf <;> try simp only [I_sq] <;> ring_nf)) ((1:ℂ)/2) * e0 + (((1:ℂ)/2) * Complex.I) * e1
  · have e0 := E 1 1 2
    have e1 := E 3 0 2
    simp [G, g0, g1, g2, g3, Matrix.mul_apply, Fin.sum_univ_four] at e0 e1 ⊢
    linear_combination (norm := (ring_nf <;> try simp only [I_sq] <;> ring_nf)) (1:ℂ) * e0 + (-1:ℂ) * e1
  · have e0 := E 0 1 2
    simp [G, g0, g1, g2, g3, Matrix.mul_apply, Fin.sum_univ_four] at e0 ⊢
    linear_combination (norm := (ring_nf <;> try simp only [I_sq] <;> ring_nf)) ((-1:ℂ)/2) * e0
  · have e0 := E 0 1 3
    simp [G, g0, g1, g2, g3, Matrix.mul_apply, Fin.sum_univ_four] at e0 ⊢
    linear_combination (norm := (ring_nf <;> try simp only [I_sq] <;> ring_nf)) ((-1:ℂ)/2) * e0
  · have e0 := E 0 2 0
    simp [G, g0, g1, g2, g3, Matrix.mul_apply, Fin.sum_univ_four] at e0 ⊢
    linear_combination (norm := (ring_nf <;> try simp only [I_sq] <;> ring_nf)) ((1:ℂ)/2) * e0
  · have e0 := E 0 2 1
    simp [G, g0, g1, g2, g3, Matrix.mul_apply, Fin.sum_univ_four] at e0 ⊢
    linear_combination (norm := (ring_nf <;> try simp only [I_sq] <;> ring_nf)) ((1:ℂ)/2) * e0
  · have e0 := E 3 0 2
    simp [G, g0, g1, g2, g3, Matrix.mul_apply, Fin.sum_univ_four] at e0 ⊢
    linear_combination (norm := (ring_nf <;> try simp only [I_sq] <;> ring_nf)) (-1:ℂ) * e0
  · have e0 := E 1 1 3
    have e1 := E 2 1 3
    simp [G, g0, g1, g2, g3, Matrix.mul_apply, Fin.sum_univ_four] at e0 e1 ⊢
    linear_combination (norm := (ring_nf <;> try simp only [I_sq] <;> ring_nf)) ((-1:ℂ)/2) * e0 + (((1:ℂ)/2) * Complex.I) * e1
  · have e0 := E 0 3 0
    simp [G, g0, g1, g2, g3, Matrix.mul_apply, Fin.sum_univ_four] at e0 ⊢
    linear_combination (norm := (ring_nf <;> try simp only [I_sq] <;> ring_nf)) ((1:ℂ)/2) * e0
  · have e0 := E 0 3 1
    simp [G, g0, g1, g2, g3, Matrix.mul_apply, Fin.sum_univ_four] at e0 ⊢
    linear_combination (norm := (ring_nf <;> try simp only [I_sq] <;> ring_nf)) ((1:ℂ)/2) * e0
  · have e0 := E 1 0 2
    have e1 := E 2 0 2
    simp [G, g0, g1, g2, g3, Matrix.mul_apply, Fin.sum_univ_four] at e0 e1 ⊢
    linear_combination (norm := (ring_nf <;> try simp only [I_sq] <;> ring_nf)) ((-1:ℂ)/2) * e0 + (((-1:ℂ)/2) * Complex.I) * e1
  · have e0 := E 1 0 3
    simp [G, g0, g1, g2, g3, Matrix.mul_apply, Fin.sum_univ_four] at e0 ⊢
    linear_combination (norm := (ring_nf <;> try simp only [I_sq] <;> ring_nf)) (-1:ℂ) * e0

/-- C07-88 (iv): no spinor map S compensates the inversion e → −e with the physical conjugate:
there is no S with S†γ⁰S = γ⁰ (mass term preserved) and S†γ⁰γ^aS = −γ⁰γ^a for all a (kinetic term
compensated). Any such S anticommutes with every γ^a, so Sγ⁵ is a scalar c, S = cγ⁵, and then
S†γ⁰S = −|c|²γ⁰ ≠ γ⁰. -/
theorem no_compensation (S : Matrix (Fin 4) (Fin 4) ℂ) (hm : Sᴴ * g0 * S = g0)
    (hk : ∀ a, Sᴴ * g0 * G a * S = -(g0 * G a)) : False := by
  have hL : (g0 * (Sᴴ * g0)) * S = 1 := by rw [Matrix.mul_assoc, hm, g0_sq]
  have hR : S * (g0 * (Sᴴ * g0)) = 1 := mul_eq_one_comm.mp hL
  have anti : ∀ a, G a * S = -(S * G a) := by
    intro a
    have h1 : g0 * (Sᴴ * g0) * G a * S = -(G a) := by
      calc g0 * (Sᴴ * g0) * G a * S = g0 * (Sᴴ * g0 * G a * S) := by simp only [Matrix.mul_assoc]
        _ = g0 * (-(g0 * G a)) := by rw [hk a]
        _ = -(G a) := by rw [Matrix.mul_neg, ← Matrix.mul_assoc, g0_sq, Matrix.one_mul]
    calc G a * S = (S * (g0 * (Sᴴ * g0))) * G a * S := by rw [hR, Matrix.one_mul]
      _ = S * (g0 * (Sᴴ * g0) * G a * S) := by simp only [Matrix.mul_assoc]
      _ = -(S * G a) := by rw [h1, Matrix.mul_neg]
  have comm : ∀ a, (S * g5) * G a = G a * (S * g5) := by
    intro a
    rw [Matrix.mul_assoc, g5_anti a, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, anti a,
      Matrix.neg_mul]
  have hX := comm_scalar (S * g5) comm
  set c := (S * g5) 0 0
  have hS : S = c • g5 := by
    calc S = S * g5 * g5 := by rw [Matrix.mul_assoc, g5_sq, Matrix.mul_one]
      _ = (c • (1 : Matrix (Fin 4) (Fin 4) ℂ)) * g5 := by rw [← hX]
      _ = c • g5 := by rw [Matrix.smul_mul, Matrix.one_mul]
  have hinv : g5 * g0 * g5 = -g0 := by have := inversion.1; rwa [g5_herm] at this
  rw [hS, Matrix.conjTranspose_smul, g5_herm, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hinv] at hm
  have h00 := congrFun (congrFun hm 0) 0
  simp [g0] at h00
  have hn : (starRingEnd ℂ) c * c = (Complex.normSq c : ℂ) := by rw [mul_comm]; exact Complex.mul_conj c
  rw [hn] at h00
  have := congrArg Complex.re h00
  simp at this
  linarith [Complex.normSq_nonneg c]

/-! ### C04-74: the vector representation is spin one -/

/-- Generators of SO(3) on ℂ³: (L_a)_{bc} = −i ε_{abc}. -/
def Lx : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 0; 0, 0, -I; 0, I, 0]
def Ly : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, I; 0, 0, 0; -I, 0, 0]
def Lz : Matrix (Fin 3) (Fin 3) ℂ := !![0, -I, 0; I, 0, 0; 0, 0, 0]

macro "mat3_tac" : tactic => `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
  simp [Lx, Ly, Lz, Matrix.mul_apply, Fin.sum_univ_three] <;> ring_nf <;> simp [I_sq]))

/-- C04-74: the vector generators obey [L_x, L_y] = iL_z (cyclic), have Casimir L² = 2 = 1·(1+1), and
L_z has the eigenvectors (1, ±i, 0) with eigenvalues ∓1 and (0, 0, 1) with eigenvalue 0: the
complexified vector representation is the spin-1 irrep. -/
theorem vector_spin_one :
    Lx * Ly - Ly * Lx = I • Lz ∧ Ly * Lz - Lz * Ly = I • Lx ∧ Lz * Lx - Lx * Lz = I • Ly ∧
      Lx * Lx + Ly * Ly + Lz * Lz = (2:ℂ) • 1 ∧
      Lz *ᵥ ![1, I, 0] = ![1, I, 0] ∧ Lz *ᵥ ![1, -I, 0] = -(![1, -I, 0]) ∧ Lz *ᵥ ![0, 0, 1] = 0 := by
  refine ⟨by mat3_tac, by mat3_tac, by mat3_tac, by mat3_tac, ?_, ?_, ?_⟩ <;>
    (ext i; fin_cases i <;> simp [Lz, Matrix.mulVec, dotProduct, Fin.sum_univ_three])

end Entropic.Sweep.Dirac
