import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Second pass, chunk 15: Schur lemma for SU(2) ladder irreps and equivariant uniqueness
(C03-24, C15-10, C15-11, C04-72, C07-126).

A spin-j irrep with n = 2j + 1 is presented in a ladder basis: J_z (or H = 2J_z) diagonal with distinct
entries and J₊ supported on the superdiagonal with nonzero entries. Every orthonormal |j, m⟩ basis is
carried to such a basis by an invertible diagonal matrix, so the statements below, which are invariant
under similarity, apply to any basis. Equivariance under SU(2) is used through its generators. -/

namespace Entropic.Pass2.Schur
open Matrix

variable {K : Type*} [Field K]

/-- Superdiagonal matrix with entries p i at (i, i + 1). -/
def sup {n : ℕ} (p : Fin n → K) : Matrix (Fin n) (Fin n) K := fun i j => if j.val = i.val + 1 then p i else 0

theorem offdiag_zero {n : ℕ} (X : Matrix (Fin n) (Fin n) K) (d : Fin n → K) (hd : Function.Injective d)
    (h : X * diagonal d = diagonal d * X) (i j : Fin n) (hij : i ≠ j) : X i j = 0 := by
  have e := congrFun (congrFun h i) j
  rw [mul_diagonal, diagonal_mul] at e
  have : (d j - d i) * X i j = 0 := by linear_combination e
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (hd (sub_eq_zero.mp h0)).symm hij
  · exact h0

theorem diag_step {n : ℕ} (X : Matrix (Fin n) (Fin n) K) (p : Fin n → K) (hp : ∀ i, p i ≠ 0)
    (d : Fin n → K) (hd : Function.Injective d) (h1 : X * diagonal d = diagonal d * X)
    (h2 : X * sup p = sup p * X) (i j : Fin n) (hij : j.val = i.val + 1) : X i i = X j j := by
  have e := congrFun (congrFun h2 i) j
  simp only [mul_apply, sup] at e
  have l : ∑ k, X i k * (if j.val = k.val + 1 then p k else 0) = X i i * p i := by
    rw [Finset.sum_eq_single i]
    · rw [if_pos hij]
    · intro k _ hk
      by_cases hkj : j.val = k.val + 1
      · exact absurd (Fin.ext (by omega)) hk
      · rw [if_neg hkj, mul_zero]
    · simp
  have r : ∑ k, (if k.val = i.val + 1 then p i else 0) * X k j = p i * X j j := by
    rw [Finset.sum_eq_single j]
    · rw [if_pos hij]
    · intro k _ hk
      by_cases hk' : k.val = i.val + 1
      · exact absurd (Fin.ext (by omega)) hk
      · rw [if_neg hk', zero_mul]
    · simp
  rw [l, r] at e
  have : p i * (X i i - X j j) = 0 := by linear_combination e
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left (hp i))

/-- Schur's lemma for a ladder irrep: a matrix commuting with H (distinct diagonal entries) and with J₊
(nonzero superdiagonal) is a scalar. -/
theorem schur_ladder {n : ℕ} (X : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (d : Fin (n + 1) → K)
    (hd : Function.Injective d) (p : Fin (n + 1) → K) (hp : ∀ i, p i ≠ 0)
    (h1 : X * diagonal d = diagonal d * X) (h2 : X * sup p = sup p * X) : X = X 0 0 • 1 := by
  have hdiag : ∀ k : ℕ, (hk : k < n + 1) → X ⟨k, hk⟩ ⟨k, hk⟩ = X 0 0 := by
    intro k; induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [← ih (by omega)]
      exact (diag_step X p hp d hd h1 h2 ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl).symm
  ext i j
  rw [Matrix.smul_apply, one_apply]
  by_cases hij : i = j
  · subst hij; rw [if_pos rfl, smul_eq_mul, mul_one]; exact hdiag i.val i.isLt
  · rw [if_neg hij, smul_zero]; exact offdiag_zero X d hd h1 i j hij

/-- Basis-free form: if J_z and J₊ are similar, by one invertible S, to ladder form, every matrix commuting
with both is a scalar. -/
theorem schur_similar {n : ℕ} (X S : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hS : IsUnit S.det)
    (d : Fin (n + 1) → K) (hd : Function.Injective d) (p : Fin (n + 1) → K) (hp : ∀ i, p i ≠ 0)
    (h1 : X * (S * diagonal d * S⁻¹) = (S * diagonal d * S⁻¹) * X)
    (h2 : X * (S * sup p * S⁻¹) = (S * sup p * S⁻¹) * X) : ∃ c : K, X = c • 1 := by
  set Y := S⁻¹ * X * S with hY
  have hSS : S⁻¹ * S = 1 := nonsing_inv_mul S hS
  have hSS' : S * S⁻¹ = 1 := mul_nonsing_inv S hS
  have conj : ∀ A : Matrix (Fin (n + 1)) (Fin (n + 1)) K, X * (S * A * S⁻¹) = (S * A * S⁻¹) * X →
      Y * A = A * Y := by
    intro A h
    have := congrArg (fun M => S⁻¹ * M * S) h
    simp only [Matrix.mul_assoc] at this
    simp only [hY, Matrix.mul_assoc]
    calc S⁻¹ * (X * (S * A)) = S⁻¹ * (X * (S * (A * (S⁻¹ * S)))) := by rw [hSS, Matrix.mul_one]
      _ = S⁻¹ * (S * (A * (S⁻¹ * (X * S)))) := by
          have := this; simp only [← Matrix.mul_assoc] at this ⊢; rw [this]
      _ = A * (S⁻¹ * (X * S)) := by rw [← Matrix.mul_assoc S⁻¹ S, hSS, Matrix.one_mul]
  have hY' := schur_ladder Y d hd p hp (conj _ h1) (conj _ h2)
  generalize Y 0 0 = c at hY'
  refine ⟨c, ?_⟩
  calc X = S * Y * S⁻¹ := by
        simp only [hY, ← Matrix.mul_assoc, hSS', Matrix.one_mul]; rw [Matrix.mul_assoc, hSS', Matrix.mul_one]
    _ = c • 1 := by rw [hY', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hSS']

/-! ### V₃ (dimension 7): the frame lock is unique up to a scalar, a phase when unitary -/

def d7 : Fin 7 → ℂ := fun k => (6 - 2 * (k.val : ℂ))
theorem d7_inj : Function.Injective d7 := by
  intro a b h
  simp only [d7] at h
  have : (a.val : ℂ) = b.val := by linear_combination -h / 2
  exact Fin.ext (by exact_mod_cast this)

/-- C03-24, C15-10: two realizations of V₃ related by a fixed equivariant W (J' = W J W⁻¹). Any L with
L J = J' L for J_z and J₊ equals c W; if L and W are unitary, |c| = 1. -/
theorem lock_unique (L W : Matrix (Fin 7) (Fin 7) ℂ) (hW : IsUnit W.det)
    (h1 : L * diagonal d7 = (W * diagonal d7 * W⁻¹) * L)
    (h2 : L * sup (fun _ => (1:ℂ)) = (W * sup (fun _ => (1:ℂ)) * W⁻¹) * L) :
    ∃ c : ℂ, L = c • W := by
  set X := W⁻¹ * L
  have hWW : W⁻¹ * W = 1 := nonsing_inv_mul W hW
  have hWW' : W * W⁻¹ = 1 := mul_nonsing_inv W hW
  have c1 : ∀ A : Matrix (Fin 7) (Fin 7) ℂ, L * A = (W * A * W⁻¹) * L → X * A = A * X := by
    intro A h
    calc X * A = W⁻¹ * (L * A) := by simp only [X, Matrix.mul_assoc]
      _ = W⁻¹ * ((W * A * W⁻¹) * L) := by rw [h]
      _ = A * X := by simp only [X, ← Matrix.mul_assoc, hWW, Matrix.one_mul]
  have hX := schur_ladder X d7 d7_inj (fun _ => (1:ℂ)) (fun _ => one_ne_zero) (by
    simpa using c1 _ h1) (c1 _ h2)
  have hLX : L = W * X := by simp only [X, ← Matrix.mul_assoc, hWW', Matrix.one_mul]
  generalize X 0 0 = c at hX
  exact ⟨c, by rw [hLX, hX, Matrix.mul_smul, Matrix.mul_one]⟩

theorem phase_of_unitary (c : ℂ) (W : Matrix (Fin 7) (Fin 7) ℂ) (hW : Wᴴ * W = 1) (hL : (c • W)ᴴ * (c • W) = 1) :
    Complex.normSq c = 1 := by
  rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hW, smul_smul] at hL
  have := congrFun (congrFun hL 0) 0
  simp at this
  have h2 : (starRingEnd ℂ c) * c = (Complex.normSq c : ℂ) := by rw [mul_comm]; exact Complex.mul_conj c
  rw [h2] at this
  exact_mod_cast this

/-! ### V₀ ⊕ V₁ ⊕ V₂ (dimension 9): the commutant is three block scalars -/

def H9 : Matrix (Fin 9) (Fin 9) ℂ := diagonal ![0, 2, 0, -2, 4, 2, 0, -2, -4]
def P9 : Matrix (Fin 9) (Fin 9) ℂ := fun i j =>
  if (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 3) ∨ (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 6) ∨
    (i.val = 6 ∧ j.val = 7) ∨ (i.val = 7 ∧ j.val = 8) then 1 else 0
def E0 : Matrix (Fin 9) (Fin 9) ℂ := diagonal ![1, 0, 0, 0, 0, 0, 0, 0, 0]
def E1 : Matrix (Fin 9) (Fin 9) ℂ := diagonal ![0, 1, 1, 1, 0, 0, 0, 0, 0]
def E2 : Matrix (Fin 9) (Fin 9) ℂ := diagonal ![0, 0, 0, 0, 1, 1, 1, 1, 1]

set_option maxHeartbeats 4000000 in
/-- C07-126, C15-11, C04-72: every matrix commuting with J_z and J₊ of V₀ ⊕ V₁ ⊕ V₂ is a combination of
the three block identities. -/
theorem block_commutant (X : Matrix (Fin 9) (Fin 9) ℂ) (h1 : X * H9 = H9 * X) (h2 : X * P9 = P9 * X) :
    X = X 0 0 • E0 + X 1 1 • E1 + X 4 4 • E2 := by
  ext i j; fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2]
  · have e0 := congrFun (congrFun h1 0) 1
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h2 0) 3
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) (1:ℂ) * e0
  · have e0 := congrFun (congrFun h1 0) 3
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h1 0) 4
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/4) * e0
  · have e0 := congrFun (congrFun h1 0) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h2 0) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) (1:ℂ) * e0
  · have e0 := congrFun (congrFun h1 0) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h1 0) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/4) * e0
  · have e0 := congrFun (congrFun h1 1) 0
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/2) * e0
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2]
  · have e0 := congrFun (congrFun h1 1) 2
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h1 1) 3
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/4) * e0
  · have e0 := congrFun (congrFun h1 1) 4
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h2 1) 6
    have e1 := congrFun (congrFun h2 2) 7
    have e2 := congrFun (congrFun h2 3) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) (1:ℂ) * e0 + (1:ℂ) * e1 + (1:ℂ) * e2
  · have e0 := congrFun (congrFun h1 1) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h1 1) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/4) * e0
  · have e0 := congrFun (congrFun h1 1) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/6) * e0
  · have e0 := congrFun (congrFun h2 1) 0
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) (-1:ℂ) * e0
  · have e0 := congrFun (congrFun h1 2) 1
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h2 1) 2
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) (-1:ℂ) * e0
  · have e0 := congrFun (congrFun h1 2) 3
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h1 2) 4
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/4) * e0
  · have e0 := congrFun (congrFun h1 2) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h2 2) 7
    have e1 := congrFun (congrFun h2 3) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) (1:ℂ) * e0 + (1:ℂ) * e1
  · have e0 := congrFun (congrFun h1 2) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h1 2) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/4) * e0
  · have e0 := congrFun (congrFun h1 3) 0
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h1 3) 1
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/4) * e0
  · have e0 := congrFun (congrFun h1 3) 2
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h2 1) 2
    have e1 := congrFun (congrFun h2 2) 3
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) (-1:ℂ) * e0 + (-1:ℂ) * e1
  · have e0 := congrFun (congrFun h1 3) 4
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/6) * e0
  · have e0 := congrFun (congrFun h1 3) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/4) * e0
  · have e0 := congrFun (congrFun h1 3) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h2 3) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) (1:ℂ) * e0
  · have e0 := congrFun (congrFun h1 3) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h1 4) 0
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/4) * e0
  · have e0 := congrFun (congrFun h1 4) 1
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h1 4) 2
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/4) * e0
  · have e0 := congrFun (congrFun h1 4) 3
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/6) * e0
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2]
  · have e0 := congrFun (congrFun h1 4) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h1 4) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/4) * e0
  · have e0 := congrFun (congrFun h1 4) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/6) * e0
  · have e0 := congrFun (congrFun h1 4) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/8) * e0
  · have e0 := congrFun (congrFun h1 5) 0
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h2 4) 1
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) (-1:ℂ) * e0
  · have e0 := congrFun (congrFun h1 5) 2
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h1 5) 3
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/4) * e0
  · have e0 := congrFun (congrFun h1 5) 4
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h2 4) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) (-1:ℂ) * e0
  · have e0 := congrFun (congrFun h1 5) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h1 5) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/4) * e0
  · have e0 := congrFun (congrFun h1 5) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/6) * e0
  · have e0 := congrFun (congrFun h2 5) 0
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) (-1:ℂ) * e0
  · have e0 := congrFun (congrFun h1 6) 1
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h2 4) 1
    have e1 := congrFun (congrFun h2 5) 2
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) (-1:ℂ) * e0 + (-1:ℂ) * e1
  · have e0 := congrFun (congrFun h1 6) 3
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h1 6) 4
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/4) * e0
  · have e0 := congrFun (congrFun h1 6) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h2 4) 5
    have e1 := congrFun (congrFun h2 5) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) (-1:ℂ) * e0 + (-1:ℂ) * e1
  · have e0 := congrFun (congrFun h1 6) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h1 6) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/4) * e0
  · have e0 := congrFun (congrFun h1 7) 0
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h1 7) 1
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/4) * e0
  · have e0 := congrFun (congrFun h1 7) 2
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h2 4) 1
    have e1 := congrFun (congrFun h2 5) 2
    have e2 := congrFun (congrFun h2 6) 3
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) (-1:ℂ) * e0 + (-1:ℂ) * e1 + (-1:ℂ) * e2
  · have e0 := congrFun (congrFun h1 7) 4
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/6) * e0
  · have e0 := congrFun (congrFun h1 7) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/4) * e0
  · have e0 := congrFun (congrFun h1 7) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h2 4) 5
    have e1 := congrFun (congrFun h2 5) 6
    have e2 := congrFun (congrFun h2 6) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) (-1:ℂ) * e0 + (-1:ℂ) * e1 + (-1:ℂ) * e2
  · have e0 := congrFun (congrFun h1 7) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((-1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h1 8) 0
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/4) * e0
  · have e0 := congrFun (congrFun h1 8) 1
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/6) * e0
  · have e0 := congrFun (congrFun h1 8) 2
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/4) * e0
  · have e0 := congrFun (congrFun h1 8) 3
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h1 8) 4
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/8) * e0
  · have e0 := congrFun (congrFun h1 8) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/6) * e0
  · have e0 := congrFun (congrFun h1 8) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/4) * e0
  · have e0 := congrFun (congrFun h1 8) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) ((1:ℂ)/2) * e0
  · have e0 := congrFun (congrFun h2 4) 5
    have e1 := congrFun (congrFun h2 5) 6
    have e2 := congrFun (congrFun h2 6) 7
    have e3 := congrFun (congrFun h2 7) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, H9, P9, E0, E1, E2] <;> ring_nf)) (-1:ℂ) * e0 + (-1:ℂ) * e1 + (-1:ℂ) * e2 + (-1:ℂ) * e3

theorem blocks_idem : E0 * E0 = E0 ∧ E1 * E1 = E1 ∧ E2 * E2 = E2 ∧ E0 * E1 = 0 ∧ E0 * E2 = 0 ∧ E1 * E2 = 0 ∧
    E0 + E1 + E2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [E0, E1, E2, Matrix.one_apply]

/-- C07-126: End_{SU(2)}(V₀ ⊕ V₁ ⊕ V₂) ≅ ℂ³: block scalars commute with the generators, multiply
componentwise (the blocks are orthogonal idempotents summing to I), and every commuting matrix is one. -/
theorem blocks_diag (a b c : ℂ) :
    a • E0 + b • E1 + c • E2 = diagonal ![a, b, b, b, c, c, c, c, c] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E0, E1, E2]

theorem commutant_C3 (a b c : ℂ) :
    (a • E0 + b • E1 + c • E2) * H9 = H9 * (a • E0 + b • E1 + c • E2) ∧
      (a • E0 + b • E1 + c • E2) * P9 = P9 * (a • E0 + b • E1 + c • E2) := by
  rw [blocks_diag]
  refine ⟨?_, ?_⟩
  · simp only [H9, diagonal_mul_diagonal]; congr 1; ext i; ring
  · ext i j; rw [diagonal_mul, mul_diagonal]
    fin_cases i <;> fin_cases j <;> simp [P9]

/-- C15-11, C04-72: an equivariant unitary on V₀ ⊕ V₁ ⊕ V₂ is diag(e^{iφ₀} I₁, e^{iφ₁} I₃, e^{iφ₂} I₅). -/
theorem block_phases (X : Matrix (Fin 9) (Fin 9) ℂ) (h1 : X * H9 = H9 * X) (h2 : X * P9 = P9 * X)
    (hu : Xᴴ * X = 1) :
    Complex.normSq (X 0 0) = 1 ∧ Complex.normSq (X 1 1) = 1 ∧ Complex.normSq (X 4 4) = 1 := by
  have hX := block_commutant X h1 h2
  have e00 := congrFun (congrFun hu 0) 0
  have e11 := congrFun (congrFun hu 1) 1
  have e44 := congrFun (congrFun hu 4) 4
  rw [hX] at e00 e11 e44
  simp [E0, E1, E2, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] at e00 e11 e44
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg Complex.re e00; simpa [Complex.normSq_apply, ← sq] using this
  · have := congrArg Complex.re e11; simpa [Complex.normSq_apply, ← sq] using this
  · have := congrArg Complex.re e44; simpa [Complex.normSq_apply, ← sq] using this

end Entropic.Pass2.Schur
