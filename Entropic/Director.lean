import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Director completion of the resolved-disk response (main manuscript Sec. 15,
App. N.8). For a unit director field ê with gradient A_{ai} = ∂_i ê^a, the
completed stiffness density is
    𝒮 = |∂ê|² + s[ê],   s = ∂_i ê^a ∂_a ê^i − (∇·ê)²,
i.e. 𝒮(A) = tr(AᵀA) + tr(A²) − (tr A)².
Unit length gives the pointwise constraint Σ_a ê^a A_{ai} = 0.

Proved here, pointwise and for every unit director:
* 𝒮 ≥ 0 (the manuscript's (λ₁−λ₂)² + |bend|² form, via a Householder frame);
* 𝒮 is invariant under orthogonal frame changes;
* on a radial director A = (1 − n nᵀ)/r, |∂ê|² + κ s vanishes iff κ = 1. -/

noncomputable section
namespace Entropic.Director
open Matrix

abbrev M3 := Matrix (Fin 3) (Fin 3) ℝ

def S (A : M3) : ℝ := (Aᵀ * A).trace + (A * A).trace - A.trace ^ 2

theorem tr_conj (X R : M3) (hR : Rᵀ * R = 1) : (R * X * Rᵀ).trace = X.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hR, Matrix.one_mul]

theorem S_conj (A R : M3) (hR : Rᵀ * R = 1) : S (R * A * Rᵀ) = S A := by
  unfold S
  have e1 : (R * A * Rᵀ)ᵀ * (R * A * Rᵀ) = R * (Aᵀ * A) * Rᵀ := by
    simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Rᵀ R, hR, Matrix.one_mul]
  have e2 : (R * A * Rᵀ) * (R * A * Rᵀ) = R * (A * A) * Rᵀ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Rᵀ R, hR, Matrix.one_mul]
  rw [e1, e2, tr_conj _ _ hR, tr_conj _ _ hR, tr_conj _ _ hR]

/-- Adapted frame (director along the third axis, so the third row vanishes):
𝒮 = (a−f)² + (b+d)² + c² + g² — the anisotropic-splay square plus |bend|². -/
theorem S_adapted (A : M3) (h : ∀ j, A 2 j = 0) :
    S A = (A 0 0 - A 1 1) ^ 2 + (A 0 1 + A 1 0) ^ 2 + A 0 2 ^ 2 + A 1 2 ^ 2 := by
  unfold S
  simp only [trace, diag, mul_apply, transpose_apply, Fin.sum_univ_three, h]
  ring

/-- Householder reflection along (x, y, z). -/
def refl (x y z : ℝ) : M3 :=
  let k := x ^ 2 + y ^ 2 + z ^ 2
  !![1 - 2 * x * x / k, -(2 * x * y / k), -(2 * x * z / k);
     -(2 * y * x / k), 1 - 2 * y * y / k, -(2 * y * z / k);
     -(2 * z * x / k), -(2 * z * y / k), 1 - 2 * z * z / k]

set_option maxHeartbeats 1000000 in
theorem refl_orth (x y z : ℝ) (hk : x ^ 2 + y ^ 2 + z ^ 2 ≠ 0) : (refl x y z)ᵀ * refl x y z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [refl, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;>
    field_simp <;> ring

def house (e : Fin 3 → ℝ) : M3 :=
  if 0 ≤ e 2 then refl (e 0) (e 1) (e 2 + 1) else refl (e 0) (e 1) (e 2 - 1)

theorem house_orth (e : Fin 3 → ℝ) : (house e)ᵀ * house e = 1 := by
  unfold house
  split_ifs with h
  · exact refl_orth _ _ _ (by nlinarith [sq_nonneg (e 0), sq_nonneg (e 1)])
  · push_neg at h; exact refl_orth _ _ _ (by nlinarith [sq_nonneg (e 0), sq_nonneg (e 1)])

/-- The third row of the reflection is ±eᵀ (uses |e| = 1). -/
theorem house_row2 (e : Fin 3 → ℝ) (he : e 0 ^ 2 + e 1 ^ 2 + e 2 ^ 2 = 1) :
    ∃ s : ℝ, ∀ a, house e 2 a = s * e a := by
  unfold house
  split_ifs with h
  · refine ⟨-1, fun a => ?_⟩
    have hk : e 0 ^ 2 + e 1 ^ 2 + (e 2 + 1) ^ 2 = 2 * (e 2 + 1) := by linear_combination he
    have hk0 : e 2 + 1 ≠ 0 := by linarith
    fin_cases a <;> simp [refl, hk] <;> field_simp <;> ring
  · refine ⟨1, fun a => ?_⟩
    have hk : e 0 ^ 2 + e 1 ^ 2 + (e 2 - 1) ^ 2 = 2 * (1 - e 2) := by linear_combination he
    have hk0 : 1 - e 2 ≠ 0 := by push_neg at h; linarith
    fin_cases a <;> simp [refl, hk] <;> field_simp <;> ring

/-- 𝒮 ≥ 0 for the gradient of every unit director field (pointwise). -/
theorem S_nonneg (e : Fin 3 → ℝ) (he : e 0 ^ 2 + e 1 ^ 2 + e 2 ^ 2 = 1) (A : M3)
    (hunit : ∀ i, ∑ a, e a * A a i = 0) : 0 ≤ S A := by
  have hH : (house e)ᵀ * house e = 1 := house_orth e
  obtain ⟨s, hs⟩ := house_row2 e he
  have h1 : ∀ b, (house e * A) 2 b = 0 := by
    intro b
    rw [Matrix.mul_apply]
    simp only [hs]
    have := hunit b
    simp only [Fin.sum_univ_three] at this ⊢
    linear_combination s * this
  have hrow : ∀ j, (house e * A * (house e)ᵀ) 2 j = 0 := by
    intro j
    rw [Matrix.mul_apply]
    simp [h1]
  rw [← S_conj A (house e) hH, S_adapted _ hrow]
  positivity

/-- Radial director: A = (1 − n nᵀ)/r with |n| = 1. Then |∂ê|² = 2/r², s = −2/r²,
and |∂ê|² + κ s = 0 holds iff κ = 1. -/
theorem radial_selects_kappa (n : Fin 3 → ℝ) (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) {r : ℝ}
    (hr : r ≠ 0) (κ : ℝ) :
    let A : M3 := of fun a i => ((if a = i then 1 else 0) - n a * n i) / r
    (Aᵀ * A).trace = 2 / r ^ 2 ∧ (A * A).trace - A.trace ^ 2 = -2 / r ^ 2 ∧
      ((Aᵀ * A).trace + κ * ((A * A).trace - A.trace ^ 2) = 0 ↔ κ = 1) ∧ S A = 0 := by
  intro A
  have hr2 : (0:ℝ) < r ^ 2 := by positivity
  set s := n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 with hs
  have k1 : (Aᵀ * A).trace * r ^ 2 = 3 - 2 * s + s ^ 2 := by
    simp only [A, trace, diag, mul_apply, transpose_apply, of_apply, Fin.sum_univ_three]
    simp only [Fin.isValue, Fin.reduceEq, if_true, if_false]
    field_simp <;> ring
  have k2 : (A * A).trace * r ^ 2 = 3 - 2 * s + s ^ 2 := by
    simp only [A, trace, diag, mul_apply, of_apply, Fin.sum_univ_three]
    simp only [Fin.isValue, Fin.reduceEq, if_true, if_false]
    field_simp <;> ring
  have k3 : A.trace * r = 3 - s := by
    simp only [A, trace, diag, of_apply, Fin.sum_univ_three]
    simp only [Fin.isValue, if_true]
    field_simp <;> ring
  have h1 : (Aᵀ * A).trace = 2 / r ^ 2 := by
    rw [eq_div_iff hr2.ne', k1, hn]; norm_num
  have h2 : (A * A).trace - A.trace ^ 2 = -2 / r ^ 2 := by
    have t2 : (A * A).trace = 2 / r ^ 2 := by rw [eq_div_iff hr2.ne', k2, hn]; norm_num
    have t3 : A.trace = 2 / r := by rw [eq_div_iff hr, k3, hn]; norm_num
    rw [t2, t3]; field_simp <;> ring
  have hS : S A = 0 := by
    unfold S
    have : (Aᵀ * A).trace + (A * A).trace - A.trace ^ 2 = (Aᵀ * A).trace + ((A * A).trace - A.trace ^ 2) := by ring
    rw [this, h1, h2]; ring
  refine ⟨h1, h2, ?_, hS⟩
  rw [h1, h2]
  constructor
  · intro h; field_simp at h; nlinarith
  · rintro rfl; field_simp; ring

/-- The completed density vanishes on uniform directors (radial: see above). -/
theorem S_uniform_zero : S 0 = 0 := by simp [S]

end Entropic.Director
