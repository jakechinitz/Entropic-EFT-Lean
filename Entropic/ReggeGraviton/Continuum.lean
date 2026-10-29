import Entropic.ReggeGraviton.Data

/-!
# The linearized Einstein–Hilbert kernel

`KEH k c d` is the Fourier kernel of the second-order part of `√g R` around flat Euclidean space,
in the coordinates `h = ∑_c h_c basisM c` of symmetric matrices:

  `(√g R)⁽²⁾ = −¼ ∂_λh_μν ∂_λh_μν + ½ (∂_μh_μλ)² − ½ ∂_μh ∂_νh_μν + ¼ (∂_λh)²`
  (up to total derivatives).

`KEH_quad`: in those coordinates the quadratic form is `FP k H` for every symmetric `H`.
`KEH_TT`: on transverse-traceless `H` it equals `−¼|k|² ∑ H_μν²`.
-/

namespace Entropic.ReggeGraviton

/-- Basis symmetric matrix of metric component `c`. -/
def basisM (c : Fin 10) (μ ν : Fin 4) : ℝ :=
  if (μ, ν) = symIdx c ∨ (ν, μ) = symIdx c then 1 else 0

/-- Fourier kernel of `(√g R)⁽²⁾` (Euclidean, flat background). -/
noncomputable def KEH (k : Fin 4 → ℝ) (c d : Fin 10) : ℝ :=
  -(1 / 4) * (∑ μ, k μ ^ 2) * (∑ μ, ∑ ν, basisM c μ ν * basisM d μ ν)
  + (1 / 2) * ∑ l, (∑ μ, k μ * basisM c μ l) * (∑ ν, k ν * basisM d ν l)
  - (1 / 4) * ((∑ μ, ∑ ν, k μ * basisM c μ ν * k ν) * (∑ μ, basisM d μ μ)
      + (∑ μ, ∑ ν, k μ * basisM d μ ν * k ν) * (∑ μ, basisM c μ μ))
  + (1 / 4) * (∑ μ, k μ ^ 2) * (∑ μ, basisM c μ μ) * (∑ μ, basisM d μ μ)

theorem KEH_symm (k : Fin 4 → ℝ) (c d : Fin 10) : KEH k c d = KEH k d c := by
  simp only [KEH]
  have h1 : ∑ μ, ∑ ν, basisM c μ ν * basisM d μ ν = ∑ μ, ∑ ν, basisM d μ ν * basisM c μ ν :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have h2 : ∑ l, (∑ μ, k μ * basisM c μ l) * (∑ ν, k ν * basisM d ν l) =
      ∑ l, (∑ μ, k μ * basisM d μ l) * (∑ ν, k ν * basisM c ν l) :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [h1, h2]; ring


/-- The Fierz–Pauli quadratic form of a symmetric matrix `H` at momentum `k`. -/
noncomputable def FP (k : Fin 4 → ℝ) (H : Fin 4 → Fin 4 → ℝ) : ℝ :=
  -(1 / 4) * (∑ μ, k μ ^ 2) * (∑ μ, ∑ ν, H μ ν ^ 2) + (1 / 2) * ∑ l, (∑ μ, k μ * H μ l) ^ 2
  - (1 / 2) * (∑ μ, ∑ ν, k μ * H μ ν * k ν) * (∑ μ, H μ μ)
  + (1 / 4) * (∑ μ, k μ ^ 2) * (∑ μ, H μ μ) ^ 2

/-- Coordinates of a symmetric matrix. -/
def coords (H : Fin 4 → Fin 4 → ℝ) (c : Fin 10) : ℝ := H (symIdx c).1 (symIdx c).2

end Entropic.ReggeGraviton

namespace Entropic.ReggeGraviton

/-- In metric coordinates, `KEH k` is the Fierz–Pauli form: `∑_{cd} h_c KEH_{cd} h_d = FP k H`. -/
theorem KEH_quad (k : Fin 4 → ℝ) (H : Fin 4 → Fin 4 → ℝ) (hH : ∀ μ ν, H μ ν = H ν μ) :
    ∑ c, ∑ d, coords H c * KEH k c d * coords H d = FP k H := by
  have h10 := hH 1 0; have h20 := hH 2 0; have h30 := hH 3 0
  have h21 := hH 2 1; have h31 := hH 3 1; have h32 := hH 3 2
  simp only [KEH, FP, coords, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Prod.mk.injEq]
  norm_num
  rw [h10, h20, h30, h21, h31, h32]
  ring

/-- **Transverse-traceless sector.** For `kᵀH = 0` and `tr H = 0`, the kernel is `−¼|k|²`. -/
theorem KEH_TT (k : Fin 4 → ℝ) (H : Fin 4 → Fin 4 → ℝ) (hH : ∀ μ ν, H μ ν = H ν μ)
    (htr : ∀ ν, ∑ μ, k μ * H μ ν = 0) (htl : ∑ μ, H μ μ = 0) :
    ∑ c, ∑ d, coords H c * KEH k c d * coords H d = -(1 / 4) * (∑ μ, k μ ^ 2) * ∑ μ, ∑ ν, H μ ν ^ 2 := by
  rw [KEH_quad k H hH, FP]
  have h3 : ∑ μ, ∑ ν, k μ * H μ ν * k ν = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [← Finset.sum_mul, htr ν, zero_mul]
  simp [htr, h3, htl]

end Entropic.ReggeGraviton
