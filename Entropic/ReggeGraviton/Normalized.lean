import Entropic.ReggeGraviton.Graviton

/-!
# Frobenius-normalized graviton operator and its TT eigenspace

The coordinates `h_c` of a symmetric matrix `H = ∑_c h_c basisM c` carry the Frobenius weights
`∑_{μν} H_μν² = ∑_c w_c² h_c²` with `w_c = 1` (diagonal) or `√2` (off-diagonal). The physical
operators are the symmetrized `KEHg = D KEH D`, `Klatg = D Klat D`, `D = diag(1/w)`, which are
Hermitian for the Frobenius inner product.

* `regge_strong_resolvent_normalized`: the lattice operators converge to `KEHg` in the
  strong-resolvent sense.
* `KEHg_TT`: transverse-traceless polarizations form an eigenspace of `KEHg k` with eigenvalue
  `−¼|k|²` (the massless spin-2 symbol), as an operator statement.
-/

open Complex Filter Topology MeasureTheory Matrix

namespace Entropic.ReggeGraviton

attribute [local irreducible] typ base hz simplexData hzL

/-- Frobenius weight of metric coordinate `c`. -/
noncomputable def wt2 (c : Fin 10) : ℝ := if (symIdx c).1 = (symIdx c).2 then 1 else Real.sqrt 2

theorem wt2_pos (c : Fin 10) : 0 < wt2 c := by
  unfold wt2; split_ifs <;> positivity

theorem wt2_sq (c : Fin 10) : wt2 c ^ 2 = if (symIdx c).1 = (symIdx c).2 then 1 else 2 := by
  unfold wt2; split_ifs <;> simp

noncomputable def Dm : Matrix (Fin 10) (Fin 10) ℂ := Matrix.diagonal fun c => ((1 / wt2 c : ℝ) : ℂ)

theorem Dm_conjTranspose : Dmᴴ = Dm := by
  simp [Dm, Matrix.diagonal_conjTranspose]

noncomputable def KEHg (k : Fin 4 → ℝ) : Matrix (Fin 10) (Fin 10) ℂ := Dm * KEHm k * Dm
noncomputable def Klatg (a : ℝ) (k : Fin 4 → ℝ) : Matrix (Fin 10) (Fin 10) ℂ := Dm * Klat a k * Dm

theorem herm_sandwich {A : Matrix (Fin 10) (Fin 10) ℂ} (hA : A.IsHermitian) :
    (Dm * A * Dm).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Dm_conjTranspose, hA.eq, Matrix.mul_assoc]

/-- **Strong-resolvent convergence in the Frobenius-normalized coordinates.** -/
theorem regge_strong_resolvent_normalized {z : ℂ} (hz : z.im ≠ 0) (f : (Fin 4 → ℝ) → Fin 10 → ℂ)
    (hfm : AEStronglyMeasurable f volume) (hfi : Integrable fun k => nrm2 (f k)) :
    Tendsto (fun a => ∫ k, nrm2 ((BZ a).indicator (fun k => (Klatg a k - z • 1)⁻¹ *ᵥ f k) k -
      (KEHg k - z • 1)⁻¹ *ᵥ f k)) (𝓝[>] 0) (𝓝 0) := by
  have hcm : Continuous fun M : Matrix (Fin 10) (Fin 10) ℂ => Dm * M * Dm :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine strong_resolvent_conv Klatg KEHg BZ BZ_eventually measurableSet_BZ
    (fun a k => herm_sandwich (Klat_herm a k)) (fun k => herm_sandwich (KEHm_herm k))
    (fun k => (hcm.tendsto _).comp (Klat_limit k)) (fun a => hcm.comp (continuous_Klat a))
    (hcm.comp continuous_KEHm) hz f hfm hfi

set_option maxHeartbeats 4000000 in
/-- Row form of `KEH` against a symmetric matrix. -/
theorem KEH_row (k : Fin 4 → ℝ) (H : Fin 4 → Fin 4 → ℝ) (hH : ∀ μ ν, H μ ν = H ν μ) (c : Fin 10) :
    ∑ d, KEH k c d * coords H d =
      -(1 / 4) * (∑ μ, k μ ^ 2) * (∑ μ, ∑ ν, basisM c μ ν * H μ ν)
      + (1 / 2) * ∑ l, (∑ μ, k μ * basisM c μ l) * (∑ ν, k ν * H ν l)
      - (1 / 4) * ((∑ μ, ∑ ν, k μ * basisM c μ ν * k ν) * (∑ μ, H μ μ)
          + (∑ μ, ∑ ν, k μ * H μ ν * k ν) * (∑ μ, basisM c μ μ))
      + (1 / 4) * (∑ μ, k μ ^ 2) * (∑ μ, basisM c μ μ) * (∑ μ, H μ μ) := by
  have h10 := hH 1 0; have h20 := hH 2 0; have h30 := hH 3 0
  have h21 := hH 2 1; have h31 := hH 3 1; have h32 := hH 3 2
  fin_cases c <;>
  · simp only [KEH, coords, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
    norm_num
    try simp only [h10, h20, h30, h21, h31, h32]
    ring

set_option maxHeartbeats 4000000 in
theorem frob_coords (H : Fin 4 → Fin 4 → ℝ) (hH : ∀ μ ν, H μ ν = H ν μ) (c : Fin 10) :
    ∑ μ, ∑ ν, basisM c μ ν * H μ ν = wt2 c ^ 2 * coords H c := by
  have h10 := hH 1 0; have h20 := hH 2 0; have h30 := hH 3 0
  have h21 := hH 2 1; have h31 := hH 3 1; have h32 := hH 3 2
  rw [wt2_sq]
  fin_cases c <;>
  · simp only [coords, basisM, symIdx, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.mk.injEq]
    norm_num
    try simp only [h10, h20, h30, h21, h31, h32]
    try ring

/-- **TT eigenspace.** For symmetric, transverse (`kᵀH = 0`), traceless `H`, the Frobenius-normalized
coordinate vector `u_c = w_c h_c` satisfies `KEHg k · u = −¼|k|² u`. -/
theorem KEHg_TT (k : Fin 4 → ℝ) (H : Fin 4 → Fin 4 → ℝ) (hH : ∀ μ ν, H μ ν = H ν μ)
    (htr : ∀ ν, ∑ μ, k μ * H μ ν = 0) (htl : ∑ μ, H μ μ = 0) :
    KEHg k *ᵥ (fun c => ((wt2 c * coords H c : ℝ) : ℂ)) =
      (((-(1 / 4) * ∑ μ, k μ ^ 2 : ℝ) : ℂ)) • (fun c => ((wt2 c * coords H c : ℝ) : ℂ)) := by
  have h3 : ∑ μ, ∑ ν, k μ * H μ ν * k ν = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [← Finset.sum_mul, htr ν, zero_mul]
  have hrow : ∀ c, ∑ d, KEH k c d * coords H d = -(1 / 4) * (∑ μ, k μ ^ 2) * (wt2 c ^ 2 * coords H c) := by
    intro c
    rw [KEH_row k H hH c, frob_coords H hH c, h3, htl]
    simp [htr]
  funext c
  simp only [KEHg, Dm, KEHm, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.diagonal_apply,
    Pi.smul_apply, smul_eq_mul]
  have hw := (wt2_pos c).ne'
  have e : ∀ d, (∑ x, (∑ y, (if c = y then ((1 / wt2 c : ℝ) : ℂ) else 0) * (KEH k y x : ℂ)) *
      (if x = d then ((1 / wt2 x : ℝ) : ℂ) else 0)) * ((wt2 d * coords H d : ℝ) : ℂ) =
      ((1 / wt2 c : ℝ) : ℂ) * ((KEH k c d * coords H d : ℝ) : ℂ) := by
    intro d
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_ite, mul_zero,
      Finset.sum_ite_eq']
    have hwd : (wt2 d : ℂ) ≠ 0 := by exact_mod_cast (wt2_pos d).ne'
    have hwc : (wt2 c : ℂ) ≠ 0 := by exact_mod_cast (wt2_pos c).ne'
    push_cast
    field_simp
  rw [Finset.sum_congr rfl fun d _ => e d, ← Finset.mul_sum, ← ofReal_sum, hrow c]
  have hwc : (wt2 c : ℂ) ≠ 0 := by exact_mod_cast hw
  push_cast
  field_simp

end Entropic.ReggeGraviton
