import Entropic.ReggeGraviton.Symbol
import Entropic.ReggeGraviton.MomentsB

/-!
# The reduced kernel is the Schur complement over the body diagonals

`KC j j' q` is the body-diagonal block of the lattice Hessian at momentum `q`. From the kernel-computed
`bodyC = −24 δ` and `bodyD = 0` (no nonzero body–body term carries a displacement), `KC q = −½ I`
for every `q` (`KC_eq`), and `Kred q = A − B C⁻¹ B†` with `A = KA`, `B = KB`, `C = KC`
(`Kred_schur`): integrating out the body-diagonal fluctuations of the Gaussian lattice action.
-/

open Complex Matrix

namespace Entropic.ReggeGraviton

attribute [local irreducible] typ base hz simplexData hzL

/-- Body-diagonal block of the lattice Hessian. -/
noncomputable def KC (j j' : Fin 4) (q : Fin 4 → ℝ) : ℂ :=
  (1 / 48 : ℂ) * ∑ x : Idx, ((if typ x.1 x.2.1 = body j ∧ typ x.1 x.2.2 = body j' then
    hz x.2.1 x.2.2 else 0 : ℤ) : ℂ) * phase q (2 • (base x.1 x.2.2 - base x.1 x.2.1))

theorem phase_zero (q : Fin 4 → ℝ) : phase q 0 = 1 := by
  simp [phase, dotH, comp, Fin.sum_univ_four]

theorem KC_eq (j j' : Fin 4) (q : Fin 4 → ℝ) : KC j j' q = if j = j' then -(1 / 2) else 0 := by
  -- every nonzero body–body term has zero displacement
  have hD : ∀ x : Idx, ¬ (hz x.2.1 x.2.2 ≠ 0 ∧ typ x.1 x.2.1 = body j ∧ typ x.1 x.2.2 = body j' ∧
      base x.1 x.2.2 - base x.1 x.2.1 ≠ 0) := by
    have h0 : bodyD j j' = 0 := by
      fin_cases j <;> fin_cases j' <;> first
        | exact bodyD_0_0 | exact bodyD_0_1 | exact bodyD_0_2 | exact bodyD_0_3
        | exact bodyD_1_0 | exact bodyD_1_1 | exact bodyD_1_2 | exact bodyD_1_3
        | exact bodyD_2_0 | exact bodyD_2_1 | exact bodyD_2_2 | exact bodyD_2_3
        | exact bodyD_3_0 | exact bodyD_3_1 | exact bodyD_3_2 | exact bodyD_3_3
    rw [bodyD, fastSum_idx] at h0
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => by split_ifs <;> norm_num)).mp h0
    intro x hx
    have hx' := this x (Finset.mem_univ x)
    rw [ite_cond_eq_true _ _ (eq_true hx)] at hx'
    exact one_ne_zero hx'
  have hC : bodyC j j' = if j = j' then -24 else 0 := by
    fin_cases j <;> fin_cases j' <;> first
      | exact bodyC_0_0 | exact bodyC_0_1 | exact bodyC_0_2 | exact bodyC_0_3
      | exact bodyC_1_0 | exact bodyC_1_1 | exact bodyC_1_2 | exact bodyC_1_3
      | exact bodyC_2_0 | exact bodyC_2_1 | exact bodyC_2_2 | exact bodyC_2_3
      | exact bodyC_3_0 | exact bodyC_3_1 | exact bodyC_3_2 | exact bodyC_3_3
  rw [bodyC, fastSum_idx] at hC
  have hterm : ∀ x : Idx, ((if typ x.1 x.2.1 = body j ∧ typ x.1 x.2.2 = body j' then
      hz x.2.1 x.2.2 else 0 : ℤ) : ℂ) * phase q (2 • (base x.1 x.2.2 - base x.1 x.2.1)) =
      ((if typ x.1 x.2.1 = body j ∧ typ x.1 x.2.2 = body j' then hz x.2.1 x.2.2 else 0 : ℤ) : ℂ) := by
    intro x
    by_cases hc : typ x.1 x.2.1 = body j ∧ typ x.1 x.2.2 = body j'
    · by_cases hzx : hz x.2.1 x.2.2 = 0
      · simp [hc, hzx]
      · have hb : base x.1 x.2.2 - base x.1 x.2.1 = 0 := by
          by_contra hne; exact hD x ⟨hzx, hc.1, hc.2, hne⟩
        rw [hb, smul_zero, phase_zero, mul_one]
    · simp [hc]
  rw [KC, Finset.sum_congr rfl fun x _ => hterm x, ← Int.cast_sum, hC]
  split_ifs <;> norm_num

noncomputable def Am (q : Fin 4 → ℝ) : Matrix (Fin 10) (Fin 10) ℂ := fun c d => KA c d q
noncomputable def Bm (q : Fin 4 → ℝ) : Matrix (Fin 10) (Fin 4) ℂ := fun c j => KB c j q
noncomputable def Cm (q : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ := fun j j' => KC j j' q

theorem Cm_eq (q : Fin 4 → ℝ) : Cm q = (-(1 / 2) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext j j'
  simp only [Cm, KC_eq, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

/-- **Schur complement.** `Kred q = A − B C⁻¹ B†`. -/
theorem Kred_schur (q : Fin 4 → ℝ) : Kred q = Am q - Bm q * (Cm q)⁻¹ * (Bm q)ᴴ := by
  have hinv : (Cm q)⁻¹ = (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    rw [Cm_eq]
    refine Matrix.inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, Matrix.one_mul]
    norm_num
  rw [hinv]
  ext c d
  simp only [Kred, Am, Bm, Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.conjTranspose_apply, smul_eq_mul]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def]
  ring

end Entropic.ReggeGraviton
