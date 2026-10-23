import Entropic.Pass2.Fields
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Second pass, chunk 17: C11-50. For the conformally flat 3-metric h_ij = e^{2ζ} δ_ij on ℝ³ the
Levi-Civita symbols computed from h, Γ^k_ij = ½ h^{kl}(∂_i h_jl + ∂_j h_il − ∂_l h_ij), are
δ^k_i ∂_jζ + δ^k_j ∂_iζ − δ_ij ∂_kζ (`christoffel_eq`), and the scalar curvature
R = h^{ij}(∂_k Γ^k_ij − ∂_j Γ^k_ik + Γ^k_kl Γ^l_ij − Γ^k_jl Γ^l_ik) equals e^{−2ζ}(−4Δζ − 2|∇ζ|²)
(`conformal_scalar_curvature`), with Δ and ∇ the flat operators. -/

open scoped ContDiff

namespace Entropic.Var

/-- Kronecker delta. -/
def kd (i j : Fin 3) : ℝ := if i = j then 1 else 0

/-- The metric e^{2ζ} δ and its inverse e^{−2ζ} δ. -/
noncomputable def hm (ζ : E 3 → ℝ) (i j : Fin 3) (x : E 3) : ℝ := Real.exp (2 * ζ x) * kd i j
noncomputable def hinv (ζ : E 3 → ℝ) (i j : Fin 3) (x : E 3) : ℝ := Real.exp (-2 * ζ x) * kd i j

theorem hinv_hm (ζ : E 3 → ℝ) (x : E 3) (i k : Fin 3) :
    ∑ l, hinv ζ i l x * hm ζ l k x = kd i k := by
  simp only [hinv, hm, kd, Fin.sum_univ_three]
  have : Real.exp (-(2 * ζ x)) * Real.exp (2 * ζ x) = 1 := by rw [← Real.exp_add]; simp
  fin_cases i <;> fin_cases k <;> simp <;> linear_combination this

/-- Christoffel symbols of the second kind computed from the metric. -/
noncomputable def chr (ζ : E 3 → ℝ) (k i j : Fin 3) (x : E 3) : ℝ :=
  (1 / 2) * ∑ l, hinv ζ k l x * (pd (hm ζ j l) i x + pd (hm ζ i l) j x - pd (hm ζ i j) l x)

theorem pd_hm {ζ : E 3 → ℝ} (hζ : Differentiable ℝ ζ) (i j l : Fin 3) (x : E 3) :
    pd (hm ζ i j) l x = kd i j * (2 * Real.exp (2 * ζ x) * pd ζ l x) := by
  have h : HasFDerivAt (fun y => Real.exp (2 * ζ y) * kd i j)
      (kd i j • (Real.exp (2 * ζ x) • ((2:ℝ) • fderiv ℝ ζ x))) x :=
    (((hζ x).hasFDerivAt.const_mul (2:ℝ)).exp).mul_const (kd i j)
  unfold pd hm
  rw [h.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]; ring

theorem christoffel_eq {ζ : E 3 → ℝ} (hζ : Differentiable ℝ ζ) (k i j : Fin 3) (x : E 3) :
    chr ζ k i j x = kd k i * pd ζ j x + kd k j * pd ζ i x - kd i j * pd ζ k x := by
  simp only [chr, pd_hm hζ, hinv, Fin.sum_univ_three]
  have e : Real.exp (-(2 * ζ x)) * Real.exp (2 * ζ x) = 1 := by rw [← Real.exp_add]; simp
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp [kd] <;> linear_combination (pd ζ _ x) * e

/-- Ricci tensor R_ij = ∂_k Γ^k_ij − ∂_j Γ^k_ik + Γ^k_kl Γ^l_ij − Γ^k_jl Γ^l_ik. -/
noncomputable def ric (ζ : E 3 → ℝ) (i j : Fin 3) (x : E 3) : ℝ :=
  ∑ k, pd (chr ζ k i j) k x - ∑ k, pd (chr ζ k i k) j x +
    ∑ k, ∑ l, (chr ζ k k l x * chr ζ l i j x - chr ζ k j l x * chr ζ l i k x)

/-- Scalar curvature R = h^{ij} R_ij. -/
noncomputable def scal (ζ : E 3 → ℝ) (x : E 3) : ℝ := ∑ i, ∑ j, hinv ζ i j x * ric ζ i j x

theorem pd_comm {ζ : E 3 → ℝ} (hζ : ContDiff ℝ 2 ζ) (i j : Fin 3) (x : E 3) :
    pd (pd ζ j) i x = pd (pd ζ i) j x := by
  have hd1 : Differentiable ℝ (fderiv ℝ ζ) :=
    (hζ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have key : ∀ a b : Fin 3, pd (pd ζ a) b x = fderiv ℝ (fderiv ℝ ζ) x (ev b) (ev a) := by
    intro a b
    unfold pd
    rw [fderiv_clm_apply (hd1 x) (differentiableAt_const _)]
    simp
  rw [key, key]
  exact (ContDiffAt.isSymmSndFDerivAt (hζ.contDiffAt (x := x)) (by simp)) (ev i) (ev j)

/-- C11-50: R = e^{−2ζ}(−4Δζ − 2|∇ζ|²) for h = e^{2ζ}δ on ℝ³. -/
theorem conformal_scalar_curvature {ζ : E 3 → ℝ} (hζ : ContDiff ℝ 2 ζ) (x : E 3) :
    scal ζ x = Real.exp (-2 * ζ x) * (-4 * lap ζ x - 2 * ∑ i, pd ζ i x ^ 2) := by
  have hd : Differentiable ℝ ζ := diff_of_c1 (c1_of_c2 hζ)
  have hp : ∀ a, Differentiable ℝ (pd ζ a) := fun a => diff_of_c1 (pd_c1 hζ a)
  have hchr : ∀ k i j, chr ζ k i j = fun y => kd k i * pd ζ j y + kd k j * pd ζ i y - kd i j * pd ζ k y :=
    fun k i j => funext (christoffel_eq hd k i j)
  have hpd : ∀ k i j m, pd (chr ζ k i j) m x =
      kd k i * pd (pd ζ j) m x + kd k j * pd (pd ζ i) m x - kd i j * pd (pd ζ k) m x := by
    intro k i j m
    rw [hchr, pd_sub (f := fun y => kd k i * pd ζ j y + kd k j * pd ζ i y) (g := fun y => kd i j * pd ζ k y)
        (((hp j).const_mul _).add ((hp i).const_mul _)) ((hp k).const_mul _),
      pd_add ((hp j).const_mul _) ((hp i).const_mul _), pd_const_mul (hp j), pd_const_mul (hp i),
      pd_const_mul (hp k)]
  simp only [scal, ric, hpd, christoffel_eq hd, hinv, lap, dvg, Fin.sum_univ_three]
  simp only [kd, Fin.isValue]
  norm_num
  ring

end Entropic.Var
