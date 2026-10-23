import Entropic.Pass2.Conformal
import Entropic.Pass2.IBPForm

/-! Second pass, chunk 17: C11-51. With N = 1 + εφ, h = e^{2ζ}δ, ζ = −εψ − ε²ψ² (ψ = ψ_N), the density
N√h ^(3)R = (1 + εφ) e^{3ζ} R[ζ] equals ε·4Δψ + ε²(4φΔψ + 4ψΔψ + 6|∇ψ|²) up to a remainder bounded by C|ε|³
(`adm_density_expansion`); the curvature is the one computed from the metric in `Conformal`. -/

open Set

namespace Entropic.Var

/-- Polynomial remainder bound: a continuous H is bounded on [−1, 1]. -/
theorem bound_Icc {H : ℝ → ℝ} (hH : Continuous H) : ∃ K, ∀ ε, |ε| ≤ 1 → |H ε| ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (-1:ℝ)) (b := 1)).exists_bound_of_continuousOn hH.continuousOn
  exact ⟨K, fun ε hε => by simpa [Real.norm_eq_abs] using hK ε (abs_le.1 hε)⟩

/-- The scalar expansion behind C11-51. -/
theorem scalar_expansion (p q s f : ℝ) : ∃ C δ : ℝ, 0 < δ ∧ ∀ ε, |ε| ≤ δ →
    |(1 + ε * f) * Real.exp (-(ε * p) - ε ^ 2 * p ^ 2) *
        (4 * ε * q + 4 * ε ^ 2 * (2 * p * q + 2 * s) - 2 * ε ^ 2 * s * (1 + 2 * ε * p) ^ 2) -
      (ε * (4 * q) + ε ^ 2 * (4 * f * q + 4 * p * q + 6 * s))| ≤ C * |ε| ^ 3 := by
  set H1 : ℝ → ℝ := fun e => 8*e^4*f*p^4*s + 16*e^3*f*p^3*s + 8*e^3*p^4*s - 8*e^2*f*p^3*q - 6*e^2*f*p^2*s +
    16*e^2*p^3*s - 12*e*f*p^2*q - 14*e*f*p*s - 8*e*p^3*q - 6*e*p^2*s + 4*f*p*q + 6*f*s - 12*p^2*q - 14*p*s
  set H2 : ℝ → ℝ := fun e => (1 + e * f) * (p + e * p ^ 2) ^ 2 *
    (-8*e^3*p^2*s - 8*e^2*p*s + 8*e*p*q + 6*e*s + 4*q)
  obtain ⟨K1, hK1⟩ := bound_Icc (H := H1) (by fun_prop)
  obtain ⟨K2, hK2⟩ := bound_Icc (H := H2) (by fun_prop)
  set m := 1 + |p| + p ^ 2
  have hm : 0 < m := by positivity
  refine ⟨K1 + K2, min 1 (1 / m), lt_min one_pos (by positivity), fun ε hε => ?_⟩
  have hε1 : |ε| ≤ 1 := hε.trans (min_le_left _ _)
  have hεm : |ε| * m ≤ 1 := by
    have := hε.trans (min_le_right _ _); rwa [le_div_iff₀ hm] at this
  set t := -(ε * p) - ε ^ 2 * p ^ 2
  have ht : |t| ≤ 1 := by
    have h1 : |t| ≤ |ε| * |p| + |ε| ^ 2 * p ^ 2 := by
      calc |t| = |-(ε * p) + -(ε ^ 2 * p ^ 2)| := by rw [show t = -(ε * p) + -(ε ^ 2 * p ^ 2) by simp only [t]; ring]
        _ ≤ |-(ε * p)| + |-(ε ^ 2 * p ^ 2)| := abs_add_le _ _
        _ = |ε| * |p| + |ε| ^ 2 * p ^ 2 := by
          rw [abs_neg, abs_neg, abs_mul, abs_mul, abs_pow, abs_of_nonneg (sq_nonneg p)]
    have h2 : |ε| ^ 2 * p ^ 2 ≤ |ε| * p ^ 2 := by
      have : |ε| ^ 2 ≤ |ε| := by nlinarith [abs_nonneg ε]
      exact mul_le_mul_of_nonneg_right this (sq_nonneg p)
    nlinarith [abs_nonneg ε, sq_nonneg p, abs_nonneg p]
  set R := Real.exp t - 1 - t
  have hR : |R| ≤ t ^ 2 := Real.abs_exp_sub_one_sub_id_le ht
  have e1 : (1 + ε * f) * (1 + t) * (4 * ε * q + 4 * ε ^ 2 * (2 * p * q + 2 * s) - 2 * ε ^ 2 * s * (1 + 2 * ε * p) ^ 2) -
      (ε * (4 * q) + ε ^ 2 * (4 * f * q + 4 * p * q + 6 * s)) = ε ^ 3 * H1 ε := by
    simp only [H1, t]; ring
  have e2 : (1 + ε * f) * (4 * ε * q + 4 * ε ^ 2 * (2 * p * q + 2 * s) - 2 * ε ^ 2 * s * (1 + 2 * ε * p) ^ 2) * t ^ 2
      = ε ^ 3 * H2 ε := by
    simp only [H2, t]; ring
  have split : (1 + ε * f) * Real.exp t *
        (4 * ε * q + 4 * ε ^ 2 * (2 * p * q + 2 * s) - 2 * ε ^ 2 * s * (1 + 2 * ε * p) ^ 2) -
      (ε * (4 * q) + ε ^ 2 * (4 * f * q + 4 * p * q + 6 * s)) =
      ε ^ 3 * H1 ε + (1 + ε * f) *
        (4 * ε * q + 4 * ε ^ 2 * (2 * p * q + 2 * s) - 2 * ε ^ 2 * s * (1 + 2 * ε * p) ^ 2) * R := by
    rw [← e1]; simp only [R]; ring
  rw [split]
  have hPR : |(1 + ε * f) * (4 * ε * q + 4 * ε ^ 2 * (2 * p * q + 2 * s) - 2 * ε ^ 2 * s * (1 + 2 * ε * p) ^ 2) * R|
      ≤ |ε| ^ 3 * K2 := by
    rw [abs_mul]
    calc _ ≤ |(1 + ε * f) * (4 * ε * q + 4 * ε ^ 2 * (2 * p * q + 2 * s) - 2 * ε ^ 2 * s * (1 + 2 * ε * p) ^ 2)| *
          t ^ 2 := mul_le_mul_of_nonneg_left hR (abs_nonneg _)
      _ = |(1 + ε * f) * (4 * ε * q + 4 * ε ^ 2 * (2 * p * q + 2 * s) - 2 * ε ^ 2 * s * (1 + 2 * ε * p) ^ 2) *
          t ^ 2| := by rw [abs_mul _ (t ^ 2), abs_of_nonneg (sq_nonneg t)]
      _ = |ε| ^ 3 * |H2 ε| := by rw [e2, abs_mul, abs_pow]
      _ ≤ |ε| ^ 3 * K2 := mul_le_mul_of_nonneg_left (hK2 ε hε1) (by positivity)
  calc _ ≤ |ε ^ 3 * H1 ε| + |(1 + ε * f) *
        (4 * ε * q + 4 * ε ^ 2 * (2 * p * q + 2 * s) - 2 * ε ^ 2 * s * (1 + 2 * ε * p) ^ 2) * R| := abs_add_le _ _
    _ ≤ |ε| ^ 3 * K1 + |ε| ^ 3 * K2 := by
      gcongr
      · rw [abs_mul, abs_pow]; exact mul_le_mul_of_nonneg_left (hK1 ε hε1) (by positivity)
    _ = (K1 + K2) * |ε| ^ 3 := by ring

/-- The conformal factor ζ_ε = −εψ − ε²ψ². -/
noncomputable def zeta (ψ : E 3 → ℝ) (ε : ℝ) (y : E 3) : ℝ := -ε * ψ y + -(ε ^ 2) * (ψ y * ψ y)

theorem pd_zeta {ψ : E 3 → ℝ} (hψ : Differentiable ℝ ψ) (ε : ℝ) (i : Fin 3) (y : E 3) :
    pd (zeta ψ ε) i y = -ε * pd ψ i y + -(ε ^ 2) * (2 * ψ y * pd ψ i y) := by
  unfold zeta
  rw [pd_add (f := fun y => -ε * ψ y) (g := fun y => -(ε ^ 2) * (ψ y * ψ y)) (hψ.const_mul _)
      ((hψ.mul hψ).const_mul _), pd_const_mul hψ, pd_const_mul (f := fun y => ψ y * ψ y) (hψ.mul hψ),
    pd_mul hψ hψ]
  ring

theorem lap_zeta {ψ : E 3 → ℝ} (hψ : ContDiff ℝ 2 ψ) (ε : ℝ) (x : E 3) :
    lap (zeta ψ ε) x = -ε * lap ψ x + -(ε ^ 2) * (2 * ψ x * lap ψ x + 2 * ∑ i, pd ψ i x ^ 2) := by
  have hd := diff_of_c1 (c1_of_c2 hψ)
  have hp : ∀ i, Differentiable ℝ (pd ψ i) := fun i => diff_of_c1 (pd_c1 hψ i)
  have e : ∀ i, pd (zeta ψ ε) i = fun y => -ε * pd ψ i y + -(ε ^ 2) * (2 * (ψ y * pd ψ i y)) := fun i =>
    funext fun y => by rw [pd_zeta hd]; ring
  simp only [lap, dvg, e]
  have : ∀ i, pd (fun y => -ε * pd ψ i y + -(ε ^ 2) * (2 * (ψ y * pd ψ i y))) i x =
      -ε * pd (pd ψ i) i x + -(ε ^ 2) * (2 * (pd ψ i x * pd ψ i x + ψ x * pd (pd ψ i) i x)) := by
    intro i
    rw [pd_add (f := fun y => -ε * pd ψ i y) (g := fun y => -(ε ^ 2) * (2 * (ψ y * pd ψ i y)))
        ((hp i).const_mul _) (((hd.mul (hp i)).const_mul 2).const_mul _), pd_const_mul (hp i),
      pd_const_mul (f := fun y => 2 * (ψ y * pd ψ i y)) ((hd.mul (hp i)).const_mul 2),
      pd_const_mul (f := fun y => ψ y * pd ψ i y) (hd.mul (hp i)), pd_mul hd (hp i)]
  rw [Finset.sum_congr rfl (fun i _ => this i)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sq]
  ring

/-- C11-51: N√h ^(3)R = ε·4Δψ + ε²(4φΔψ + 4ψΔψ + 6|∇ψ|²) + O(ε³), with N = 1 + εφ and ζ = −εψ − ε²ψ². -/
theorem adm_density_expansion {φ ψ : E 3 → ℝ} (hψ : ContDiff ℝ 2 ψ) (x : E 3) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ ε, |ε| ≤ δ →
      |(1 + ε * φ x) * Real.exp (3 * zeta ψ ε x) * scal (zeta ψ ε) x -
        (ε * (4 * lap ψ x) + ε ^ 2 * (4 * φ x * lap ψ x + 4 * ψ x * lap ψ x + 6 * ∑ i, pd ψ i x ^ 2))| ≤
        C * |ε| ^ 3 := by
  have hd := diff_of_c1 (c1_of_c2 hψ)
  have hz : ∀ ε, ContDiff ℝ 2 (zeta ψ ε) := fun ε => by
    unfold zeta; exact (contDiff_const.mul hψ).add (contDiff_const.mul (hψ.mul hψ))
  obtain ⟨C, δ, hδ, hb⟩ := scalar_expansion (ψ x) (lap ψ x) (∑ i, pd ψ i x ^ 2) (φ x)
  refine ⟨C, δ, hδ, fun ε hε => ?_⟩
  have key : (1 + ε * φ x) * Real.exp (3 * zeta ψ ε x) * scal (zeta ψ ε) x =
      (1 + ε * φ x) * Real.exp (-(ε * ψ x) - ε ^ 2 * ψ x ^ 2) *
        (4 * ε * lap ψ x + 4 * ε ^ 2 * (2 * ψ x * lap ψ x + 2 * ∑ i, pd ψ i x ^ 2) -
          2 * ε ^ 2 * (∑ i, pd ψ i x ^ 2) * (1 + 2 * ε * ψ x) ^ 2) := by
    rw [conformal_scalar_curvature (hz ε), lap_zeta hψ]
    simp only [pd_zeta hd]
    have ex : Real.exp (3 * zeta ψ ε x) * Real.exp (-2 * zeta ψ ε x) = Real.exp (-(ε * ψ x) - ε ^ 2 * ψ x ^ 2) := by
      rw [← Real.exp_add]; congr 1; simp only [zeta]; ring
    have hs : ∑ i, (-ε * pd ψ i x + -(ε ^ 2) * (2 * ψ x * pd ψ i x)) ^ 2 =
        ε ^ 2 * (1 + 2 * ε * ψ x) ^ 2 * ∑ i, pd ψ i x ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hs]
    calc _ = (1 + ε * φ x) * (Real.exp (3 * zeta ψ ε x) * Real.exp (-2 * zeta ψ ε x)) *
          (-4 * (-ε * lap ψ x + -ε ^ 2 * (2 * ψ x * lap ψ x + 2 * ∑ i, pd ψ i x ^ 2)) -
            2 * (ε ^ 2 * (1 + 2 * ε * ψ x) ^ 2 * ∑ i, pd ψ i x ^ 2)) := by ring
      _ = _ := by rw [ex]; ring
  rw [key]
  have := hb ε hε
  convert this using 2 <;> ring

open MeasureTheory in
/-- ∫ ∂ᵢ g = 0 for a C¹ compactly supported g. -/
theorem integral_pd_eq_zero {n : ℕ} {g : E n → ℝ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (i : Fin n) :
    ∫ x, pd g i x = 0 := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := fun _ : E n => (1:ℝ))
    (g := g) (v := ev i) (by simp) (by simp only [one_mul]; exact integrable_of_cs (pd_continuous hg i) (pd_hasCompactSupport hgc i))
    (by simpa using integrable_of_cs hg.continuous hgc) (fun x _ => differentiableAt_const _)
    (fun x _ => (diff_of_c1 hg) x)
  simpa [pd] using h

open MeasureTheory in
/-- ∫ div V = 0 for C¹ compactly supported components. -/
theorem integral_dvg_eq_zero {n : ℕ} {V : Fin n → E n → ℝ} (hV : ∀ i, ContDiff ℝ 1 (V i))
    (hc : ∀ i, HasCompactSupport (V i)) : ∫ x, dvg V x = 0 := by
  unfold dvg
  rw [integral_finsetSum _ fun i _ => integrable_of_cs (pd_continuous (hV i) i) (pd_hasCompactSupport (hc i) i)]
  exact Finset.sum_eq_zero fun i _ => integral_pd_eq_zero (hV i) (hc i) i

open MeasureTheory in
/-- C01-44 (integrated form, compactly supported perturbations): the linear term ∫ 4Δψ of N√h ^(3)R vanishes
and the quadratic term integrates to ∫ 2(|∇ψ|² − 2∇φ·∇ψ); with φ = Φ/c², ψ = Ψ/c² and the prefactor
c⁴/(16πG) this is ∫ (|∇Ψ|² − 2∇Φ·∇Ψ)/(8πG), which with I_matter^(1) = −∫ρΦ gives I^(2) of `Var.I2`. -/
theorem adm_reduction {φ ψ : E 3 → ℝ} (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ x, 4 * lap ψ x = 0 ∧
      ∫ x, (4 * φ x * lap ψ x + 4 * ψ x * lap ψ x + 6 * ∑ i, pd ψ i x ^ 2) =
        ∫ x, 2 * (∑ i, pd ψ i x ^ 2 - 2 * ∑ i, pd φ i x * pd ψ i x) := by
  have hp1 : ∀ i, ContDiff ℝ 1 (pd ψ i) := pd_c1 hψ
  have hpc : ∀ i, HasCompactSupport (pd ψ i) := pd_hasCompactSupport hψc
  constructor
  · rw [integral_const_mul, show (∫ x, lap ψ x) = 0 from integral_dvg_eq_zero hp1 hpc, mul_zero]
  · have hV : ∀ i, ContDiff ℝ 1 fun y => 4 * (φ y * pd ψ i y) + 4 * (ψ y * pd ψ i y) := fun i =>
      (contDiff_const.mul ((c1_of_c2 hφ).mul (hp1 i))).add (contDiff_const.mul ((c1_of_c2 hψ).mul (hp1 i)))
    have hVc : ∀ i, HasCompactSupport fun y => 4 * (φ y * pd ψ i y) + 4 * (ψ y * pd ψ i y) := fun i =>
      (((hpc i).mul_left).mul_left).add (((hpc i).mul_left).mul_left)
    have hcont : Continuous fun x => 2 * (∑ i, pd ψ i x ^ 2 - 2 * ∑ i, pd φ i x * pd ψ i x) :=
      continuous_const.mul ((continuous_finsetSum _ fun i _ => (pd_continuous (c1_of_c2 hψ) i).pow 2).sub
        (continuous_const.mul (continuous_finsetSum _ fun i _ =>
          (pd_continuous (c1_of_c2 hφ) i).mul (pd_continuous (c1_of_c2 hψ) i))))
    have hI1 : Integrable fun x => 2 * (∑ i, pd ψ i x ^ 2 - 2 * ∑ i, pd φ i x * pd ψ i x) :=
      integrable_of_cs hcont (HasCompactSupport.intro hψc.isCompact fun x hx => by simp [pd_eq_zero hx])
    have hI2 : Integrable fun x => dvg (fun i y => 4 * (φ y * pd ψ i y) + 4 * (ψ y * pd ψ i y)) x := by
      unfold dvg
      exact integrable_finsetSum _ fun i _ => integrable_of_cs (pd_continuous (hV i) i) (pd_hasCompactSupport (hVc i) i)
    have hpt : (fun x => 4 * φ x * lap ψ x + 4 * ψ x * lap ψ x + 6 * ∑ i, pd ψ i x ^ 2) = fun x =>
        2 * (∑ i, pd ψ i x ^ 2 - 2 * ∑ i, pd φ i x * pd ψ i x) +
          dvg (fun i y => 4 * (φ y * pd ψ i y) + 4 * (ψ y * pd ψ i y)) x :=
      funext fun x => quad_form_ibp hφ hψ x
    rw [hpt, integral_add hI1 hI2, integral_dvg_eq_zero hV hVc, add_zero]


end Entropic.Var
