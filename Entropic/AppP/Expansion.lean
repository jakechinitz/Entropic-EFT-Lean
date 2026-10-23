import Entropic.AppP.Records
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Appendix P, information under fixed-marginal distortion: marginals and the second-order
expansion of mutual information with an explicit cubic remainder (C14-29), exact monotonicity
and convexity of I(d) (C14-30), monotonicity of total history information (C14-31), the
Bhattacharyya/Fubini-Study expansion (C14-32) and I = 2d_FS² + O(·) (C14-33). -/

noncomputable section
namespace Entropic.AppP.Exp
open Real

/-- |(1 + u) ln(1 + u) − u − u²/2| ≤ 4|u|³ for |u| ≤ 1/2. -/
theorem xlogx_cubic {u : ℝ} (hu : |u| ≤ 1/2) :
    |(1 + u) * Real.log (1 + u) - u - u ^ 2 / 2| ≤ 4 * |u| ^ 3 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -u) (by rw [abs_neg]; linarith) 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at h
  norm_num at h
  set r := Real.log (1 + u) - u + u ^ 2 / 2
  have hr : |r| ≤ 2 * |u| ^ 3 := by
    have e : -u + u ^ 2 / 2 + Real.log (1 + u) = r := by simp only [r]; ring
    rw [e] at h
    calc |r| ≤ |u| ^ 3 / (1 - |u|) := h
      _ ≤ 2 * |u| ^ 3 := by
        rw [div_le_iff₀ (by linarith)]; nlinarith [pow_nonneg (abs_nonneg u) 3]
  have e2 : (1 + u) * Real.log (1 + u) - u - u ^ 2 / 2 = -u ^ 3 / 2 + (1 + u) * r := by
    simp only [r]; ring
  rw [e2]
  calc |-u ^ 3 / 2 + (1 + u) * r| ≤ |u| ^ 3 / 2 + (3/2) * (2 * |u| ^ 3) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_div, abs_neg, abs_pow]; norm_num
        · rw [abs_mul]
          apply mul_le_mul _ hr (abs_nonneg _) (by norm_num)
          rw [abs_le]; constructor <;> linarith [abs_le.mp hu]
    _ ≤ 4 * |u| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg u) 3]

section Fam
variable {ι : Type*} [Fintype ι] (w e : ι → ℝ)

/-- I(d) = Σ w(1 + dε) ln(1 + dε) (the mutual information of p_ij = p_ip_j(1 + dε)). -/
def Ifam (d : ℝ) : ℝ := ∑ k, w k * ((1 + d * e k) * Real.log (1 + d * e k))

/-- C14-29: with Σwε = 0 (fixed marginals) and |dε| ≤ 1/2, |I(d) − (d²/2)Σwε²| ≤ 4Σw|dε|³. -/
theorem second_order (hw : ∀ k, 0 ≤ w k) (h0 : ∑ k, w k * e k = 0) (d : ℝ) (hd : ∀ k, |d * e k| ≤ 1/2) :
    |Ifam w e d - d ^ 2 / 2 * ∑ k, w k * e k ^ 2| ≤ 4 * ∑ k, w k * |d * e k| ^ 3 := by
  have e1 : Ifam w e d - d ^ 2 / 2 * ∑ k, w k * e k ^ 2 =
      ∑ k, w k * ((1 + d * e k) * Real.log (1 + d * e k) - d * e k - (d * e k) ^ 2 / 2) +
        d * ∑ k, w k * e k := by
    unfold Ifam
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [e1, h0, mul_zero, add_zero, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
  rw [abs_mul, abs_of_nonneg (hw k)]
  have := xlogx_cubic (hd k)
  nlinarith [hw k]

/-- C14-29: the joint p_ij = p_ip_j(1 + Dε) has marginals p_i, p_j under the zero-mean conditions. -/
theorem marginals {X Y : Type*} [Fintype X] [Fintype Y] (px : X → ℝ) (py : Y → ℝ) (ε : X → Y → ℝ)
    (hpx : ∑ x, px x = 1) (hpy : ∑ y, py y = 1) (hx : ∀ x, ∑ y, py y * ε x y = 0)
    (hy : ∀ y, ∑ x, px x * ε x y = 0) (D : ℝ) :
    (∀ x, ∑ y, px x * py y * (1 + D * ε x y) = px x) ∧ (∀ y, ∑ x, px x * py y * (1 + D * ε x y) = py y) := by
  constructor
  · intro x
    have : ∀ y, px x * py y * (1 + D * ε x y) = px x * py y + px x * D * (py y * ε x y) := fun y => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hpy, hx x]; ring
  · intro y
    have : ∀ x, px x * py y * (1 + D * ε x y) = py y * px x + py y * D * (px x * ε x y) := fun x => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hpx, hy y]; ring

/-- C14-30: I′(d) = Σwε ln(1 + dε) ≥ 0 for d ≥ 0 and I″(d) = Σwε²/(1 + dε) ≥ 0. -/
theorem first_derivative (h0 : ∑ k, w k * e k = 0) (d : ℝ) (hpos : ∀ k, 0 < 1 + d * e k) :
    HasDerivAt (Ifam w e) (∑ k, w k * e k * Real.log (1 + d * e k)) d := by
  have hk : ∀ k, HasDerivAt (fun d => w k * ((1 + d * e k) * Real.log (1 + d * e k)))
      (w k * e k * Real.log (1 + d * e k) + w k * e k) d := by
    intro k
    have h1 : HasDerivAt (fun d => 1 + d * e k) (e k) d := by
      simpa using ((hasDerivAt_id d).mul_const (e k)).const_add 1
    have h2 := h1.mul (h1.log (hpos k).ne')
    convert h2.const_mul (w k) using 1
    rw [mul_div_cancel₀ _ (hpos k).ne']; ring
  have := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => hk k)
  unfold Ifam
  convert this using 1
  rw [Finset.sum_add_distrib, h0, add_zero]

theorem first_derivative_nonneg (hw : ∀ k, 0 ≤ w k) (d : ℝ) (hd : 0 ≤ d) (hpos : ∀ k, 0 < 1 + d * e k) :
    0 ≤ ∑ k, w k * e k * Real.log (1 + d * e k) := by
  apply Finset.sum_nonneg; intro k _
  rcases le_total 0 (e k) with h | h
  · have : 0 ≤ Real.log (1 + d * e k) := Real.log_nonneg (by nlinarith)
    exact mul_nonneg (mul_nonneg (hw k) h) this
  · have : Real.log (1 + d * e k) ≤ 0 := Real.log_nonpos (hpos k).le (by nlinarith)
    have := mul_nonneg_of_nonpos_of_nonpos h this
    nlinarith [hw k]

theorem second_derivative (hw : ∀ k, 0 ≤ w k) (d : ℝ) (hpos : ∀ k, 0 < 1 + d * e k) :
    HasDerivAt (fun d => ∑ k, w k * e k * Real.log (1 + d * e k)) (∑ k, w k * e k ^ 2 / (1 + d * e k)) d ∧
      0 ≤ ∑ k, w k * e k ^ 2 / (1 + d * e k) := by
  refine ⟨?_, Finset.sum_nonneg (fun k _ => div_nonneg (mul_nonneg (hw k) (sq_nonneg _)) (hpos k).le)⟩
  have hk : ∀ k, HasDerivAt (fun d => w k * e k * Real.log (1 + d * e k)) (w k * e k ^ 2 / (1 + d * e k)) d := by
    intro k
    have h1 : HasDerivAt (fun d => 1 + d * e k) (e k) d := by
      simpa using ((hasDerivAt_id d).mul_const (e k)).const_add 1
    convert (h1.log (hpos k).ne').const_mul (w k * e k) using 1
    field_simp [(hpos k).ne']
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => hk k)
end Fam

/-- C14-31: I_H(a) = Σ_pairs I_ij(D₊(a)) with I_ij′ ≥ 0 and D₊′ ≥ 0 has dI_H/da = Σ I_ij′(D₊)D₊′ ≥ 0. -/
theorem total_history_monotone {P : Type*} [Fintype P] (I I' : P → ℝ → ℝ) (Dp : ℝ → ℝ) {Dp' a : ℝ}
    (hD : HasDerivAt Dp Dp' a) (hD' : 0 ≤ Dp') (hI : ∀ q, HasDerivAt (I q) (I' q (Dp a)) (Dp a))
    (hI' : ∀ q, 0 ≤ I' q (Dp a)) :
    HasDerivAt (fun a => ∑ q, I q (Dp a)) (∑ q, I' q (Dp a) * Dp') a ∧ 0 ≤ ∑ q, I' q (Dp a) * Dp' := by
  refine ⟨HasDerivAt.fun_sum (u := Finset.univ) (fun q _ => (hI q).comp a hD),
    Finset.sum_nonneg (fun q _ => mul_nonneg (hI' q) hD')⟩

/-! ### C14-32, C14-33: Bhattacharyya coefficient and Fubini–Study distance -/

/-- |√(1 + u) − (1 + u/2 − u²/8)| ≤ |u|³/10 for |u| ≤ 1/2. -/
theorem sqrt_cubic {u : ℝ} (hu : |u| ≤ 1/2) :
    |Real.sqrt (1 + u) - (1 + u / 2 - u ^ 2 / 8)| ≤ |u| ^ 3 / 10 := by
  obtain ⟨hu1, hu2⟩ := abs_le.mp hu
  set s := Real.sqrt (1 + u)
  set q := 1 + u / 2 - u ^ 2 / 8
  have hs2 : s ^ 2 = 1 + u := Real.sq_sqrt (by linarith)
  have hs : 0.7 ≤ s := by
    rw [show (0.7:ℝ) = Real.sqrt (0.49) by
      rw [show (0.49:ℝ) = 0.7 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hq : 0.7 ≤ q := by simp only [q]; nlinarith
  have hdiff : s - q = (u ^ 3 / 8 - u ^ 4 / 64) / (s + q) := by
    rw [eq_div_iff (by linarith)]; simp only [q]; nlinarith [hs2]
  rw [hdiff, abs_div, abs_of_pos (by linarith : (0:ℝ) < s + q), div_le_div_iff₀ (by linarith) (by norm_num)]
  have hua : |u| ≤ 1/2 := hu
  have : |u ^ 3 / 8 - u ^ 4 / 64| ≤ |u| ^ 3 / 8 * (1 + 1/16) := by
    rw [show u ^ 3 / 8 - u ^ 4 / 64 = u ^ 3 / 8 * (1 - u / 8) by ring, abs_mul, abs_div, abs_pow]
    have : |1 - u / 8| ≤ 1 + 1/16 := by rw [abs_le]; constructor <;> linarith
    have h3 : 0 ≤ |u| ^ 3 / 8 := by positivity
    norm_num at this ⊢; nlinarith
  nlinarith [pow_nonneg (abs_nonneg u) 3]

section BC
variable {ι : Type*} [Fintype ι] (w e : ι → ℝ)

/-- C14-32 (Bhattacharyya coefficient): with Σw = 1, Σwε = 0 and |Dε| ≤ 1/2,
|Σw√(1 + Dε) − (1 − (D²/8)Σwε²)| ≤ Σw|Dε|³/10. -/
theorem bhattacharyya (hw : ∀ k, 0 ≤ w k) (h1 : ∑ k, w k = 1) (h0 : ∑ k, w k * e k = 0) (D : ℝ)
    (hd : ∀ k, |D * e k| ≤ 1/2) :
    |∑ k, w k * Real.sqrt (1 + D * e k) - (1 - D ^ 2 / 8 * ∑ k, w k * e k ^ 2)| ≤
      ∑ k, w k * |D * e k| ^ 3 / 10 := by
  have e0 : ∑ k, w k * (Real.sqrt (1 + D * e k) - (1 + D * e k / 2 - (D * e k) ^ 2 / 8)) =
      ∑ k, w k * Real.sqrt (1 + D * e k) - ∑ k, w k - D / 2 * ∑ k, w k * e k +
        D ^ 2 / 8 * ∑ k, w k * e k ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have e1 : ∑ k, w k * Real.sqrt (1 + D * e k) - (1 - D ^ 2 / 8 * ∑ k, w k * e k ^ 2) =
      ∑ k, w k * (Real.sqrt (1 + D * e k) - (1 + D * e k / 2 - (D * e k) ^ 2 / 8)) := by
    rw [e0, h0, h1]; ring
  rw [e1]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
  rw [abs_mul, abs_of_nonneg (hw k)]
  calc w k * |Real.sqrt (1 + D * e k) - (1 + D * e k / 2 - (D * e k) ^ 2 / 8)|
      ≤ w k * (|D * e k| ^ 3 / 10) := mul_le_mul_of_nonneg_left (sqrt_cubic (hd k)) (hw k)
    _ = w k * |D * e k| ^ 3 / 10 := by ring

/-- θ² − 2(1 − cos θ) ∈ [0, (5/48)θ⁴] for |θ| ≤ 1, and θ² ≤ (π²/2)(1 − cos θ) for |θ| ≤ π. -/
theorem angle_vs_chord {θ : ℝ} (h1 : |θ| ≤ 1) :
    0 ≤ θ ^ 2 - 2 * (1 - Real.cos θ) ∧ θ ^ 2 - 2 * (1 - Real.cos θ) ≤ 5 / 48 * θ ^ 4 := by
  have hb := Real.cos_bound h1
  have hl := Real.one_sub_sq_div_two_le_cos (x := θ)
  rw [abs_le] at hb
  have : |θ| ^ 4 = θ ^ 4 := by rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
  rw [this] at hb
  constructor <;> nlinarith [hb.1, hb.2]

theorem angle_sq_le_chord {θ : ℝ} (h : |θ| ≤ π) : θ ^ 2 ≤ π ^ 2 / 2 * (1 - Real.cos θ) := by
  have := Real.cos_le_one_sub_mul_cos_sq h
  have hp : 0 < π ^ 2 := by positivity
  have : 2 / π ^ 2 * θ ^ 2 ≤ 1 - Real.cos θ := by linarith
  calc θ ^ 2 = π ^ 2 / 2 * (2 / π ^ 2 * θ ^ 2) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)

/-- C14-32: d_FS = arccos c with 1 − c = (D²/8)S − R satisfies
|d_FS² − (D²/4)S| ≤ 2|R| + (5/48)(π²/2)²(1 − c)² (when d_FS ≤ 1). -/
theorem fubini_study_expansion {c S R D : ℝ} (hc0 : -1 ≤ c) (hc1 : c ≤ 1) (hc : 1 - c = D ^ 2 / 8 * S - R)
    (hθ : Real.arccos c ≤ 1) :
    |Real.arccos c ^ 2 - D ^ 2 / 4 * S| ≤ 2 * |R| + 5 / 48 * (π ^ 2 / 2) ^ 2 * (1 - c) ^ 2 := by
  set θ := Real.arccos c
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg c
  have hcos : Real.cos θ = c := Real.cos_arccos hc0 hc1
  obtain ⟨a1, a2⟩ := angle_vs_chord (θ := θ) (by rw [abs_of_nonneg hθ0]; exact hθ)
  have hsq := angle_sq_le_chord (θ := θ) (by rw [abs_of_nonneg hθ0]; exact Real.arccos_le_pi c)
  rw [hcos] at a1 a2 hsq
  have h4 : θ ^ 4 ≤ (π ^ 2 / 2) ^ 2 * (1 - c) ^ 2 := by
    rw [show θ ^ 4 = (θ ^ 2) ^ 2 by ring, ← mul_pow]
    exact pow_le_pow_left₀ (sq_nonneg θ) hsq 2
  have e : θ ^ 2 - D ^ 2 / 4 * S = (θ ^ 2 - 2 * (1 - c)) - 2 * R := by rw [hc]; ring
  rw [e]
  calc |(θ ^ 2 - 2 * (1 - c)) - 2 * R| ≤ |θ ^ 2 - 2 * (1 - c)| + |2 * R| := abs_sub _ _
    _ ≤ 5 / 48 * ((π ^ 2 / 2) ^ 2 * (1 - c) ^ 2) + 2 * |R| := by
        rw [abs_of_nonneg a1, abs_mul, abs_two]; nlinarith
    _ = _ := by ring

/-- C14-33: |I − 2d²| ≤ |I − (D²/2)S| + 2|d² − (D²/4)S|, so I = 2d_FS² up to the cubic remainders. -/
theorem info_twice_distance (I d2 D S : ℝ) :
    |I - 2 * d2| ≤ |I - D ^ 2 / 2 * S| + 2 * |d2 - D ^ 2 / 4 * S| := by
  have e : I - 2 * d2 = (I - D ^ 2 / 2 * S) - 2 * (d2 - D ^ 2 / 4 * S) := by ring
  rw [e]
  calc _ ≤ |I - D ^ 2 / 2 * S| + |2 * (d2 - D ^ 2 / 4 * S)| := abs_sub _ _
    _ = _ := by rw [abs_mul, abs_two]
end BC

end Entropic.AppP.Exp
