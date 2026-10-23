import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! Appendix H.13–H.15: two-source covariance, metric codifferential and Dirac–Kähler operator,
orbital frequency, coarse symbol, cochain counts, microscopic metric, projected bridge arithmetic
(ledger C09-36, -75, -81, -82, -83, -85, -86, -91). -/

noncomputable section
namespace Entropic.AppH11
open Matrix
open scoped ComplexOrder

/-! ### Mixed log-derivative equals covariance (C09-75) -/

section Cov
variable {ι : Type*} (S : Finset ι) (p a b : ι → ℝ)

def Zs (m1 m2 : ℝ) : ℝ := ∑ T ∈ S, p T * Real.exp (-m1 * a T - m2 * b T)
def mom (f : ι → ℝ) (m1 m2 : ℝ) : ℝ := ∑ T ∈ S, p T * f T * Real.exp (-m1 * a T - m2 * b T)

theorem hasDerivAt_Zs_m2 (m1 m2 : ℝ) :
    HasDerivAt (fun x => Zs S p a b m1 x) (-mom S p a b b m1 m2) m2 := by
  unfold Zs mom
  rw [← Finset.sum_neg_distrib]
  apply HasDerivAt.fun_sum
  intro T _
  have h := ((((hasDerivAt_id' m2).const_mul (b T)).const_sub (-m1 * a T)).exp).const_mul (p T)
  convert h using 1
  · funext x; ring_nf
  · ring

theorem hasDerivAt_mom_m1 (f : ι → ℝ) (m1 m2 : ℝ) :
    HasDerivAt (fun x => mom S p a b f x m2) (-mom S p a b (fun T => f T * a T) m1 m2) m1 := by
  unfold mom
  rw [← Finset.sum_neg_distrib]
  apply HasDerivAt.fun_sum
  intro T _
  have h := ((((hasDerivAt_id' m1).const_mul (-(a T))).sub_const (m2 * b T)).exp).const_mul (p T * f T)
  convert h using 1
  · funext x; ring_nf
  · ring_nf

theorem hasDerivAt_Zs_m1 (m1 m2 : ℝ) :
    HasDerivAt (fun x => Zs S p a b x m2) (-mom S p a b a m1 m2) m1 := by
  have := hasDerivAt_mom_m1 S p a b (fun _ => 1) m1 m2
  simp only [mom, mul_one, one_mul] at this
  exact this

/-- C09-75: ∂_{m₂} log Z = −⟨ℓ₂⟩ and ∂_{m₁}∂_{m₂} log Z = ⟨ℓ₁ℓ₂⟩ − ⟨ℓ₁⟩⟨ℓ₂⟩ (tilted covariance). -/
theorem mixed_log_derivative (m1 m2 : ℝ) (hZ : ∀ x, 0 < Zs S p a b x m2) :
    HasDerivAt (fun x => Real.log (Zs S p a b m1 x)) (-(mom S p a b b m1 m2 / Zs S p a b m1 m2)) m2 ∧
    HasDerivAt (fun x => -(mom S p a b b x m2 / Zs S p a b x m2))
      (mom S p a b (fun T => b T * a T) m1 m2 / Zs S p a b m1 m2 -
        (mom S p a b a m1 m2 / Zs S p a b m1 m2) * (mom S p a b b m1 m2 / Zs S p a b m1 m2)) m1 := by
  constructor
  · have hz : Zs S p a b m1 m2 ≠ 0 := (hZ m1).ne'
    convert (hasDerivAt_Zs_m2 S p a b m1 m2).log hz using 1; ring
  · have hz : Zs S p a b m1 m2 ≠ 0 := (hZ m1).ne'
    have h := ((hasDerivAt_mom_m1 S p a b b m1 m2).div (hasDerivAt_Zs_m1 S p a b m1 m2) hz).neg
    convert h using 1
    field_simp; ring

end Cov

/-! ### Metric codifferential and Dirac–Kähler operator (C09-81 … C09-83) -/

section DK
variable {n p q : Type*} [Fintype n] [Fintype p] [Fintype q] [DecidableEq n] [DecidableEq p] [DecidableEq q]

/-- C09-81: d* := M_p⁻¹ dᵀ M_q is the adjoint of d : Cᵖ → C^q for ⟨x,y⟩ = xᵀMy. -/
theorem codifferential_adjoint (d : Matrix q p ℝ) (Mp : Matrix p p ℝ) (Mq : Matrix q q ℝ)
    (hMp : IsUnit Mp.det) (x : p → ℝ) (y : q → ℝ) :
    x ⬝ᵥ (Mp *ᵥ ((Mp⁻¹ * dᵀ * Mq) *ᵥ y)) = (d *ᵥ x) ⬝ᵥ (Mq *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hMp,
    Matrix.one_mul, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- D = d + M⁻¹dᵀM is self-adjoint for ⟨x,y⟩_M = xᵀMy (M symmetric invertible). -/
theorem dirac_kahler_selfadjoint (d M : Matrix n n ℝ) (hMs : Mᵀ = M) (hM : IsUnit M.det) (x y : n → ℝ) :
    x ⬝ᵥ (M *ᵥ ((d + M⁻¹ * dᵀ * M) *ᵥ y)) = ((d + M⁻¹ * dᵀ * M) *ᵥ x) ⬝ᵥ (M *ᵥ y) := by
  set D := d + M⁻¹ * dᵀ * M
  have key : M * D = M * d + dᵀ * M := by
    simp only [D]
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hM, Matrix.one_mul]
  have hsym : (M * D)ᵀ = M * D := by
    rw [key, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, hMs, Matrix.transpose_transpose,
      add_comm]
  have h1 : x ⬝ᵥ (M *ᵥ (D *ᵥ y)) = x ⬝ᵥ ((M * D) *ᵥ y) := by rw [Matrix.mulVec_mulVec]
  have h2 : (D *ᵥ x) ⬝ᵥ (M *ᵥ y) = x ⬝ᵥ ((M * D) *ᵥ y) := by
    rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
    congr 2
    rw [← hsym, Matrix.transpose_mul, hMs]
  rw [h1, h2]

/-- C09-81: ⟨x, (D² + m²)x⟩_M = ⟨Dx, Dx⟩_M + m²⟨x,x⟩_M > 0 for x ≠ 0 (M > 0, m > 0), and harmonic
cochains (Dx = 0) satisfy (D² + m²)x = m²x. -/
theorem orbital_frequency_pos (D M : Matrix n n ℝ) (hM : M.PosDef)
    (hsa : ∀ x y : n → ℝ, x ⬝ᵥ (M *ᵥ (D *ᵥ y)) = (D *ᵥ x) ⬝ᵥ (M *ᵥ y)) {m : ℝ} (hm : 0 < m)
    (x : n → ℝ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ (M *ᵥ ((D * D + (m ^ 2) • (1 : Matrix n n ℝ)) *ᵥ x)) ∧
      (D *ᵥ x = 0 → (D * D + (m ^ 2) • (1 : Matrix n n ℝ)) *ᵥ x = (m ^ 2) • x) := by
  constructor
  · rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_add,
      dotProduct_add, hsa, Matrix.mulVec_smul, dotProduct_smul]
    have h1 : 0 ≤ (D *ᵥ x) ⬝ᵥ (M *ᵥ (D *ᵥ x)) := by
      simpa using hM.posSemidef.dotProduct_mulVec_nonneg (D *ᵥ x)
    have h2 : 0 < x ⬝ᵥ (M *ᵥ x) := by simpa using hM.dotProduct_mulVec_pos hx
    simp only [smul_eq_mul]; positivity
  · intro h
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero, zero_add, Matrix.smul_mulVec,
      Matrix.one_mulVec]

/-- C09-82: for an eigenvalue λ of D, ∂_m√(λ² + m²) = m/√(λ² + m²), which equals 1 iff λ = 0 and is
≥ m/√(Λ² + m²) whenever |λ| ≤ Λ. -/
theorem orbital_mass_derivative (lam Λ m : ℝ) (hm : 0 < m) (hl : |lam| ≤ Λ) :
    HasDerivAt (fun x => Real.sqrt (lam ^ 2 + x ^ 2)) (m / Real.sqrt (lam ^ 2 + m ^ 2)) m ∧
      m / Real.sqrt (Λ ^ 2 + m ^ 2) ≤ m / Real.sqrt (lam ^ 2 + m ^ 2) ∧
      m / Real.sqrt (lam ^ 2 + m ^ 2) ≤ 1 ∧ (lam = 0 → m / Real.sqrt (lam ^ 2 + m ^ 2) = 1) := by
  have hpos : 0 < lam ^ 2 + m ^ 2 := by positivity
  have hs := Real.sqrt_pos.mpr hpos
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := ((hasDerivAt_pow 2 m).const_add (lam ^ 2)).sqrt hpos.ne'
    convert h using 1; simp; field_simp
  · apply div_le_div_of_nonneg_left hm.le hs
    apply Real.sqrt_le_sqrt
    have : lam ^ 2 ≤ Λ ^ 2 := by
      have h0 : 0 ≤ Λ := (abs_nonneg _).trans hl
      nlinarith [sq_abs lam, abs_nonneg lam]
    linarith
  · rw [div_le_one hs]
    calc m = Real.sqrt (m ^ 2) := (Real.sqrt_sq hm.le).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg lam])
  · intro h; subst h; simp [Real.sqrt_sq hm.le, hm.ne']

/-- C09-83: congruence by N^{1/2} preserves positive semidefiniteness, so ∂_mH ⪰ 0. -/
theorem lapse_monotone (A N : Matrix n n ℂ) (hA : A.PosSemidef) : (Nᴴ * A * N).PosSemidef :=
  hA.conjTranspose_mul_mul_same N

end DK

/-! ### Coarse symbol (C09-85) -/

section Coarse
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- C09-85: for H = N E, E = √(pᵀh⁻¹p + m²), the velocity ẋ = (N/E)h⁻¹p satisfies
N² − ẋᵀhẋ = (Nm/E)², and pᵀẋ − H = −m(Nm/E). -/
theorem coarse_symbol (h hinv : Matrix n n ℝ) (hh : h * hinv = 1) (hs : hinvᵀ = hinv) (p : n → ℝ)
    (N m : ℝ) (hE : 0 < p ⬝ᵥ (hinv *ᵥ p) + m ^ 2) :
    let E := Real.sqrt (p ⬝ᵥ (hinv *ᵥ p) + m ^ 2)
    let xd := (N / E) • (hinv *ᵥ p)
    (N ^ 2 - xd ⬝ᵥ (h *ᵥ xd) = (N * m / E) ^ 2 ∧ p ⬝ᵥ xd - N * E = -m * (N * m / E)) := by
  intro E xd
  have hE2 : E ^ 2 = p ⬝ᵥ (hinv *ᵥ p) + m ^ 2 := Real.sq_sqrt hE.le
  have hEp : 0 < E := Real.sqrt_pos.mpr hE
  have hq : (hinv *ᵥ p) ⬝ᵥ (h *ᵥ (hinv *ᵥ p)) = p ⬝ᵥ (hinv *ᵥ p) := by
    rw [Matrix.mulVec_mulVec, hh, Matrix.one_mulVec, dotProduct_comm]
  constructor
  · simp only [xd, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, hq]
    field_simp
    rw [hE2]; ring
  · simp only [xd, dotProduct_smul, smul_eq_mul]
    field_simp
    linear_combination (-N) * hE2

end Coarse

/-! ### Cochain counts (C09-86) -/

/-- C09-86: ∂Δ⁴ has (V,E,F,T) = (5,10,10,5) (total 30); a stellar 1–4 move adds (1,4,6,3), giving
(6,14,16,8) (44) and then (7,18,22,11) (58); each has Euler characteristic 0; joint totals 74 and 102. -/
theorem cochain_counts :
    (Nat.choose 5 1, Nat.choose 5 2, Nat.choose 5 3, Nat.choose 5 4) = (5, 10, 10, 5) ∧
    5 + 10 + 10 + 5 = 30 ∧ 6 + 14 + 16 + 8 = 44 ∧ 7 + 18 + 22 + 11 = 58 ∧
    (5 : ℤ) - 10 + 10 - 5 = 0 ∧ (6 : ℤ) - 14 + 16 - 8 = 0 ∧ (7 : ℤ) - 18 + 22 - 11 = 0 ∧
    30 + 44 = 74 ∧ 44 + 58 = 102 := by decide

/-! ### Microscopic metric (C09-91) -/

section Micro
variable {c f : Type*} [Fintype c] [Fintype f] [DecidableEq c] [DecidableEq f]

/-- C09-91: with RP = I, Q = I − PR and M_f = RᵀM_cR + QᵀM_aQ, every v splits as P(Rv) + Qv with
R(Qv) = 0, and ‖Px + y‖_f² = xᵀM_cx + yᵀM_ay whenever Ry = 0. -/
theorem micro_metric (P : Matrix f c ℝ) (R : Matrix c f ℝ) (Mc : Matrix c c ℝ) (Ma : Matrix f f ℝ)
    (hRP : R * P = 1) (x : c → ℝ) (y : f → ℝ) (hy : R *ᵥ y = 0) :
    let Q := 1 - P * R
    let Mf := Rᵀ * Mc * R + Qᵀ * Ma * Q
    (∀ v : f → ℝ, v = P *ᵥ (R *ᵥ v) + Q *ᵥ v ∧ R *ᵥ (Q *ᵥ v) = 0) ∧
      (P *ᵥ x + y) ⬝ᵥ (Mf *ᵥ (P *ᵥ x + y)) = x ⬝ᵥ (Mc *ᵥ x) + y ⬝ᵥ (Ma *ᵥ y) := by
  intro Q Mf
  have hRQ : R * Q = 0 := by
    simp only [Q, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hRP, Matrix.one_mul, sub_self]
  have hQP : Q * P = 0 := by
    simp only [Q, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hRP, Matrix.mul_one, sub_self]
  have hRw : R *ᵥ (P *ᵥ x + y) = x := by
    rw [Matrix.mulVec_add, hy, add_zero, Matrix.mulVec_mulVec, hRP, Matrix.one_mulVec]
  have hQw : Q *ᵥ (P *ᵥ x + y) = y := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hQP, Matrix.zero_mulVec, zero_add]
    simp only [Q, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero, sub_zero]
  refine ⟨fun v => ⟨?_, ?_⟩, ?_⟩
  · simp only [Q, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]; abel
  · rw [Matrix.mulVec_mulVec, hRQ, Matrix.zero_mulVec]
  · have split : ∀ (A : Matrix c f ℝ) (B : Matrix c c ℝ) (w : f → ℝ),
        w ⬝ᵥ ((Aᵀ * B * A) *ᵥ w) = (A *ᵥ w) ⬝ᵥ (B *ᵥ (A *ᵥ w)) := by
      intro A B w
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    have split' : ∀ (A : Matrix f f ℝ) (B : Matrix f f ℝ) (w : f → ℝ),
        w ⬝ᵥ ((Aᵀ * B * A) *ᵥ w) = (A *ᵥ w) ⬝ᵥ (B *ᵥ (A *ᵥ w)) := by
      intro A B w
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    simp only [Mf, Matrix.add_mulVec, dotProduct_add]
    rw [split, split', hRw, hQw]

end Micro

/-! ### Projected bridge arithmetic (C09-36) -/

/-- C09-36 (arithmetic consistency): the listed spectrum {0, ±2, ±√205/5, ±(1 + 2√15/5),
±(2√15/5 − 1)} has Σλ² = 38, the largest |λ| is √205/5 ∈ (2.8635, 2.8636), and the tensor norm is
(√205/5)² = 41/5. -/
theorem bridge_spectrum_arith :
    0 ^ 2 + 2 * 2 ^ 2 + 2 * (Real.sqrt 205 / 5) ^ 2 + 2 * (1 + 2 * Real.sqrt 15 / 5) ^ 2 +
        2 * (2 * Real.sqrt 15 / 5 - 1) ^ 2 = 38 ∧
      1 + 2 * Real.sqrt 15 / 5 < Real.sqrt 205 / 5 ∧ 2 < Real.sqrt 205 / 5 ∧
      2.8635 < Real.sqrt 205 / 5 ∧ Real.sqrt 205 / 5 < 2.8636 ∧ (Real.sqrt 205 / 5) ^ 2 = 41 / 5 := by
  have h205 : Real.sqrt 205 ^ 2 = 205 := Real.sq_sqrt (by norm_num)
  have h15 : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  have a1 : (14.3178 : ℝ) < Real.sqrt 205 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have a2 : Real.sqrt 205 < 14.3179 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have b2 : Real.sqrt 15 < 3.873 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  refine ⟨by nlinarith [h205, h15], by linarith, by linarith, by linarith, by linarith, by
    rw [div_pow, h205]; norm_num⟩

end Entropic.AppH11
