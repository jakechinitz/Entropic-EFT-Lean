import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-! Appendix H.10: perfect-action pullback, compression, renewal channel and GNS projector
(ledger C08-24, -25, -32, -34, -51, -52, -53, -54, -55, -64, -73, -84, -86). -/

noncomputable section
namespace Entropic.AppH10
open Matrix
open scoped Kronecker

section Pullback
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable (F : Matrix m n ℂ) (hF : F * Fᴴ = 1)

/-- The null complement Q_N := I − F†F. -/
def nullQ : Matrix n n ℂ := 1 - Fᴴ * F

include hF

theorem F_nullQ : F * nullQ F = 0 := by
  unfold nullQ; rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hF, Matrix.one_mul, sub_self]

theorem nullQ_Fh : nullQ F * Fᴴ = 0 := by
  unfold nullQ; rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hF, Matrix.mul_one, sub_self]

theorem nullQ_idem : nullQ F * nullQ F = nullQ F := by
  have h := F_nullQ F hF
  unfold nullQ at h ⊢
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, h, Matrix.mul_zero, sub_zero]

/-- C08-32: A_fine Q_N = 0 for A_fine := A F (the complement is null for the induced seminorm). -/
theorem fine_null {k : Type*} [Fintype k] (A : Matrix k m ℂ) : (A * F) * nullQ F = 0 := by
  rw [Matrix.mul_assoc, F_nullQ F hF, Matrix.mul_zero]

/-- C08-55 (second part): A_fine ∘ I_N = A_N with I_N := F†. -/
theorem fine_embed {k : Type*} [Fintype k] (A : Matrix k m ℂ) : (A * F) * Fᴴ = A := by
  rw [Matrix.mul_assoc, hF, Matrix.mul_one]

/-- The primitive kernel K^prim := F†K^cF + C with C F† = 0 (C = Δ_N Q_N, or the hierarchical H_T). -/
def prim (Kc : Matrix m m ℂ) (C : Matrix n n ℂ) : Matrix n n ℂ := Fᴴ * Kc * F + C

/-- C08-51 (first identity): F K^prim F† = K^c whenever C F† = 0. -/
theorem prim_compress (Kc : Matrix m m ℂ) (C : Matrix n n ℂ) (hC : C * Fᴴ = 0) :
    F * prim F Kc C * Fᴴ = Kc := by
  unfold prim
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc F C, hC, Matrix.mul_zero, add_zero,
    show F * (Fᴴ * Kc * F) * Fᴴ = (F * Fᴴ) * Kc * (F * Fᴴ) by simp only [Matrix.mul_assoc], hF]
  simp

/-- The primitive kernel intertwines: K^prim F† = F† K^c. -/
theorem prim_intertwine (Kc : Matrix m m ℂ) (C : Matrix n n ℂ) (hC : C * Fᴴ = 0) :
    prim F Kc C * Fᴴ = Fᴴ * Kc := by
  unfold prim
  rw [Matrix.add_mul, hC, add_zero, Matrix.mul_assoc, hF, Matrix.mul_one]

theorem prim_pow_intertwine (Kc : Matrix m m ℂ) (C : Matrix n n ℂ) (hC : C * Fᴴ = 0) (k : ℕ) :
    prim F Kc C ^ k * Fᴴ = Fᴴ * Kc ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, prim_intertwine F hF Kc C hC,
      Matrix.mul_assoc, ← pow_succ']

/-- C08-51 (resolvent): with Δ ≠ z, R := (K^c − z)⁻¹ (two-sided), the matrix
F†RF + (Δ − z)⁻¹Q_N is a two-sided inverse of K^prim − z, and compresses to R. -/
theorem prim_resolvent (Kc R : Matrix m m ℂ) (Δ z : ℂ) (hΔ : Δ - z ≠ 0)
    (hR1 : (Kc - z • 1) * R = 1) (hR2 : R * (Kc - z • 1) = 1) :
    (prim F Kc (Δ • nullQ F) - z • 1) * (Fᴴ * R * F + (Δ - z)⁻¹ • nullQ F) = 1 ∧
      (Fᴴ * R * F + (Δ - z)⁻¹ • nullQ F) * (prim F Kc (Δ • nullQ F) - z • 1) = 1 ∧
      F * (Fᴴ * R * F + (Δ - z)⁻¹ • nullQ F) * Fᴴ = R := by
  have hFQ := F_nullQ F hF
  have hQF := nullQ_Fh F hF
  have hQQ := nullQ_idem F hF
  have h1 : (1 : Matrix n n ℂ) = Fᴴ * F + nullQ F := by unfold nullQ; abel
  have hdec : prim F Kc (Δ • nullQ F) - z • 1 = Fᴴ * (Kc - z • 1) * F + (Δ - z) • nullQ F := by
    unfold prim; rw [h1]; simp only [Matrix.mul_sub, Matrix.sub_mul, smul_add, sub_smul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    abel
  refine ⟨?_, ?_, ?_⟩
  · rw [hdec]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul]
    rw [show Fᴴ * (Kc - z • 1) * F * (Fᴴ * R * F) = Fᴴ * ((Kc - z • 1) * ((F * Fᴴ) * R)) * F by
        simp only [Matrix.mul_assoc], hF, Matrix.one_mul, hR1,
      show Fᴴ * (Kc - z • 1) * F * nullQ F = Fᴴ * (Kc - z • 1) * (F * nullQ F) by
        simp only [Matrix.mul_assoc], hFQ,
      show nullQ F * (Fᴴ * R * F) = (nullQ F * Fᴴ) * R * F by simp only [Matrix.mul_assoc], hQF, hQQ]
    simp only [Matrix.mul_zero, Matrix.zero_mul, smul_zero, add_zero, zero_add, Matrix.mul_one, smul_smul,
      mul_inv_cancel₀ hΔ, inv_mul_cancel₀ hΔ, one_smul]
    rw [h1]
  · rw [hdec]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul]
    rw [show Fᴴ * R * F * (Fᴴ * (Kc - z • 1) * F) = Fᴴ * (R * ((F * Fᴴ) * (Kc - z • 1))) * F by
        simp only [Matrix.mul_assoc], hF, Matrix.one_mul, hR2,
      show Fᴴ * R * F * nullQ F = Fᴴ * R * (F * nullQ F) by simp only [Matrix.mul_assoc], hFQ,
      show nullQ F * (Fᴴ * (Kc - z • 1) * F) = (nullQ F * Fᴴ) * (Kc - z • 1) * F by
        simp only [Matrix.mul_assoc], hQF, hQQ]
    simp only [Matrix.mul_zero, Matrix.zero_mul, smul_zero, add_zero, zero_add, Matrix.mul_one, smul_smul,
      mul_inv_cancel₀ hΔ, inv_mul_cancel₀ hΔ, one_smul]
    rw [h1]
  · rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hFQ,
      show F * (Fᴴ * R * F) * Fᴴ = (F * Fᴴ) * R * (F * Fᴴ) by simp only [Matrix.mul_assoc], hF]
    simp

/-- C08-54, C08-64: the same pullback with any complement C (e.g. H_T) satisfying C F† = 0,
F C = 0 and a two-sided inverse Cinv of C − z on Ran Q (C Q = C, (C − z)Cinv = Q). -/
theorem prim_resolvent_general (Kc R : Matrix m m ℂ) (C Ci : Matrix n n ℂ) (z : ℂ)
    (hCF : C * Fᴴ = 0) (hFC : F * C = 0) (hCiF : Ci * Fᴴ = 0) (hFCi : F * Ci = 0)
    (hCi : (C - z • nullQ F) * Ci = nullQ F)
    (hR1 : (Kc - z • 1) * R = 1) :
    (prim F Kc C - z • 1) * (Fᴴ * R * F + Ci) = 1 ∧ F * (Fᴴ * R * F + Ci) * Fᴴ = R := by
  have hFQ := F_nullQ F hF
  have hQF := nullQ_Fh F hF
  have h1 : (1 : Matrix n n ℂ) = Fᴴ * F + nullQ F := by unfold nullQ; abel
  have hdec : prim F Kc C - z • 1 = Fᴴ * (Kc - z • 1) * F + (C - z • nullQ F) := by
    unfold prim; rw [h1]; simp only [Matrix.mul_sub, Matrix.sub_mul, smul_add, Matrix.mul_one]
    rw [show Fᴴ * (z • (1 : Matrix m m ℂ)) * F = z • (Fᴴ * F) by simp]; abel
  have hYF : (C - z • nullQ F) * Fᴴ = 0 := by
    rw [Matrix.sub_mul, hCF, Matrix.smul_mul, hQF, smul_zero, sub_zero]
  constructor
  · rw [hdec, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      show Fᴴ * (Kc - z • 1) * F * (Fᴴ * R * F) = Fᴴ * ((Kc - z • 1) * ((F * Fᴴ) * R)) * F by
        simp only [Matrix.mul_assoc], hF, Matrix.one_mul, hR1,
      show Fᴴ * (Kc - z • 1) * F * Ci = Fᴴ * (Kc - z • 1) * (F * Ci) by simp only [Matrix.mul_assoc],
      hFCi, show (C - z • nullQ F) * (Fᴴ * R * F) = ((C - z • nullQ F) * Fᴴ) * R * F by
        simp only [Matrix.mul_assoc], hYF, hCi, h1]
    simp
  · rw [Matrix.mul_add, Matrix.add_mul, hFCi, Matrix.zero_mul, add_zero,
      show F * (Fᴴ * R * F) * Fᴴ = (F * Fᴴ) * R * (F * Fᴴ) by simp only [Matrix.mul_assoc], hF]
    simp

end Pullback


section Exp
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- C08-53: F exp(K^prim) F† = exp(K^c) (apply with K = −itH/ħ, both for H^prim and the joint
geometry-defect version F ⊗ I): every power intertwines, and the exponential series is mapped
termwise by the continuous linear map X ↦ F X F†. -/
theorem prim_exp (F : Matrix m n ℂ) (hF : F * Fᴴ = 1) (Kc : Matrix m m ℂ) (C : Matrix n n ℂ)
    (hC : C * Fᴴ = 0) :
    F * NormedSpace.exp (prim F Kc C) * Fᴴ = NormedSpace.exp Kc := by
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  let L : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ :=
    { toFun := fun X => F * X * Fᴴ
      map_add' := fun X Y => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by simp }
  let Lc : Matrix n n ℂ →L[ℂ] Matrix m m ℂ := LinearMap.toContinuousLinearMap L
  have hsum := NormedSpace.expSeries_summable' (𝕂 := ℂ) (prim F Kc C)
  rw [NormedSpace.exp_eq_tsum ℂ, NormedSpace.exp_eq_tsum ℂ]
  have hmap : F * (∑' k : ℕ, ((k.factorial : ℂ)⁻¹) • prim F Kc C ^ k) * Fᴴ =
      Lc (∑' k : ℕ, ((k.factorial : ℂ)⁻¹) • prim F Kc C ^ k) := rfl
  rw [hmap, Lc.map_tsum hsum]
  congr 1; funext k
  show F * (((k.factorial : ℂ)⁻¹) • prim F Kc C ^ k) * Fᴴ = ((k.factorial : ℂ)⁻¹) • Kc ^ k
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, prim_pow_intertwine F hF Kc C hC k,
    ← Matrix.mul_assoc, hF, Matrix.one_mul]

end Exp

/-! ### Dilated update, compression, renewal channel, GNS projector -/

section Misc
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- C08-73: V†V = P + (1/9)Σₐ W_a†W_a Q = I when each W_a is an isometry and P + Q = I. -/
theorem dilation_isometry (P Q : Matrix n n ℂ) (W : Fin 9 → Matrix n n ℂ) (hPQ : P + Q = 1)
    (hW : ∀ a, (W a)ᴴ * W a = 1) :
    P + (1/9 : ℂ) • (∑ a, (W a)ᴴ * W a) * Q = 1 := by
  rw [Finset.sum_congr rfl (fun a _ => hW a), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  norm_num; exact hPQ

/-- C08-34: for an orthogonal projector P, (CP)†(CP) = (PCP)†(PCP) + ((I−P)CP)†((I−P)CP); summed
over I this is ⟨Ψ,PMPΨ⟩ − Σ‖PC_IPΨ‖² = Σ‖(I−P)C_IPΨ‖² ≥ 0. -/
theorem compression_split (P C : Matrix n n ℂ) (hP : P * P = P) (hPh : Pᴴ = P) :
    (C * P)ᴴ * (C * P) = (P * C * P)ᴴ * (P * C * P) + ((1 - P) * C * P)ᴴ * ((1 - P) * C * P) := by
  have h1 : (1 - P)ᴴ = 1 - P := by rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPh]
  simp only [Matrix.conjTranspose_mul, hPh, h1]
  have hq : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hP]; simp
  calc P * Cᴴ * (C * P) = P * Cᴴ * P * C * P + P * Cᴴ * (1 - P) * C * P := by noncomm_ring
    _ = P * Cᴴ * (P * P) * C * P + P * Cᴴ * ((1 - P) * (1 - P)) * C * P := by rw [hP, hq]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem compression_nonneg (P C : Matrix n n ℂ) (ψ : n → ℂ) :
    0 ≤ (star (((1 - P) * C * P) *ᵥ ψ) ⬝ᵥ (((1 - P) * C * P) *ᵥ ψ)).re := by
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.re_sum]
  exact Finset.sum_nonneg (fun i _ => by
    rw [mul_comm, Complex.mul_conj]; simp [Complex.normSq_nonneg])

/-- C08-24: for a probability vector p, v := (√p_b) is a unit vector; P_stat := vvᵀ is a rank-one
orthogonal projector; ρ_* := diag p has trace 1. -/
theorem stat_projector (p : n → ℝ) (hp : ∀ b, 0 ≤ p b) (hp1 : ∑ b, p b = 1) :
    (∑ b, Real.sqrt (p b) ^ 2 = 1) ∧
      (Matrix.vecMulVec (fun b => Real.sqrt (p b)) (fun b => Real.sqrt (p b))) *
          (Matrix.vecMulVec (fun b => Real.sqrt (p b)) (fun b => Real.sqrt (p b))) =
        Matrix.vecMulVec (fun b => Real.sqrt (p b)) (fun b => Real.sqrt (p b)) ∧
      (Matrix.diagonal p).trace = 1 := by
  have hv : ∑ b, Real.sqrt (p b) ^ 2 = 1 := by
    simp_rw [Real.sq_sqrt (hp _)]; exact hp1
  refine ⟨hv, ?_, by rw [Matrix.trace_diagonal, hp1]⟩
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply]
  rw [show ∑ k, √(p i) * √(p k) * (√(p k) * √(p j)) = √(p i) * √(p j) * ∑ k, √(p k) ^ 2 by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring), hv, mul_one]

/-- The replacement channel E_*(X) = ρ_* Tr X. -/
def replace (ρ X : Matrix n n ℂ) : Matrix n n ℂ := X.trace • ρ

/-- C08-24, C08-25: E_* is trace preserving and idempotent when Tr ρ_* = 1; it kills every traceless X;
its fixed points are exactly the multiples of ρ_*. -/
theorem replace_props (ρ : Matrix n n ℂ) (hρ : ρ.trace = 1) :
    (∀ X, (replace ρ X).trace = X.trace) ∧ (∀ X, replace ρ (replace ρ X) = replace ρ X) ∧
      (∀ X, X.trace = 0 → replace ρ X = 0) ∧ (∀ X, replace ρ X = X ↔ ∃ c : ℂ, X = c • ρ) := by
  refine ⟨fun X => by simp [replace, Matrix.trace_smul, hρ], fun X => by
    simp [replace, Matrix.trace_smul, hρ], fun X hX => by simp [replace, hX], fun X => ⟨fun h =>
      ⟨X.trace, h.symm⟩, ?_⟩⟩
  rintro ⟨c, rfl⟩; simp [replace, Matrix.trace_smul, hρ]

/-- ω_*(A) = Tr(ρA), Π_*(A) = ω_*(A) I, ⟨A, B⟩_ω = Tr(ρA†B). -/
def omega (ρ A : Matrix n n ℂ) : ℂ := (ρ * A).trace
def gnsPi (ρ A : Matrix n n ℂ) : Matrix n n ℂ := omega ρ A • 1
def gnsInner (ρ A B : Matrix n n ℂ) : ℂ := (ρ * (Aᴴ * B)).trace

/-- C08-84: Π_* is idempotent, self-adjoint for ⟨·,·⟩_ω, with ⟨A, Π_*B⟩ = conj ω(A) ω(B); and
Π_* is the Hilbert–Schmidt adjoint of E_*. -/
theorem gns_projector (ρ : Matrix n n ℂ) (hρ : ρ.trace = 1) (hH : ρᴴ = ρ) (A B X : Matrix n n ℂ) :
    gnsPi ρ (gnsPi ρ A) = gnsPi ρ A ∧
      gnsInner ρ A (gnsPi ρ B) = star (omega ρ A) * omega ρ B ∧
      gnsInner ρ (gnsPi ρ A) B = star (omega ρ A) * omega ρ B ∧
      (Xᴴ * gnsPi ρ A).trace = ((replace ρ X)ᴴ * A).trace := by
  have hstar : star (omega ρ A) = (ρ * Aᴴ).trace := by
    unfold omega
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hH, Matrix.trace_mul_comm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [gnsPi, omega, Matrix.mul_smul, Matrix.trace_smul, hρ]
  · simp only [gnsInner, gnsPi, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, hstar]
    ring
  · simp only [gnsInner, gnsPi, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    rfl
  · simp only [gnsPi, replace, omega, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
      Matrix.conjTranspose_smul, Matrix.smul_mul, hH, smul_eq_mul]
    rw [Matrix.trace_conjTranspose]; ring

end Misc

/-! ### Renewal factorization of joint states (C08-86) -/

section Joint
variable {s r : Type*} [Fintype s] [Fintype r] [DecidableEq s] [DecidableEq r]

/-- Partial trace over the second (record) factor. -/
def ptrR (X : Matrix (s × r) (s × r) ℂ) : Matrix s s ℂ := Matrix.of fun i j => ∑ k, X (i, k) (j, k)

/-- id_S ⊗ E_* realized as X ↦ Tr_R X ⊗ ρ_*. -/
def idReplace (ρ : Matrix r r ℂ) (X : Matrix (s × r) (s × r) ℂ) : Matrix (s × r) (s × r) ℂ :=
  ptrR X ⊗ₖ ρ

/-- On product operators A ⊗ B it is A ⊗ E_*(B), so it is the linear extension id ⊗ E_*. -/
theorem idReplace_kron (ρ : Matrix r r ℂ) (A : Matrix s s ℂ) (B : Matrix r r ℂ) :
    idReplace ρ (A ⊗ₖ B) = A ⊗ₖ replace ρ B := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [idReplace, ptrR, replace, Matrix.kroneckerMap_apply, Matrix.trace, Finset.mul_sum, mul_comm,
    mul_left_comm]

theorem idReplace_add (ρ : Matrix r r ℂ) (X Y : Matrix (s × r) (s × r) ℂ) :
    idReplace ρ (X + Y) = idReplace ρ X + idReplace ρ Y := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [idReplace, ptrR, Matrix.kroneckerMap_apply, Finset.sum_add_distrib, add_mul]

/-- C08-86: (U ⊗ I)(id ⊗ E_*)(ρ_SR)(U† ⊗ I) = U Tr_R(ρ_SR) U† ⊗ ρ_*. -/
theorem idReplace_unitary (ρ : Matrix r r ℂ) (U : Matrix s s ℂ) (X : Matrix (s × r) (s × r) ℂ) :
    (U ⊗ₖ (1 : Matrix r r ℂ)) * idReplace ρ X * (Uᴴ ⊗ₖ (1 : Matrix r r ℂ)) = (U * ptrR X * Uᴴ) ⊗ₖ ρ := by
  unfold idReplace
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

end Joint

end Entropic.AppH10
