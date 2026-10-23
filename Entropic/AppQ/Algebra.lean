import Entropic.AppP.Numbers
import Entropic.AppIJ.Shells
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-! Appendix Q, algebraic items: K² equality cases (C15-06), the same-factor impossibility
remainder (C15-07), capacity/gauge commutation (C15-09), frame covariance and frame-independent
traces (C15-15 … C15-17), the tetrahedral witness identity (C15-18, C15-19), the equilibrium transfer
projector (C15-20), the homogeneous potential and its minimum (C15-23 … C15-25), fresh amplitudes
(C15-26), push-forward Hessians and the frame connection (C15-28 … C15-30), the return contraction
(C15-32), the sharing-entropy split (C15-34), set invariance and counts (C15-41, C15-42, C15-44),
hinge kernels (C15-50 … C15-52, C15-75), the channel-area chain (C15-53 … C15-56), frame transport
(C15-63), the two-direction decomposition (C15-64), counts and parity (C15-65 … C15-68), block
selection (C15-74) and sewing kernels (C15-77, C15-78). -/

noncomputable section
namespace Entropic.AppQ
open Real Matrix
open scoped Kronecker

/-! ### C15-06: equality cases of the K² floor -/

def eqB (a b c d : Fin 7) : Bool :=
  a == b || a == c || a == d || b == c || b == d || c == d ||
    !(Entropic.AppP.Num.pairSum ((a.val:ℤ) - 3) ((b.val:ℤ) - 3) ((c.val:ℤ) - 3) ((d.val:ℤ) - 3) == 11) ||
    ((3 ≤ a.val && 3 ≤ b.val && 3 ≤ c.val && 3 ≤ d.val) || (a.val ≤ 3 && b.val ≤ 3 && c.val ≤ 3 && d.val ≤ 3))

theorem eqB_all : ∀ a b c d : Fin 7, eqB a b c d = true := by decide +kernel

/-- C15-06: for distinct labels, K² = 122/3 (pair sum 11) only when all labels are ≥ 0 or all are ≤ 0,
i.e. the set is {0,1,2,3} or {−3,−2,−1,0}. -/
theorem K2_equality (a b c d : Fin 7) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d)
    (h : Entropic.AppP.Num.pairSum ((a.val:ℤ) - 3) ((b.val:ℤ) - 3) ((c.val:ℤ) - 3) ((d.val:ℤ) - 3) = 11) :
    (3 ≤ a.val ∧ 3 ≤ b.val ∧ 3 ≤ c.val ∧ 3 ≤ d.val) ∨ (a.val ≤ 3 ∧ b.val ≤ 3 ∧ c.val ≤ 3 ∧ d.val ≤ 3) := by
  have := eqB_all a b c d
  simp [eqB, hab, hac, had, hbc, hbd, hcd, h] at this
  omega

/-! ### C15-07, C15-09 -/

/-- C15-07 (remainder): if ⟨v, K²v⟩ ≥ (122/3)‖v‖² and C²v = 0 for a nonzero v, then K² and C² differ on v;
and any polynomial f(C²) acts on such v as f(0). -/
theorem same_factor {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (K C : E →ₗ[ℝ] E) (v : E)
    (hv : v ≠ 0) (hK : (122/3) * ‖v‖ ^ 2 ≤ inner ℝ v (K v)) (hC : C v = 0) : K v ≠ C v := by
  intro h
  rw [h, hC, inner_zero_right] at hK
  have : 0 < ‖v‖ := norm_pos_iff.mpr hv
  nlinarith

theorem gibbs_constant {E : Type*} [AddCommGroup E] [Module ℝ E] (C : E →ₗ[ℝ] E) (v : E) (hC : C v = 0)
    (p : Polynomial ℝ) : (Polynomial.aeval C p) v = p.eval 0 • v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_smul]
  | monomial n a =>
    cases n with
    | zero => simp
    | succ k => simp [pow_succ, hC]

/-- C15-09: I ⊗ O ⊗ I commutes with U ⊗ I ⊗ I. -/
theorem capacity_commutes {n m k : Type*} [Fintype n] [Fintype m] [Fintype k] [DecidableEq n] [DecidableEq m]
    [DecidableEq k] (U : Matrix n n ℂ) (O : Matrix m m ℂ) :
    ((U ⊗ₖ (1 : Matrix m m ℂ)) ⊗ₖ (1 : Matrix k k ℂ)) * (((1 : Matrix n n ℂ) ⊗ₖ O) ⊗ₖ (1 : Matrix k k ℂ)) =
      (((1 : Matrix n n ℂ) ⊗ₖ O) ⊗ₖ (1 : Matrix k k ℂ)) * ((U ⊗ₖ (1 : Matrix m m ℂ)) ⊗ₖ (1 : Matrix k k ℂ)) := by
  simp only [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

/-! ### C15-15 … C15-17: relational-frame covariance -/

section Frame
variable {G n : Type*} [Monoid G] [Fintype n] [DecidableEq n]

/-- C15-15: for a homomorphism U into unitary matrices, K²(GR) = U(G) K²(R) U(G)†. -/
theorem frame_covariance (U : G →* Matrix n n ℂ) (K : Matrix n n ℂ) (g r : G) :
    U (g * r) * K * (U (g * r))ᴴ = U g * (U r * K * (U r)ᴴ) * (U g)ᴴ := by
  rw [map_mul, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]

/-- C15-16, C15-17: unitary conjugation preserves rank, trace, and Tr[P e^{−ηK}]. -/
theorem frame_invariance (V : Matrix n n ℂ) (hV : Vᴴ * V = 1) (P K : Matrix n n ℂ) (η : ℂ) :
    (V * P * Vᴴ).rank = P.rank ∧ (V * P * Vᴴ).trace = P.trace ∧
      ((V * P * Vᴴ) * NormedSpace.exp (-η • (V * K * Vᴴ))).trace = (P * NormedSpace.exp (-η • K)).trace := by
  have hVV : V * Vᴴ = 1 := mul_eq_one_comm.mp hV
  have hu : IsUnit V := (Matrix.isUnit_iff_isUnit_det V).mpr (Matrix.isUnit_det_of_right_inverse hVV)
  have hinv : V⁻¹ = Vᴴ := Matrix.inv_eq_right_inv hVV
  have hdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).mp hu
  have hdet' : IsUnit Vᴴ.det := by
    rw [Matrix.det_conjTranspose]; exact hdet.star
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdet', Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet]
  · rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]
  · have e : -η • (V * K * Vᴴ) = V * (-η • K) * V⁻¹ := by
      rw [hinv, Matrix.mul_smul, Matrix.smul_mul]
    rw [e, Matrix.exp_conj _ _ hu, hinv]
    have : V * P * Vᴴ * (V * NormedSpace.exp (-η • K) * Vᴴ) = V * (P * NormedSpace.exp (-η • K)) * Vᴴ := by
      simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul]
    rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]
end Frame

/-! ### C15-18, C15-19: tetrahedral witness -/

def tv : Fin 4 → Fin 3 → ℝ := ![![1,1,1], ![1,-1,-1], ![-1,1,-1], ![-1,-1,1]]

/-- C15-18: |Σ bᵢvᵢ|² = 4Σbᵢ² − (Σbᵢ)². -/
theorem witness_identity (b : Fin 4 → ℝ) :
    ∑ a, (∑ i, b i * tv i a) ^ 2 = 4 * ∑ i, b i ^ 2 - (∑ i, b i) ^ 2 := by
  simp [Fin.sum_univ_succ, tv]; ring

/-- C15-19: Σ(12 − bᵢ²) + (1/3)|Σbᵢvᵢ|² = 48 − ((Σb)² − Σb²)/3. -/
theorem witness_K2 (b : Fin 4 → ℝ) :
    ∑ i, (12 - b i ^ 2) + (1/3) * ∑ a, (∑ i, b i * tv i a) ^ 2 =
      48 - ((∑ i, b i) ^ 2 - ∑ i, b i ^ 2) / 3 := by
  rw [witness_identity]; simp [Fin.sum_univ_succ]; ring

/-- C15-42: K²(b) depends only on the unordered set: invariant under permutations of the four slots. -/
theorem K2_perm (b : Fin 4 → ℝ) (σ : Equiv.Perm (Fin 4)) :
    48 - ((∑ i, b (σ i)) ^ 2 - ∑ i, b (σ i) ^ 2) / 3 = 48 - ((∑ i, b i) ^ 2 - ∑ i, b i ^ 2) / 3 := by
  rw [Equiv.sum_comp σ b, Equiv.sum_comp σ (fun i => b i ^ 2)]

/-! ### C15-20: the equilibrium transfer projector -/

section Pi
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- ω(A) = Tr(ρA) for ρ = diag(p). -/
def omegaS (p : n → ℝ) (A : Matrix n n ℂ) : ℂ := (Matrix.diagonal (fun b => (p b : ℂ)) * A).trace

/-- C15-20: Π(A) = ω(A)I is idempotent, self-adjoint for ⟨A,B⟩ = Tr(ρA†B), and ⟨A,A⟩ > 0 for A ≠ 0 when p > 0. -/
theorem transfer_projector (p : n → ℝ) (hp : ∀ b, 0 < p b) (h1 : ∑ b, p b = 1) (A B : Matrix n n ℂ) :
    omegaS p (omegaS p A • (1 : Matrix n n ℂ)) = omegaS p A ∧
      omegaS p (Aᴴ * (omegaS p B • 1)) = omegaS p ((omegaS p A • (1 : Matrix n n ℂ))ᴴ * B) ∧
      (A ≠ 0 → 0 < (omegaS p (Aᴴ * A)).re) := by
  have hone : omegaS p 1 = 1 := by
    simp [omegaS, Matrix.trace_diagonal]; exact_mod_cast h1
  refine ⟨?_, ?_, ?_⟩
  · simp only [omegaS, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
    rw [show (Matrix.diagonal (fun b => (p b : ℂ))).trace = 1 by
      simp [Matrix.trace_diagonal]; exact_mod_cast h1, mul_one]
  · have hω : ∀ X : Matrix n n ℂ, omegaS p X = ∑ b, (p b : ℂ) * X b b := by
      intro X; simp [omegaS, Matrix.trace, Matrix.diagonal_mul]
    have hst : star (omegaS p A) = omegaS p Aᴴ := by
      rw [hω, hω, star_sum]
      exact Finset.sum_congr rfl (fun b _ => by
        rw [star_mul', Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_ofReal, mul_comm])
    have e1 : Aᴴ * (omegaS p B • (1 : Matrix n n ℂ)) = omegaS p B • Aᴴ := by
      rw [Matrix.mul_smul, Matrix.mul_one]
    have e2 : (omegaS p A • (1 : Matrix n n ℂ))ᴴ * B = star (omegaS p A) • B := by
      rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.one_mul]
    rw [e1, e2, hst]
    simp only [omegaS, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]; ring
  · intro hA
    obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
      by_contra h; push_neg at h; exact hA (Matrix.ext h)
    have hω : omegaS p (Aᴴ * A) = ∑ b, ((p b * ∑ k, Complex.normSq (A k b) : ℝ) : ℂ) := by
      simp only [omegaS, Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
      push_cast
      simp only [Complex.normSq_eq_conj_mul_self, Complex.star_def]
    rw [hω, ← Complex.ofReal_sum, Complex.ofReal_re]
    apply Finset.sum_pos' (fun b _ => mul_nonneg (hp b).le (Finset.sum_nonneg (fun k _ => Complex.normSq_nonneg _)))
    refine ⟨j, Finset.mem_univ _, mul_pos (hp j) ?_⟩
    exact Finset.sum_pos' (fun k _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hij⟩
end Pi

/-! ### C15-23 … C15-26: homogeneous potential -/

/-- C15-24: for r < 0 < u, κ > 0 and ρ_J ≥ 0, V ≥ −r²/(2u), with equality iff ρ₀ = ρ₁ = ρ₂ = 0 and ρ₃ = −r/u. -/
theorem potential_minimum {r u κ ρ0 ρ1 ρ2 ρ3 : ℝ} (hr : r < 0) (hu : 0 < u) (hκ : 0 < κ)
    (h0 : 0 ≤ ρ0) (h1 : 0 ≤ ρ1) (h2 : 0 ≤ ρ2) (h3 : 0 ≤ ρ3) :
    let ρ := ρ0 + ρ1 + ρ2 + ρ3
    let V := r * ρ + u / 2 * ρ ^ 2 + κ * (6 * ρ0 + 5 * ρ1 + 3 * ρ2)
    (-r ^ 2 / (2 * u) ≤ V ∧ (V = -r ^ 2 / (2 * u) ↔ ρ0 = 0 ∧ ρ1 = 0 ∧ ρ2 = 0 ∧ ρ3 = -r / u)) := by
  intro ρ V
  have key : V + r ^ 2 / (2 * u) = u / 2 * (ρ + r / u) ^ 2 + κ * (6 * ρ0 + 5 * ρ1 + 3 * ρ2) := by
    simp only [V]; field_simp; ring
  have hk : 0 ≤ κ * (6 * ρ0 + 5 * ρ1 + 3 * ρ2) := by positivity
  have hs : 0 ≤ u / 2 * (ρ + r / u) ^ 2 := by positivity
  have hneg : -r ^ 2 / (2 * u) = -(r ^ 2 / (2 * u)) := by ring
  refine ⟨by linarith, ⟨fun h => ?_, fun ⟨a, b, c, d⟩ => ?_⟩⟩
  · have hsum : u / 2 * (ρ + r / u) ^ 2 + κ * (6 * ρ0 + 5 * ρ1 + 3 * ρ2) = 0 := by
      rw [← key, h]; ring
    have e1 : κ * (6 * ρ0 + 5 * ρ1 + 3 * ρ2) = 0 := by linarith
    have e2 : u / 2 * (ρ + r / u) ^ 2 = 0 := by linarith
    have e3 : 6 * ρ0 + 5 * ρ1 + 3 * ρ2 = 0 := by
      rcases mul_eq_zero.mp e1 with h | h
      · linarith
      · exact h
    have a0 : ρ0 = 0 := by linarith
    have a1 : ρ1 = 0 := by linarith
    have a2 : ρ2 = 0 := by linarith
    have e4 : ρ + r / u = 0 := by
      rcases mul_eq_zero.mp e2 with h | h
      · linarith
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    refine ⟨a0, a1, a2, ?_⟩
    simp only [ρ] at e4; rw [a0, a1, a2] at e4; rw [neg_div]; linarith
  · have : V + r ^ 2 / (2 * u) = 0 := by
      rw [key]; simp only [ρ]; rw [a, b, c, d]; field_simp; ring
    linarith

/-- C15-25: at the minimizer ∂V/∂ρ_J = r + uρ + κq_J = κq_J, so m²_{J|3} = 6κ, 5κ, 3κ > 0. -/
theorem relative_masses {r u κ : ℝ} (hu : 0 < u) (hκ : 0 < κ) :
    let ρ := -r / u
    (r + u * ρ + κ * 6) - (r + u * ρ + κ * 0) = 6 * κ ∧ (r + u * ρ + κ * 5) - (r + u * ρ) = 5 * κ ∧
      (r + u * ρ + κ * 3) - (r + u * ρ) = 3 * κ ∧ r + u * ρ = 0 ∧ 0 < 3 * κ := by
  intro ρ
  refine ⟨by ring, by ring, by ring, by simp only [ρ]; field_simp; ring, by linarith⟩

/-- C15-23: Φ†(Σ_J q_JP_J)Φ = Σ_J q_Jρ_J, so V = rρ + (u/2)ρ² + κ(6ρ₀ + 5ρ₁ + 3ρ₂). -/
theorem potential_form {n : Type*} [Fintype n] (P : Fin 4 → Matrix n n ℂ) (Φ : n → ℂ) (q : Fin 4 → ℂ) :
    star Φ ⬝ᵥ ((∑ J, q J • P J) *ᵥ Φ) = ∑ J, q J * (star Φ ⬝ᵥ (P J *ᵥ Φ)) := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl (fun J _ => by rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul])

/-- C15-26: |Z^{−1/2}e^{−ηK/2}|² = Z^{−1}e^{−ηK}. -/
theorem fresh_amplitude {Z η K : ℝ} (hZ : 0 < Z) :
    (Z ^ (-(1:ℝ)/2) * Real.exp (-η * K / 2)) ^ 2 = Z⁻¹ * Real.exp (-η * K) := by
  rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hZ.le, ← Real.exp_nat_mul]
  norm_num; rw [Real.rpow_neg_one]; ring_nf

/-! ### C15-28 … C15-30: marked Hessian and frame connection -/

section Hess
variable {q m : Type*} [Fintype q] [Fintype m] [DecidableEq q] [DecidableEq m]

/-- C15-28: with d = Lφ and LᵀL = I, φᵀH φ = dᵀ(LHLᵀ)d. -/
theorem hessian_pushforward (L : Matrix m q ℝ) (hL : Lᵀ * L = 1) (H : Matrix q q ℝ) (φ : q → ℝ) :
    φ ⬝ᵥ (H *ᵥ φ) = (L *ᵥ φ) ⬝ᵥ ((L * H * Lᵀ) *ᵥ (L *ᵥ φ)) := by
  have e1 : (L * H * Lᵀ) *ᵥ (L *ᵥ φ) = L *ᵥ (H *ᵥ φ) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hL, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  have e2 : (L *ᵥ φ) ᵥ* L = φ := by
    rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]
  rw [e1]; conv_rhs => rw [Matrix.dotProduct_mulVec, e2]

/-- C15-29: if LLᵀ = I is constant and L′ is the derivative, A = L L′ᵀ satisfies A + Aᵀ = 0
(entrywise product rule: L′Lᵀ + LL′ᵀ = 0). -/
theorem frame_connection_antisymm (L L' : Matrix m q ℝ) (h : L' * Lᵀ + L * L'ᵀ = 0) :
    (L * L'ᵀ)ᵀ = -(L * L'ᵀ) := by
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]; exact eq_neg_of_add_eq_zero_left h

theorem constraint_derivative (L : ℝ → Matrix m q ℝ) (L' : Matrix m q ℝ) (x : ℝ)
    (hL : ∀ i j, HasDerivAt (fun y => L y i j) (L' i j) x) (hc : ∀ y, L y * (L y)ᵀ = 1) :
    L' * (L x)ᵀ + L x * L'ᵀ = 0 := by
  ext i j
  have hd : HasDerivAt (fun y => (L y * (L y)ᵀ) i j) (∑ k, (L' i k * L x j k + L x i k * L' j k)) x := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hL i k).mul (hL j k)) |>.congr_deriv
      (Finset.sum_congr rfl (fun k _ => by ring))
  have hconst : (fun y => (L y * (L y)ᵀ) i j) = fun _ => (1 : Matrix m m ℝ) i j := by
    funext y; rw [hc y]
  rw [hconst] at hd
  have := hd.unique (hasDerivAt_const x _)
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply]
  rw [← Finset.sum_add_distrib]; exact this
end Hess

/-! ### C15-32, C15-34, C15-41, C15-44 -/

/-- C15-32: 2η(2/7)² = 8η/49, C(7,2) = 21, and (√(1 − u))²¹ = (1 − u)^{21/2}. -/
theorem return_contraction (η : ℝ) (hu : 8 * η / 49 ≤ 1) :
    2 * η * (2/7) ^ 2 = 8 * η / 49 ∧ Nat.choose 7 2 = 21 ∧
      Real.sqrt (1 - 8 * η / 49) ^ 21 = (1 - 8 * η / 49) ^ ((21:ℝ)/2) := by
  refine ⟨by ring, by decide, ?_⟩
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num

/-- C15-34 (split): if each class s of a distribution carries 48 equiprobable microstates with total P_s,
the microstate entropy is H(P) + ln 48 = 4 ln 2 + (H(P) + ln 3). -/
theorem sharing_split {S : Type*} [Fintype S] (P : S → ℝ) (hP : ∀ s, 0 < P s) (h1 : ∑ s, P s = 1) :
    -∑ s, (48:ℝ) * (P s / 48 * Real.log (P s / 48)) = 4 * Real.log 2 + (-∑ s, P s * Real.log (P s) + Real.log 3) := by
  have e : ∀ s, (48:ℝ) * (P s / 48 * Real.log (P s / 48)) = P s * Real.log (P s) - P s * Real.log 48 := by
    intro s; rw [Real.log_div (hP s).ne' (by norm_num)]; ring
  simp only [e, Finset.sum_sub_distrib, ← Finset.sum_mul, h1]
  rw [show (48:ℝ) = 2 ^ 4 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  push_cast; ring

/-- C15-41: injective 4-tuples of 7 labels ↔ (4-subsets) × S₄: C(7,4)·4! = 35·24 = 840 = P(7,4); ×2 = 1680. -/
theorem encoded_counts : Nat.choose 7 4 = 35 ∧ Nat.factorial 4 = 24 ∧ 35 * 24 = Nat.descFactorial 7 4 ∧
    35 * 24 * 2 = 1680 := by decide

/-- C15-44: ρ_cell = (I/16) ⊗ σ with σ = ⊕_s (P_s/3)I₃ has trace 1 and microstate probability P_s/48. -/
theorem encoded_cell {S : Type*} [Fintype S] (P : S → ℝ) (h1 : ∑ s, P s = 1) :
    (16 : ℝ) * (1/16) * ∑ s, 3 * (P s / 3) = 1 ∧ ∀ s, (1/16 : ℝ) * (P s / 3) = P s / 48 := by
  refine ⟨?_, fun s => by ring⟩
  rw [show ∑ s, 3 * (P s / 3) = ∑ s, P s from Finset.sum_congr rfl (fun s _ => by ring), h1]; norm_num

/-! ### C15-50 … C15-52, C15-75: hinge kernels (b = ln 2/(2π)) -/

def bH : ℝ := Real.log 2 / (2 * π)

theorem two_pi_b : 2 * π * bH = Real.log 2 := by unfold bH; field_simp

/-- C15-50: K(θ) = e^{−bθ} is a semigroup and K(2π) = 1/2 (ρ_h = I/2). -/
theorem hinge_semigroup (a c : ℝ) :
    Real.exp (-bH * a) * Real.exp (-bH * c) = Real.exp (-bH * (a + c)) ∧ Real.exp (-bH * (2 * π)) = 1/2 := by
  refine ⟨by rw [← Real.exp_add]; ring_nf, ?_⟩
  rw [show -bH * (2 * π) = -Real.log 2 by rw [← two_pi_b]; ring, Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

/-- C15-51: angles summing to 2π − δ give hinge trace 2e^{−b(2π−δ)} = e^{bδ}, and N channels give e^{bNδ}. -/
theorem hinge_trace (δ : ℝ) (N : ℕ) :
    2 * Real.exp (-bH * (2 * π - δ)) = Real.exp (bH * δ) ∧ Real.exp (bH * δ) ^ N = Real.exp (bH * N * δ) := by
  constructor
  · rw [show -bH * (2 * π - δ) = -(2 * π * bH) + bH * δ by ring, two_pi_b, Real.exp_add, Real.exp_neg,
      Real.exp_log (by norm_num)]; ring
  · rw [← Real.exp_nat_mul]; ring_nf

/-- C15-52: Tr K(2πn) = 2·2^{−n} = 2^{1−n} = Tr ρ_hⁿ, and Tr ρ_cellⁿ = 16·16^{−n} Tr σⁿ = 2^{4(1−n)} Tr σⁿ. -/
theorem replica_traces (n : ℝ) (trσ : ℝ) :
    2 * Real.exp (-bH * (2 * π * n)) = (2:ℝ) ^ (1 - n) ∧ 2 * (1/2 : ℝ) ^ n = (2:ℝ) ^ (1 - n) ∧
      16 * (1/16 : ℝ) ^ n * trσ = (2:ℝ) ^ (4 * (1 - n)) * trσ := by
  have h2 : (0:ℝ) < 2 := by norm_num
  refine ⟨?_, ?_, ?_⟩
  · have e : Real.exp (-bH * (2 * π * n)) = (2:ℝ) ^ (-n) := by
      rw [show -bH * (2 * π * n) = Real.log 2 * (-n) by rw [← two_pi_b]; ring, Real.rpow_def_of_pos h2]
    rw [e, Real.rpow_sub h2, Real.rpow_one, Real.rpow_neg h2.le]; field_simp
  · rw [Real.rpow_sub h2, Real.rpow_one, Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow]; ring
  · have e : (2:ℝ) ^ (4 * (1 - n)) = 16 / 16 ^ n := by
      rw [show (4:ℝ) * (1 - n) = 4 - 4 * n by ring, Real.rpow_sub h2, Real.rpow_mul h2.le]; norm_num
    rw [e, Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow]; ring

/-- C15-75: B(θ) = ρ_h^{−1/2}K(θ) = √2 e^{−bθ} = e^{b(π − θ)}, and Tr[ρ_h B(θ₁)B(θ₂)] = e^{b(2π − θ₁ − θ₂)}. -/
theorem half_turn (θ1 θ2 : ℝ) :
    Real.sqrt 2 * Real.exp (-bH * θ1) = Real.exp (bH * (π - θ1)) ∧
      2 * (1/2) * (Real.exp (bH * (π - θ1)) * Real.exp (bH * (π - θ2))) = Real.exp (bH * (2 * π - θ1 - θ2)) := by
  have hs : Real.sqrt 2 = Real.exp (bH * π) := by
    rw [show bH * π = Real.log 2 / 2 by unfold bH; field_simp, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num)]
    ring_nf
  refine ⟨by rw [hs, ← Real.exp_add]; ring_nf, by rw [← Real.exp_add]; ring_nf⟩

/-! ### C15-53 … C15-56: channel-area chain -/

/-- C15-53 (algebra): −bΣN_hδ_h = −(b/(2A_ch))·2Σ A_ch N_hδ_h, and equating −(b/(2A_ch))R with
−(c³/(16πħG))R (R ≠ 0) gives ħG/c³ = A_ch/(8πb) = A_ch/(4 ln 2). -/
theorem channel_area_relation {Ach R k : ℝ} (hA : Ach ≠ 0) (hR : R ≠ 0)
    (h : -(bH / (2 * Ach)) * R = -(1 / (16 * π * k)) * R) (hk : k ≠ 0) :
    k = Ach / (8 * π * bH) ∧ 8 * π * bH = 4 * Real.log 2 := by
  have hb : bH ≠ 0 := by unfold bH; have := Real.log_pos one_lt_two; positivity
  have h' : bH / (2 * Ach) = 1 / (16 * π * k) := by
    have := mul_right_cancel₀ hR h; linarith
  refine ⟨?_, by rw [show 8 * π * bH = 4 * (2 * π * bH) by ring, two_pi_b]⟩
  field_simp at h' ⊢; linarith

/-- C15-54: A_N = 24πγNL² equals Z_A(N)·8πγL²√(3N(3N+1)) with Z_A = √(3N/(3N+1)). -/
theorem flux_area (N : ℕ) (hN : 1 ≤ N) (γ L : ℝ) :
    24 * π * γ * N * L ^ 2 = Real.sqrt (3 * N / (3 * N + 1)) * (8 * π * γ * L ^ 2 * Real.sqrt (3 * N * (3 * N + 1))) := by
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hprod : Real.sqrt (3 * N / (3 * N + 1)) * Real.sqrt (3 * N * (3 * N + 1)) = 3 * N := by
    rw [← Real.sqrt_mul (by positivity),
      show 3 * (N:ℝ) / (3 * N + 1) * (3 * N * (3 * N + 1)) = (3 * N) ^ 2 by field_simp, Real.sqrt_sq (by positivity)]
  calc 24 * π * γ * N * L ^ 2
      = (8 * π * γ * L ^ 2) * (Real.sqrt (3 * N / (3 * N + 1)) * Real.sqrt (3 * N * (3 * N + 1))) := by
        rw [hprod]; ring
    _ = _ := by ring

/-- C15-55, C15-56: G₀/G* = 24πγ/(4 ln 2) = 6πγ/ln 2, which is 1 iff γ = ln 2/(6π); then A_ch = 4 ln 2 L². -/
theorem matched_immirzi (γ : ℝ) :
    24 * π * γ / (4 * Real.log 2) = 6 * π * γ / Real.log 2 ∧
      (6 * π * γ / Real.log 2 = 1 ↔ γ = Real.log 2 / (6 * π)) ∧
      24 * π * (Real.log 2 / (6 * π)) = 4 * Real.log 2 := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hp : π ≠ 0 := Real.pi_ne_zero
  refine ⟨by field_simp; ring, ⟨fun h => by field_simp at h ⊢; linarith, fun h => by rw [h]; field_simp⟩,
    by field_simp; ring⟩

/-! ### C15-63, C15-64, C15-65 … C15-68 -/

/-- C15-63: with D†D = I and (U ⊗ I)E = EU, U_phys = D(U⊗I)D† satisfies U_phys (DE) = (DE)U. -/
theorem transport_intertwines {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a]
    (D : Matrix a a ℂ) (hD : Dᴴ * D = 1) (UI : Matrix a a ℂ) (E : Matrix a b ℂ) (U : Matrix b b ℂ)
    (hE : UI * E = E * U) : (D * UI * Dᴴ) * (D * E) = (D * E) * U := by
  calc (D * UI * Dᴴ) * (D * E) = D * UI * (Dᴴ * D) * E := by simp only [Matrix.mul_assoc]
    _ = D * (UI * E) := by rw [hD, Matrix.mul_one, Matrix.mul_assoc]
    _ = (D * E) * U := by rw [hE, Matrix.mul_assoc]

/-- C15-64: for symmetric K on Fin 6, Σ K_AB x_Ax_B = Σ c_Ax_A² + Σ_{A<B} c_AB(x_A + x_B)². -/
theorem two_direction (K : Matrix (Fin 6) (Fin 6) ℝ) (hK : Kᵀ = K) (x : Fin 6 → ℝ) :
    ∑ A, ∑ B, K A B * x A * x B =
      ∑ A, (K A A - ∑ B, (if B = A then 0 else K A B)) * x A ^ 2 +
        ∑ A, ∑ B, (if A < B then K A B * (x A + x B) ^ 2 else 0) := by
  have hs : ∀ A B, K B A = K A B := fun A B => by rw [← Matrix.transpose_apply K A B, hK]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  simp (config := {decide := true}) only [Fin.lt_def, Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_two,
    Fin.val_succ, if_true, if_false]
  norm_num
  rw [hs 0 1, hs 0 2, hs 0 3, hs 0 4, hs 0 5, hs 1 2, hs 1 3, hs 1 4, hs 1 5, hs 2 3, hs 2 4, hs 2 5,
    hs 3 4, hs 3 5, hs 4 5]
  ring

/-- C15-65 (counts), C15-67, C15-68. -/
theorem lift_counts : 3 ^ 6 = 729 ∧ 2 ^ 12 = 4096 ∧ Nat.choose 6 2 = 15 := by decide

theorem port_parity (V E : ℕ) (h : 2 * E ≤ 4 * V) : Even (4 * V - 2 * E) := by
  refine ⟨2 * V - E, by omega⟩

theorem odd_mixed (n : ℕ) (h : Even (1 + 3 * n)) : Odd n := by
  rcases Nat.even_or_odd n with hn | hn
  · exfalso; obtain ⟨k, hk⟩ := hn; obtain ⟨m, hm⟩ := h; omega
  · exact hn

/-- C15-66, C15-68: √(4α − 1)/√3 = n/m ⇔ α = (1 + 3(n/m)²)/4 (for α ≥ 1/4, n/m ≥ 0); n/m = 3 gives α = 7. -/
theorem cdt_asymmetry {α r : ℝ} (hα : 1/4 ≤ α) (hr : 0 ≤ r) :
    Real.sqrt (4 * α - 1) / Real.sqrt 3 = r ↔ α = (1 + 3 * r ^ 2) / 4 := by
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [div_eq_iff h3.ne']
  constructor
  · intro h
    have := congrArg (· ^ 2) h
    simp only [mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ 4 * α - 1 by linarith), Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)] at this
    linarith
  · intro h
    rw [← Real.sqrt_sq hr, ← Real.sqrt_mul (sq_nonneg r)]
    congr 1; rw [h]; ring

theorem alpha_seven : (1 + 3 * (3:ℝ) ^ 2) / 4 = 7 := by norm_num

/-! ### C15-74, C15-77, C15-78 -/

/-- C15-74: if C ≤ P (PC = CP = C) are projections then (P − C)² = P − C, and for Px = x,
(P − C)x = 0 iff Cx = x. -/
theorem block_selection {n : Type*} [Fintype n] [DecidableEq n] (P C : Matrix n n ℂ) (hP : P * P = P)
    (hC : C * C = C) (hPC : P * C = C) (hCP : C * P = C) (x : n → ℂ) (hx : P *ᵥ x = x) :
    (P - C) * (P - C) = P - C ∧ ((P - C) *ᵥ x = 0 ↔ C *ᵥ x = x) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hP, hPC, hCP, hC]; abel
  · rw [Matrix.sub_mulVec, hx, sub_eq_zero]; exact eq_comm

/-- C15-77: T̃(g′,g) = √(C(g′)C(g))T(g′,g) satisfies T̃⁽²⁾ = T̃T̃, and T̃ᵀT̃ is positive semidefinite. -/
theorem sewing {g : Type*} [Fintype g] (C : g → ℝ) (hC : ∀ x, 0 < C x) (T : Matrix g g ℝ) (g2 g0 : g) :
    Real.sqrt (C g2 * C g0) * ∑ g1, C g1 * T g2 g1 * T g1 g0 =
      ∑ g1, (Real.sqrt (C g2 * C g1) * T g2 g1) * (Real.sqrt (C g1 * C g0) * T g1 g0) := by
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun g1 _ => ?_)
  have h1 : Real.sqrt (C g2 * C g1) * Real.sqrt (C g1 * C g0) = C g1 * Real.sqrt (C g2 * C g0) := by
    rw [← Real.sqrt_mul (by have := hC g2; have := hC g1; positivity),
      show C g2 * C g1 * (C g1 * C g0) = C g1 ^ 2 * (C g2 * C g0) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hC g1).le]
  calc Real.sqrt (C g2 * C g0) * (C g1 * T g2 g1 * T g1 g0)
      = (C g1 * Real.sqrt (C g2 * C g0)) * (T g2 g1 * T g1 g0) := by ring
    _ = _ := by rw [← h1]; ring

theorem sewing_psd {g : Type*} [Fintype g] (Tt : Matrix g g ℝ) : (Ttᴴ * Tt).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self Tt

/-- C15-78: (J T J†)ⁿ⁺¹ = J Tⁿ⁺¹ J† for an isometry J. -/
theorem encoded_powers {a h : Type*} [Fintype a] [Fintype h] [DecidableEq a] [DecidableEq h]
    (J : Matrix h a ℂ) (hJ : Jᴴ * J = 1) (T : Matrix a a ℂ) (n : ℕ) :
    (J * T * Jᴴ) ^ (n + 1) = J * T ^ (n + 1) * Jᴴ :=
  (Entropic.AppP.isometry_powers J hJ T n).1

end Entropic.AppQ
