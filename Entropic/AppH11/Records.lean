import Entropic.AppH10.Pullback
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-! Appendix H.11: records, overlaps, channels, Kraus dilations, isometric lifts
(ledger C09-02 … -05, -07, -08, -39 … -42, -72, -74, -78, -93, -94, -21). -/

noncomputable section
namespace Entropic.AppH11
open Matrix
open scoped Kronecker ComplexOrder
open InnerProductSpace

section Overlap
variable {s r : Type*} [Fintype s] [Fintype r]

/-- Product vector u ⊗ e. -/
def kvec (u : s → ℂ) (e : r → ℂ) : s × r → ℂ := fun p => u p.1 * e p.2

/-- Partial trace over the record factor. -/
def ptrE (X : Matrix (s × r) (s × r) ℂ) : Matrix s s ℂ := Matrix.of fun i j => ∑ k, X (i, k) (j, k)

/-- C09-03, C09-07: Tr_E |u⊗e_x⟩⟨v⊗e_y| = ⟨e_y|e_x⟩ |u⟩⟨v|; the record overlap multiplies the
coherence, and orthogonal records (⟨e_Q|e_V⟩ = 0) kill the off-diagonal block. -/
theorem ptr_record (u v : s → ℂ) (ex ey : r → ℂ) :
    ptrE (Matrix.vecMulVec (kvec u ex) (star (kvec v ey))) =
      (∑ k, star (ey k) * ex k) • Matrix.vecMulVec u (star v) := by
  ext i j
  simp only [ptrE, kvec, Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply, star_mul',
    Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- C09-04: n successive updates with multipliers γ_k give C(n) = (∏ γ_k) C(0). -/
theorem overlap_product (γ : ℕ → ℂ) (C : ℕ → ℂ) (h : ∀ n, C (n + 1) = γ (n + 1) * C n) (n : ℕ) :
    C n = (∏ k ∈ Finset.range n, γ (k + 1)) * C 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [h, ih, Finset.prod_range_succ]; ring

end Overlap

section Unit
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- C09-05 (iii), C09-08: for unit vectors |⟨e_y|e_x⟩| ≤ 1, and ⟨e_y|e_x⟩ = 1 iff e_x = e_y;
(i) orthogonal records give γ = 0, (ii) equal records give γ = 1. -/
theorem overlap_cases {ex ey : E} (hx : ‖ex‖ = 1) (hy : ‖ey‖ = 1) :
    ‖⟪ey, ex⟫_ℂ‖ ≤ 1 ∧ (⟪ey, ex⟫_ℂ = 1 ↔ ey = ex) ∧ ⟪ex, ex⟫_ℂ = 1 := by
  refine ⟨?_, inner_eq_one_iff_of_norm_eq_one hy hx, ?_⟩
  · calc ‖⟪ey, ex⟫_ℂ‖ ≤ ‖ey‖ * ‖ex‖ := norm_inner_le_norm _ _
      _ = 1 := by rw [hx, hy, one_mul]
  · rw [inner_self_eq_norm_sq_to_K, hx]; simp

/-- C09-39: for an orthogonal projector Π, ‖Πψ‖² = ⟨ψ, Πψ⟩; for a complete family Σ‖Π_aψ‖² = ‖ψ‖². -/
theorem projector_prob (Pr : E →ₗ[ℂ] E) (hsym : Pr.IsSymmetric) (hid : ∀ v, Pr (Pr v) = Pr v) (ψ : E) :
    ((‖Pr ψ‖ ^ 2 : ℝ) : ℂ) = ⟪ψ, Pr ψ⟫_ℂ := by
  have h1 : ⟪Pr ψ, Pr ψ⟫_ℂ = ⟪ψ, Pr ψ⟫_ℂ := by rw [hsym, hid]
  rw [← h1, inner_self_eq_norm_sq_to_K]; norm_cast

theorem projector_complete {α : Type*} (s : Finset α) (Pr : α → E →ₗ[ℂ] E) (hsym : ∀ a, (Pr a).IsSymmetric)
    (hid : ∀ a v, Pr a (Pr a v) = Pr a v) (hsum : ∀ v, ∑ a ∈ s, Pr a v = v) (ψ : E) :
    ((∑ a ∈ s, ‖Pr a ψ‖ ^ 2 : ℝ) : ℂ) = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
  push_cast
  rw [Finset.sum_congr rfl (fun a _ => by
    have := projector_prob (Pr a) (hsym a) (hid a) ψ; push_cast at this; exact this)]
  rw [← inner_sum, hsum, inner_self_eq_norm_sq_to_K]; rfl

end Unit

section Channels
variable {n s r : Type*} [Fintype n] [Fintype s] [Fintype r] [DecidableEq n] [DecidableEq s]
  [DecidableEq r]

/-- C09-40: Tr(|ψ⟩⟨ψ| Π) = ⟨ψ|Π|ψ⟩, so p(a) = Σ_r p_r⟨ψ_r|Π_a|ψ_r⟩ = Tr(ρΠ_a). -/
theorem pure_trace (ψ : n → ℂ) (Pr : Matrix n n ℂ) :
    (Matrix.vecMulVec ψ (star ψ) * Pr).trace = star ψ ⬝ᵥ (Pr *ᵥ ψ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)

theorem mixed_prob {ι : Type*} (S : Finset ι) (p : ι → ℂ) (ψ : ι → n → ℂ) (Pr : Matrix n n ℂ) :
    ((∑ t ∈ S, p t • Matrix.vecMulVec (ψ t) (star (ψ t))) * Pr).trace =
      ∑ t ∈ S, p t * (star (ψ t) ⬝ᵥ (Pr *ᵥ ψ t)) := by
  rw [Finset.sum_mul, Matrix.trace_sum]
  exact Finset.sum_congr rfl (fun t _ => by rw [Matrix.smul_mul, Matrix.trace_smul, pure_trace]; rfl)

/-- Composite form: Tr(ρ(Π ⊗ I)) = Tr(ρ_S Π) with ρ_S = Tr_E ρ. -/
theorem reduced_prob (ρ : Matrix (s × r) (s × r) ℂ) (Pr : Matrix s s ℂ) :
    (ρ * (Pr ⊗ₖ (1 : Matrix r r ℂ))).trace = (ptrE ρ * Pr).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, ptrE, Matrix.of_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  exact Finset.sum_comm

/-- Block of a bipartite operator. -/
def blk (X : Matrix (s × r) (s × r) ℂ) (i j : s) : Matrix r r ℂ := Matrix.of fun k l => X (i, k) (j, l)

/-- id ⊗ E for a linear map E on the second factor. -/
def idTensor (E : Matrix r r ℂ →ₗ[ℂ] Matrix r r ℂ) (X : Matrix (s × r) (s × r) ℂ) :
    Matrix (s × r) (s × r) ℂ := Matrix.of fun p q => E (blk X p.1 q.1) p.2 q.2

theorem idTensor_kron (E : Matrix r r ℂ →ₗ[ℂ] Matrix r r ℂ) (A : Matrix s s ℂ) (B : Matrix r r ℂ) :
    idTensor E (A ⊗ₖ B) = A ⊗ₖ E B := by
  ext ⟨i, k⟩ ⟨j, l⟩
  have : blk (A ⊗ₖ B) i j = A i j • B := by ext k l; simp [blk, Matrix.kroneckerMap_apply]
  simp [idTensor, this, Matrix.kroneckerMap_apply]

/-- C09-78: background renewal by any trace-preserving E leaves the retained marginal unchanged. -/
theorem idTensor_marginal (E : Matrix r r ℂ →ₗ[ℂ] Matrix r r ℂ) (hE : ∀ Y, (E Y).trace = Y.trace)
    (X : Matrix (s × r) (s × r) ℂ) : ptrE (idTensor E X) = ptrE X := by
  ext i j
  exact hE (blk X i j)

/-- C09-02: for the replacement channel, (id ⊗ E_*)(ρ) = Tr_A ρ ⊗ ρ_* (entanglement breaking). -/
theorem replace_tensor (σ : Matrix r r ℂ) (X : Matrix (s × r) (s × r) ℂ) :
    idTensor ((LinearMap.lsmul ℂ (Matrix r r ℂ)).flip σ ∘ₗ Matrix.traceLinearMap r ℂ ℂ) X = ptrE X ⊗ₖ σ := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [idTensor, blk, ptrE, Matrix.kroneckerMap_apply, Matrix.trace, Matrix.diag, Matrix.sum_apply,
    Finset.sum_mul]

/-- C09-41: Kraus operators M_a := (I ⊗ ⟨a|)U(I ⊗ |0⟩) of a unitary dilation satisfy Σ_a M_a†M_a = I. -/
def kraus (U : Matrix (s × r) (s × r) ℂ) (r0 a : r) : Matrix s s ℂ := Matrix.of fun i j => U (i, a) (j, r0)

theorem kraus_complete (U : Matrix (s × r) (s × r) ℂ) (hU : Uᴴ * U = 1) (r0 : r) :
    ∑ a, (kraus U r0 a)ᴴ * kraus U r0 a = 1 := by
  ext i j
  have := congrFun (congrFun hU (i, r0)) (j, r0)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.one_apply,
    Prod.mk.injEq, and_true] at this
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, kraus, Matrix.of_apply,
    Matrix.one_apply]
  rw [Finset.sum_comm]; exact this

/-- U(|ψ⟩|0⟩) = Σ_a M_a|ψ⟩|a⟩. -/
theorem kraus_dilation (U : Matrix (s × r) (s × r) ℂ) (r0 : r) (ψ : s → ℂ) :
    U *ᵥ (kvec ψ (Pi.single r0 1)) = fun p => (kraus U r0 p.2 *ᵥ ψ) p.1 := by
  funext ⟨i, a⟩
  simp [Matrix.mulVec, dotProduct, kvec, kraus, Fintype.sum_prod_type, Pi.single_apply]

/-- C09-42: for Σ_k M_k†M_k = I, V ψ := Σ_k M_kψ ⊗ |k⟩ is an isometry: V†V = I. -/
def stinespring (M : r → Matrix s s ℂ) : Matrix (s × r) s ℂ := Matrix.of fun p j => M p.2 p.1 j

theorem stinespring_isometry (M : r → Matrix s s ℂ) (hM : ∑ k, (M k)ᴴ * M k = 1) :
    (stinespring M)ᴴ * stinespring M = 1 := by
  rw [← hM]; ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, stinespring, Matrix.of_apply, Matrix.sum_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]

end Channels

/-! ### Proper-time semigroup (C09-72) and two-source ratio (C09-74) -/

section Semigroup
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- C09-72: T(s) = exp(−ε s P) and U[γ] = exp(−iεPτ_γ/τ_*) compose additively. -/
theorem proper_time_semigroup (P : Matrix n n ℂ) (ε s1 s2 : ℂ) :
    NormedSpace.exp ((-(ε * (s1 + s2))) • P) =
      NormedSpace.exp ((-(ε * s1)) • P) * NormedSpace.exp ((-(ε * s2)) • P) := by
  rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl P).smul_left _ |>.smul_right _)]
  congr 1; rw [← add_smul]; ring_nf

end Semigroup

/-- C09-74: if ℓᵢ(T) = ℓᵢ is geometry independent then Z(m₁,m₂)Z(0,0)/(Z(m₁,0)Z(0,m₂)) = 1. -/
theorem fixed_edge_ratio {ι : Type*} (S : Finset ι) (p : ι → ℝ) (l1 l2 m1 m2 : ℝ)
    (hZ : 0 < ∑ T ∈ S, p T) :
    (∑ T ∈ S, p T * Real.exp (-m1 * l1 - m2 * l2)) * (∑ T ∈ S, p T * Real.exp (-0 * l1 - 0 * l2)) /
      ((∑ T ∈ S, p T * Real.exp (-m1 * l1 - 0 * l2)) * (∑ T ∈ S, p T * Real.exp (-0 * l1 - m2 * l2))) = 1 := by
  simp only [← Finset.sum_mul]
  have e1 : Real.exp (-m1 * l1 - m2 * l2) = Real.exp (-m1 * l1) * Real.exp (-m2 * l2) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1]; simp only [zero_mul, neg_zero, sub_zero, zero_sub, Real.exp_zero, mul_one]
  have h1 := Real.exp_pos (-m1 * l1); have h2 := Real.exp_pos (-m2 * l2)
  field_simp

/-! ### Isometric lifts (C09-93) and the moving-subspace product rule (C09-94) -/

section Lift
variable {c f : Type*} [Fintype c] [Fintype f] [DecidableEq c] [DecidableEq f]

def lift (J : Matrix f c ℂ) (A : Matrix c c ℂ) : Matrix f f ℂ := J * A * Jᴴ

/-- C09-93: for J†J = I, P = JJ† is an orthogonal projector, ι(A)ι(B) = ι(AB), J†ι(A)J = A,
Tr ι(A) = Tr A, ι(I) = P, ι preserves positivity, and intertwining passes to powers. -/
theorem lift_identities (J : Matrix f c ℂ) (hJ : Jᴴ * J = 1) (A B : Matrix c c ℂ) :
    (J * Jᴴ) * (J * Jᴴ) = J * Jᴴ ∧ (J * Jᴴ)ᴴ = J * Jᴴ ∧ lift J A * lift J B = lift J (A * B) ∧
      Jᴴ * lift J A * J = A ∧ (lift J A).trace = A.trace ∧ lift J 1 = J * Jᴴ := by
  refine ⟨?_, by simp [Matrix.conjTranspose_mul], ?_, ?_, ?_, by simp [lift]⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ, hJ, Matrix.one_mul]
  · unfold lift
    rw [show J * A * Jᴴ * (J * B * Jᴴ) = J * A * (Jᴴ * J) * B * Jᴴ by simp only [Matrix.mul_assoc], hJ,
      Matrix.mul_one, Matrix.mul_assoc J A B]
  · unfold lift
    rw [show Jᴴ * (J * A * Jᴴ) * J = (Jᴴ * J) * A * (Jᴴ * J) by simp only [Matrix.mul_assoc], hJ]; simp
  · unfold lift; rw [Matrix.trace_mul_cycle, hJ, Matrix.one_mul]

theorem lift_posSemidef (J : Matrix f c ℂ) {A : Matrix c c ℂ} (hA : A.PosSemidef) : (lift J A).PosSemidef := by
  unfold lift
  simpa using hA.mul_mul_conjTranspose_same J

theorem lift_intertwine_pow (J : Matrix f c ℂ) (Hf : Matrix f f ℂ) (Hc : Matrix c c ℂ)
    (h : Hf * J = J * Hc) (k : ℕ) : Hf ^ k * J = J * Hc ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, h, Matrix.mul_assoc, ← pow_succ']

/-- C09-94: ∂_s(J†H J) = J†(∂H)J + (∂J)†HJ + J†H(∂J), entrywise. -/
theorem moving_subspace (J : ℝ → Matrix f c ℂ) (H : ℝ → Matrix f f ℂ) (J' : Matrix f c ℂ)
    (H' : Matrix f f ℂ) (s0 : ℝ) (hJ : ∀ i j, HasDerivAt (fun s => J s i j) (J' i j) s0)
    (hH : ∀ i j, HasDerivAt (fun s => H s i j) (H' i j) s0) (i j : c) :
    HasDerivAt (fun s => ((J s)ᴴ * H s * J s) i j)
      (((J s0)ᴴ * H' * J s0 + J'ᴴ * H s0 * J s0 + (J s0)ᴴ * H s0 * J') i j) s0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.add_apply]
  have hterm : ∀ l k, HasDerivAt (fun s => star (J s k i) * H s k l * J s l j)
      (star (J s0 k i) * H' k l * J s0 l j + star (J' k i) * H s0 k l * J s0 l j +
        star (J s0 k i) * H s0 k l * J' l j) s0 := by
    intro l k
    have h1 := ((hJ k i).star.mul (hH k l)).mul (hJ l j)
    convert h1 using 1
    simp only [Pi.mul_apply]; ring
  have := HasDerivAt.fun_sum (u := Finset.univ) (fun l _ => HasDerivAt.fun_sum (u := Finset.univ)
    (fun k _ => hterm l k))
  convert this using 1
  · funext y; simp only [Finset.sum_mul]
  · simp only [Finset.sum_mul, ← Finset.sum_add_distrib]

end Lift

/-! ### Effective Hamiltonian is Hermitian (C09-21) -/

section Heff
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- C09-21: if UU† = I along a differentiable family (so U′U† + UU′† = 0) then H_eff = iħU′U† is
Hermitian, and ψ = Uψ₀ obeys iħψ′ = H_eff ψ when U†U = I. -/
theorem heff_hermitian (U D : Matrix n n ℂ) (ħ : ℝ) (hD : D * Uᴴ + U * Dᴴ = 0) :
    ((Complex.I * ħ) • (D * Uᴴ))ᴴ = (Complex.I * ħ) • (D * Uᴴ) := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have : U * Dᴴ = -(D * Uᴴ) := eq_neg_of_add_eq_zero_right hD
  rw [this, smul_neg, ← neg_smul]
  congr 1; simp [Complex.conj_ofReal]

theorem heff_schrodinger (U D : Matrix n n ℂ) (hU : Uᴴ * U = 1) (ψ0 : n → ℂ) :
    D *ᵥ ψ0 = (D * Uᴴ) *ᵥ (U *ᵥ ψ0) := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hU, Matrix.mul_one]

/-- The unitarity derivative: from entrywise derivatives of U(s), UU† = I for all s gives
U′U† + UU′† = 0. -/
theorem unitary_deriv (U : ℝ → Matrix n n ℂ) (D : Matrix n n ℂ) (s0 : ℝ)
    (hU : ∀ s, U s * (U s)ᴴ = 1) (hD : ∀ i j, HasDerivAt (fun s => U s i j) (D i j) s0) :
    D * (U s0)ᴴ + U s0 * Dᴴ = 0 := by
  ext i j
  have hconst : HasDerivAt (fun s => (U s * (U s)ᴴ) i j) 0 s0 := by
    have : (fun s => (U s * (U s)ᴴ) i j) = fun _ => (1 : Matrix n n ℂ) i j := by funext s; rw [hU]
    rw [this]; exact hasDerivAt_const _ _
  have hprod : HasDerivAt (fun s => (U s * (U s)ᴴ) i j)
      (∑ k, (D i k * star (U s0 j k) + U s0 i k * star (D j k))) s0 := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact HasDerivAt.fun_sum (fun k _ => (hD i k).mul (hD j k).star)
  have := hconst.unique hprod
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.zero_apply,
    ← Finset.sum_add_distrib]
  exact this.symm

end Heff

end Entropic.AppH11
