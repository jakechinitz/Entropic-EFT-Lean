import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Appendix G / Section 22: decoherent histories, records, instruments, no-signaling and the
replacement channel, in finite dimension (ledger C06-38 … -47, C03-11, -12, -15, -16, -17). -/

noncomputable section
namespace Entropic.AppFG.Histories
open Matrix Finset
open scoped ComplexOrder Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Op (ι : Type*) := Matrix ι ι ℂ

/-- Decoherence functional D(h, h′) = Tr(C_h ρ C_{h′}†). -/
def dec {Hs : Type*} (C : Hs → Op ι) (ρ : Op ι) (h h' : Hs) : ℂ := trace (C h * ρ * (C h')ᴴ)

/-- C06-38: D is Hermitian. -/
theorem dec_hermitian {Hs : Type*} (C : Hs → Op ι) {ρ : Op ι} (hρ : ρᴴ = ρ) (h h' : Hs) :
    dec C ρ h' h = star (dec C ρ h h') := by
  unfold dec
  rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hρ,
    Matrix.mul_assoc]

/-- C06-38: D is a positive-semidefinite (Gram) kernel; in particular p(h) = D(h,h) ≥ 0. -/
theorem dec_psd {Hs : Type*} [Fintype Hs] (C : Hs → Op ι) {ρ : Op ι} (hρ : ρ.PosSemidef)
    (z : Hs → ℂ) : 0 ≤ ∑ h, ∑ h', star (z h) * z h' * dec C ρ h h' := by
  set X : Op ι := ∑ h, star (z h) • C h
  have hX : trace (X * ρ * Xᴴ) = ∑ h, ∑ h', star (z h) * z h' * dec C ρ h h' := by
    simp only [X, conjTranspose_sum, conjTranspose_smul, star_star, Finset.sum_mul, Finset.mul_sum,
      smul_mul_assoc, mul_smul_comm, trace_sum, trace_smul, smul_eq_mul, dec]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  have := (hρ.mul_mul_conjTranspose_same X).trace_nonneg
  rwa [hX] at this

theorem prob_nonneg {Hs : Type*} (C : Hs → Op ι) {ρ : Op ι} (hρ : ρ.PosSemidef) (h : Hs) :
    0 ≤ dec C ρ h h :=
  (hρ.mul_mul_conjTranspose_same (C h)).trace_nonneg

/-- C06-39: p(A) = Tr(C_A ρ C_A†) = Σ_{h,h′∈A} D(h,h′); with decoherence it is Σ_{h∈A} p(h). -/
theorem coarse_grain {Hs : Type*} (C : Hs → Op ι) (ρ : Op ι) (A : Finset Hs) :
    trace ((∑ h ∈ A, C h) * ρ * (∑ h ∈ A, C h)ᴴ) = ∑ h ∈ A, ∑ h' ∈ A, dec C ρ h h' := by
  simp only [conjTranspose_sum, Finset.sum_mul, Finset.mul_sum, trace_sum, dec]
  rw [Finset.sum_comm]

theorem coarse_grain_decoherent {Hs : Type*} [DecidableEq Hs] (C : Hs → Op ι) (ρ : Op ι)
    (A : Finset Hs) (hdec : ∀ h ∈ A, ∀ h' ∈ A, h ≠ h' → dec C ρ h h' = 0) :
    trace ((∑ h ∈ A, C h) * ρ * (∑ h ∈ A, C h)ᴴ) = ∑ h ∈ A, dec C ρ h h := by
  rw [coarse_grain]
  refine Finset.sum_congr rfl (fun h hh => ?_)
  rw [Finset.sum_eq_single h (fun h' hh' hne => hdec h hh h' hh' (Ne.symm hne)) (fun h' => absurd hh h')]

/-- Exhaustive intermediate alternatives collapse: Σ_α A P_α B = A B when Σ_α P_α = 1. -/
theorem exhaustive {α : Type*} [Fintype α] (A B : Op ι) (P : α → Op ι) (hP : ∑ a, P a = 1) :
    ∑ a, A * P a * B = A * B := by
  rw [← Finset.sum_mul, ← Finset.mul_sum, hP, Matrix.mul_one]

/-- C06-40: if the histories ending in the record P_P sum to P_P U and are decoherent, then
p(P) = Σ p(h) = Tr(P_P ρ_now) with ρ_now = UρU†. -/
theorem record_born {Hs : Type*} [DecidableEq Hs] (C : Hs → Op ι) (ρ U P : Op ι) (A : Finset Hs)
    (hsum : ∑ h ∈ A, C h = P * U) (hP : P * P = P) (hPh : Pᴴ = P)
    (hdec : ∀ h ∈ A, ∀ h' ∈ A, h ≠ h' → dec C ρ h h' = 0) :
    ∑ h ∈ A, dec C ρ h h = trace (P * (U * ρ * Uᴴ)) := by
  rw [← coarse_grain_decoherent C ρ A hdec, hsum, conjTranspose_mul, hPh]
  rw [show P * U * ρ * (Uᴴ * P) = (P * U * ρ * Uᴴ) * P by simp only [Matrix.mul_assoc],
    trace_mul_comm]
  simp only [← Matrix.mul_assoc, hP]

/-! ### Conditional weights (C06-41, -42, -44, C03-11, -12) -/

/-- C06-41/C03-11: p(h|P) = p(h)/p(P) is a probability on H_P. -/
theorem conditional_normalized {Hs : Type*} (A : Finset Hs) (p : Hs → ℝ) (hp : ∀ h, 0 ≤ p h)
    (hP : 0 < ∑ h ∈ A, p h) :
    (∀ h, 0 ≤ p h / ∑ h ∈ A, p h) ∧ ∑ h ∈ A, p h / ∑ h' ∈ A, p h' = 1 := by
  refine ⟨fun h => div_nonneg (hp h) hP.le, ?_⟩
  rw [← Finset.sum_div, div_self hP.ne']

/-- C06-42: with D(h,P) = −ln p(h) on the support (and weight 0 off it),
p(h|P) = e^{−D(h,P)}/Σ e^{−D(h′,P)}. -/
def boltz (w : ℝ) : ℝ := if w = 0 then 0 else Real.exp (-(-Real.log w))

theorem boltz_eq {w : ℝ} (hw : 0 ≤ w) : boltz w = w := by
  unfold boltz; split_ifs with h
  · exact h.symm
  · rw [neg_neg, Real.exp_log (lt_of_le_of_ne hw (Ne.symm h))]

theorem softmax_form {Hs : Type*} (A : Finset Hs) (p : Hs → ℝ) (hp : ∀ h, 0 ≤ p h) (h : Hs) :
    p h / ∑ h' ∈ A, p h' = boltz (p h) / ∑ h' ∈ A, boltz (p h') := by
  rw [boltz_eq (hp h), Finset.sum_congr rfl (fun h' _ => boltz_eq (hp h'))]

/-- C06-47/C03-12: record coarse-graining is linear: p(h, ΣR_i) = Σ p(h, R_i), and the
conditional weight is the corresponding ratio. -/
theorem record_pushforward {I : Type*} (s : Finset I) (R : I → Op ι) (C ρ : Op ι) :
    trace ((∑ i ∈ s, R i) * (C * ρ * Cᴴ)) = ∑ i ∈ s, trace (R i * (C * ρ * Cᴴ)) := by
  rw [Finset.sum_mul, trace_sum]

/-! ### Instruments (C06-43, -44) and no-signaling (C06-46) -/

/-- Kraus instrument: M_a(ρ) = Σ_k K_{a,k} ρ K_{a,k}†, Σ_{a,k} K†K = 1.
C06-43: p(a) = Tr M_a(ρ) ≥ 0 and Σ_a p(a) = Tr ρ (= 1 for a state). -/
theorem instrument_distribution {Aout Kr : Type*} [Fintype Aout] [Fintype Kr]
    (K : Aout → Kr → Op ι) (hK : ∑ a, ∑ k, (K a k)ᴴ * K a k = 1) {ρ : Op ι} (hρ : ρ.PosSemidef) :
    (∀ a, 0 ≤ ∑ k, trace (K a k * ρ * (K a k)ᴴ)) ∧
      ∑ a, ∑ k, trace (K a k * ρ * (K a k)ᴴ) = trace ρ := by
  refine ⟨fun a => Finset.sum_nonneg (fun k _ => (hρ.mul_mul_conjTranspose_same _).trace_nonneg), ?_⟩
  have : ∀ a k, trace (K a k * ρ * (K a k)ᴴ) = trace (ρ * ((K a k)ᴴ * K a k)) := by
    intro a k; rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  simp_rw [this, ← trace_sum, ← Finset.mul_sum, hK, Matrix.mul_one]

/-- C06-44: given a refinement Σ_h p(h,a) = p(a) > 0 with p(h,a) ≥ 0, p(h|a) is a distribution. -/
theorem record_conditional {Hs : Type*} [Fintype Hs] (q : Hs → ℝ) (pa : ℝ) (hq : ∀ h, 0 ≤ q h)
    (href : ∑ h, q h = pa) (hpa : 0 < pa) :
    (∀ h, 0 ≤ q h / pa) ∧ ∑ h, q h / pa = 1 := by
  refine ⟨fun h => div_nonneg (hq h) hpa.le, ?_⟩
  rw [← Finset.sum_div, href, div_self hpa.ne']

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem kronecker_finset_sum {γ : Type*} (s : Finset γ) (A : Matrix α α ℂ) (B : γ → Matrix β β ℂ) :
    A ⊗ₖ (∑ i ∈ s, B i) = ∑ i ∈ s, A ⊗ₖ B i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, kronecker_add, ih]

theorem trace_sandwich (M ρ : Matrix α α ℂ) : trace (M * ρ * Mᴴ) = trace (ρ * (Mᴴ * M)) := by
  rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]

/-- C06-46 no-signaling: with Alice's Kraus operators K_{a,k} and Bob's L_{b,l} (Σ_{b,l} L†L = 1),
Σ_b Tr[(K ⊗ L)ρ(K ⊗ L)†] summed over Kraus labels equals Tr[(K ⊗ 1)ρ(K ⊗ 1)†]: Alice's
marginal does not depend on Bob's instrument. -/
theorem no_signaling {Bout Lr Kr : Type*} [Fintype Bout] [Fintype Lr] [Fintype Kr]
    (K : Kr → Matrix α α ℂ) (L : Bout → Lr → Matrix β β ℂ)
    (hL : ∑ b, ∑ l, (L b l)ᴴ * L b l = 1) (ρ : Matrix (α × β) (α × β) ℂ) :
    ∑ b, ∑ k, ∑ l, trace ((K k ⊗ₖ L b l) * ρ * (K k ⊗ₖ L b l)ᴴ) =
      ∑ k, trace ((K k ⊗ₖ (1 : Matrix β β ℂ)) * ρ * (K k ⊗ₖ (1 : Matrix β β ℂ))ᴴ) := by
  simp_rw [trace_sandwich, conjTranspose_kronecker, ← mul_kronecker_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp_rw [← trace_sum, ← Finset.mul_sum]
  congr 2
  rw [conjTranspose_one, Matrix.one_mul]
  have : ∑ b, ∑ l, ((K k)ᴴ * K k) ⊗ₖ ((L b l)ᴴ * L b l) =
      ((K k)ᴴ * K k) ⊗ₖ (∑ b, ∑ l, (L b l)ᴴ * L b l) := by
    rw [kronecker_finset_sum]; refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [kronecker_finset_sum]
  rw [this, hL]

/-! ### Replacement channel (C03-15, -16) and environment overlap (C03-17) -/

def IsDensity (ρ : Op ι) : Prop := ρ.PosSemidef ∧ trace ρ = 1

theorem half_nonneg : (0 : ℂ) ≤ 1/2 := by
  rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by push_cast; ring]; exact Complex.zero_le_real.mpr (by norm_num)

/-- Matrix units and basis vectors (with the index on the left of every test). -/
def Eb (i j : ι) : Op ι := Matrix.of fun a b => if a = i ∧ b = j then 1 else 0
def ev (i : ι) : ι → ℂ := fun a => if a = i then 1 else 0

theorem trace_Eb (i j : ι) : trace (Eb i j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h; simp [trace, Eb]
  · rw [if_neg h]; simp only [trace, Eb, Matrix.diag]
    exact Finset.sum_eq_zero (fun a _ => if_neg (fun ⟨h1, h2⟩ => h (h1 ▸ h2)))

theorem Eb_eq (i j : ι) : Eb i j = single i j 1 := by
  ext a b; simp only [Eb, of_apply, single_apply]
  exact if_congr ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩ rfl rfl

theorem decompose (X : Op ι) : X = ∑ i, ∑ j, X i j • Eb i j := by
  conv_lhs => rw [matrix_eq_sum_single X]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Eb_eq, smul_single, smul_eq_mul, mul_one]

/-- C03-15: a linear map that sends every density matrix to the same state σ is the
replacement channel E(X) = Tr(X)·σ. -/
theorem replacement_unique (E : Op ι →ₗ[ℂ] Op ι) (σ : Op ι)
    (hE : ∀ ρ, IsDensity ρ → E ρ = σ) (X : Op ι) : E X = trace X • σ := by
  have vv : ∀ u : ι → ℂ, (vecMulVec u (star u)).PosSemidef := posSemidef_vecMulVec_self_star
  have hdiag : ∀ i, E (Eb i i) = σ := by
    intro i
    have e : Eb i i = vecMulVec (ev i) (star (ev i)) := by
      ext a b; simp only [Eb, ev, vecMulVec, of_apply, Pi.star_apply]
      by_cases ha : a = i <;> by_cases hb : b = i <;> simp [ha, hb]
    apply hE; refine ⟨e ▸ vv _, ?_⟩; rw [trace_Eb]; simp
  have hoff : ∀ i j, i ≠ j → E (Eb i j) = 0 := by
    intro i j hij
    have hv : vecMulVec (ev i + ev j) (star (ev i + ev j)) = Eb i i + Eb i j + Eb j i + Eb j j := by
      ext a b; simp only [Eb, ev, vecMulVec, of_apply, Pi.star_apply, Pi.add_apply, Matrix.add_apply]
      by_cases ha : a = i <;> by_cases hb : b = i <;> by_cases ha' : a = j <;> by_cases hb' : b = j <;>
        simp_all
    have hw : vecMulVec (ev i + Complex.I • ev j) (star (ev i + Complex.I • ev j)) =
        Eb i i + (-Complex.I) • Eb i j + Complex.I • Eb j i + Eb j j := by
      ext a b; simp only [Eb, ev, vecMulVec, of_apply, Pi.star_apply, Pi.add_apply, Matrix.add_apply,
        Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
      by_cases ha : a = i <;> by_cases hb : b = i <;> by_cases ha' : a = j <;> by_cases hb' : b = j <;>
        simp_all [Complex.conj_I]
    have htr : ∀ c d : ℂ, trace (Eb i i + c • Eb i j + d • Eb j i + Eb j j) = 2 := by
      intro c d
      simp only [trace_add, trace_smul, trace_Eb, if_pos rfl, if_neg hij, if_neg (Ne.symm hij),
        smul_zero]; norm_num
    have dv : IsDensity ((1/2 : ℂ) • vecMulVec (ev i + ev j) (star (ev i + ev j))) := by
      refine ⟨(vv _).smul half_nonneg, ?_⟩
      rw [trace_smul, hv, show Eb i i + Eb i j + Eb j i + Eb j j =
        Eb i i + (1:ℂ) • Eb i j + (1:ℂ) • Eb j i + Eb j j by simp, htr]; norm_num
    have dw : IsDensity ((1/2 : ℂ) • vecMulVec (ev i + Complex.I • ev j)
        (star (ev i + Complex.I • ev j))) := by
      refine ⟨(vv _).smul half_nonneg, ?_⟩
      rw [trace_smul, hw, htr]; norm_num
    have e1 := hE _ dv
    have e2 := hE _ dw
    rw [map_smul, hv, map_add, map_add, map_add, hdiag, hdiag] at e1
    rw [map_smul, hw, map_add, map_add, map_add, map_smul, map_smul, hdiag, hdiag] at e2
    set a := E (Eb i j)
    set b := E (Eb j i)
    have s1 : a + b = 0 := by linear_combination (norm := module) (2:ℂ) • e1
    have s2 : Complex.I • (b - a) = 0 := by linear_combination (norm := module) (2:ℂ) • e2
    have hb : b - a = 0 := (smul_eq_zero.mp s2).resolve_left Complex.I_ne_zero
    linear_combination (norm := module) (1/2:ℂ) • s1 - (1/2:ℂ) • hb
  conv_lhs => rw [decompose X]
  simp only [map_sum, map_smul]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_eq_single i
    (fun j _ hj => by rw [hoff i j (Ne.symm hj), smul_zero]) (by simp))]
  simp_rw [hdiag]
  rw [← Finset.sum_smul]; rfl

/-- C03-16: the Heisenberg dual of E(ρ) = Tr(ρ)σ is O ↦ Tr(σO)·1. -/
theorem replacement_dual (σ ρ O : Op ι) :
    trace ((trace ρ • σ) * O) = trace (ρ * (trace (σ * O) • (1 : Op ι))) := by
  rw [smul_mul_assoc, trace_smul, Matrix.mul_smul, Matrix.mul_one, trace_smul, smul_eq_mul,
    smul_eq_mul, mul_comm]

/-- C03-17: for ψ = a|x⟩|e_x⟩ + b|y⟩|e_y⟩ (x ≠ y) the reduced system matrix has
⟨x|ρ_S|y⟩ = Σ_e ψ(x,e) ψ(y,e)* = a b* ⟨e_y|e_x⟩. -/
theorem environment_overlap {S Env : Type*} [Fintype Env] [DecidableEq S] {x y : S} (hxy : x ≠ y)
    (a b : ℂ) (ex ey : Env → ℂ) :
    let ψ : S → Env → ℂ := fun s e => (if s = x then a * ex e else 0) + (if s = y then b * ey e else 0)
    ∑ e, ψ x e * star (ψ y e) = a * star b * ∑ e, ex e * star (ey e) := by
  intro ψ
  simp only [ψ, if_true, if_neg hxy, if_neg (Ne.symm hxy), add_zero, zero_add, star_mul', eq_self_iff_true]
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun e _ => ?_); ring

end Entropic.AppFG.Histories
