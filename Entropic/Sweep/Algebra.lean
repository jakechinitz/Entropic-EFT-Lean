import Entropic.Main.Galactic
import Entropic.AppH10.Symbols
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-! Chunk 14 sweep: finite algebra and elementary analysis for deferred claims
(C04-53, C04-54, C04-66, C07-46, C08-44, C08-45, C09-32, C09-47, C10-35, C11-49, C11-89, C11-94,
C12-03, C12-14, C12-65, C12-79). -/

noncomputable section
namespace Entropic.Sweep.Alg
open Matrix Finset
open scoped Kronecker BigOperators

/-! ### C04-66: label multisets -/

/-- C04-66 (label form): with m = 2s and n = 2j (n ≥ 1), the label sets {0, …, 2s} of H_mark(s) and
{0, …, 2j − 1} of Q(j) coincide iff 2s = 2j − 1; the dimensions are (2s+1)² and (2j)² = (2j+1)² − (4j+1). -/
theorem label_match (m n : ℕ) : Finset.range (m + 1) = Finset.range n ↔ m + 1 = n :=
  ⟨fun h => by simpa using congrArg Finset.card h, fun h => h ▸ rfl⟩

theorem label_dims (m : ℕ) : ∑ J ∈ Finset.range (m + 1), (2 * J + 1) = (m + 1) ^ 2 := by
  induction m with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

/-! ### C04-53, C04-54 -/

/-- C04-53 (gap): with E_J = (κ/2)[3N(3N+1) − J(J+1)], E_{3N} = 0 and Δ_N = E_{3N−1} − E_{3N} = 3κN. -/
theorem heisenberg_gap (κ N : ℝ) :
    let E : ℝ → ℝ := fun J => κ / 2 * (3 * N * (3 * N + 1) - J * (J + 1))
    E (3 * N) = 0 ∧ E (3 * N - 1) - E (3 * N) = 3 * κ * N := by
  intro E; constructor <;> simp only [E] <;> ring

/-- C04-54 (asymptotic): |j²(1 − cos θ) − j²θ²/2| ≤ (5/96) j² θ⁴ for |θ| ≤ 1. -/
theorem mismatch_asymptotic (j θ : ℝ) (h : |θ| ≤ 1) :
    |j ^ 2 * (1 - Real.cos θ) - j ^ 2 * θ ^ 2 / 2| ≤ 5 / 96 * j ^ 2 * θ ^ 4 := by
  have hb := Real.cos_bound h
  have e : j ^ 2 * (1 - Real.cos θ) - j ^ 2 * θ ^ 2 / 2 = -(j ^ 2 * (Real.cos θ - (1 - θ ^ 2 / 2))) := by ring
  rw [e, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg j)]
  have : |θ| ^ 4 = θ ^ 4 := by rw [pow_abs]; exact abs_of_nonneg (by positivity)
  calc j ^ 2 * |Real.cos θ - (1 - θ ^ 2 / 2)| ≤ j ^ 2 * (|θ| ^ 4 * (5 / 96)) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg j)
    _ = 5 / 96 * j ^ 2 * θ ^ 4 := by rw [this]; ring

/-! ### C08-44, C08-45: vector operators vanish between invariants -/

/-- C08-44: let J_tot^a be generators with P J_tot^a = J_tot^a P = 0 (P the projector onto invariants)
and F^a a vector operator, [J_tot^a, F^b] = i ε_{abc} F^c on the cyclic triples. Then P F^c P = 0. -/
theorem projected_vector_zero {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ)
    (Jt F : Fin 3 → Matrix n n ℂ) (hl : ∀ a, P * Jt a = 0) (hr : ∀ a, Jt a * P = 0)
    (h01 : Jt 0 * F 1 - F 1 * Jt 0 = Complex.I • F 2) (h12 : Jt 1 * F 2 - F 2 * Jt 1 = Complex.I • F 0)
    (h20 : Jt 2 * F 0 - F 0 * Jt 2 = Complex.I • F 1) : ∀ c, P * F c * P = 0 := by
  have key : ∀ a b c, Jt a * F b - F b * Jt a = Complex.I • F c → P * F c * P = 0 := by
    intro a b c h
    have e : P * (Jt a * F b - F b * Jt a) * P = 0 := by
      rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, hl, Matrix.zero_mul, Matrix.zero_mul,
        Matrix.mul_assoc, Matrix.mul_assoc, hr, Matrix.mul_zero, Matrix.mul_zero, sub_zero]
    rw [h, Matrix.mul_smul, Matrix.smul_mul] at e
    exact (smul_eq_zero.mp e).resolve_left Complex.I_ne_zero
  intro c; fin_cases c
  · exact key 1 2 0 h12
  · exact key 2 0 1 h20
  · exact key 0 1 2 h01

/-- C08-45: (P ⊗ P')(Σ_{ab} R_{ab} F^a ⊗ G^b)(P ⊗ P') = Σ R_{ab}(P F^a P) ⊗ (P' G^b P') = 0. -/
theorem transported_bilinear_zero {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (P : Matrix n n ℂ) (P' : Matrix m m ℂ) (F : Fin 3 → Matrix n n ℂ) (G : Fin 3 → Matrix m m ℂ)
    (R : Fin 3 → Fin 3 → ℂ) (hF : ∀ a, P * F a * P = 0) :
    (P ⊗ₖ P') * (∑ a, ∑ b, R a b • (F a ⊗ₖ G b)) * (P ⊗ₖ P') = 0 := by
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_kronecker_mul,
    hF, Matrix.zero_kronecker, smul_zero, Finset.sum_const_zero]

/-! ### C09-32: mixed-product factorization of the projected bridge -/

/-- C09-32: (P ⊗ P)((I⊗H) ⊗ (H⊗I))(P ⊗ P) = (P(I⊗H)P) ⊗ (P(H⊗I)P) = A_R ⊗ A_L. Traces Tr A = 0 and
Tr A² = 38 are `AppP.Spin.bridge_traces`. -/
theorem bridge_factorizes {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (P A B : Matrix n n R) : (P ⊗ₖ P) * (A ⊗ₖ B) * (P ⊗ₖ P) = (P * A * P) ⊗ₖ (P * B * P) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

/-! ### C09-47: the Z relation on invariants -/

/-- C09-47: on a vector v annihilated by the total spin (Σ_k J_k^a) v = 0, with J₁·J₁ = 12 (spin 3),
J₁·J₄ v = (−12 − X − Y) v where X = J₁·J₂ and Y = J₁·J₃. -/
theorem z_relation {V : Type*} [AddCommGroup V] [Module ℂ V] (J : Fin 4 → Fin 3 → V →ₗ[ℂ] V) (v : V)
    (hinv : ∀ a, (J 0 a + J 1 a + J 2 a + J 3 a) v = 0)
    (hcas : ∑ a, (J 0 a ∘ₗ J 0 a) v = (12 : ℂ) • v) :
    ∑ a, (J 0 a ∘ₗ J 3 a) v = -(12 : ℂ) • v - ∑ a, (J 0 a ∘ₗ J 1 a) v - ∑ a, (J 0 a ∘ₗ J 2 a) v := by
  have h : ∑ a, J 0 a ((J 0 a + J 1 a + J 2 a + J 3 a) v) = 0 := by simp [hinv]
  simp only [LinearMap.add_apply, map_add, Finset.sum_add_distrib] at h
  simp only [LinearMap.comp_apply] at hcas ⊢
  rw [hcas] at h
  rw [neg_smul]
  calc ∑ a, J 0 a (J 3 a v) = ((12:ℂ) • v + ∑ a, J 0 a (J 1 a v) + ∑ a, J 0 a (J 2 a v) + ∑ a, J 0 a (J 3 a v)) -
        (12:ℂ) • v - ∑ a, J 0 a (J 1 a v) - ∑ a, J 0 a (J 2 a v) := by abel
    _ = _ := by rw [h]; abel

/-! ### C07-46: reversible export by register permutation -/

section Export
variable {B : Type*} [Fintype B] [DecidableEq B]

/-- The register permutation A → H, F → A, H → F (R fixed) on wavefunctions over (a, f, r, h). -/
def regPerm (Ψ : B × B × B × B → ℂ) : B × B × B × B → ℂ := fun x => Ψ (x.2.2.2, x.1, x.2.2.1, x.2.1)
def regPermInv (Φ : B × B × B × B → ℂ) : B × B × B × B → ℂ := fun x => Φ (x.2.1, x.2.2.2, x.2.2.1, x.1)

/-- Input |ψ⟩_A |Ψ_*⟩_{FR} |0⟩_H with Ψ_* = Σ_b √p(b)|b⟩|b⟩. -/
def inState (p : B → ℝ) (b0 : B) (ψ : B → ℂ) : B × B × B × B → ℂ := fun x =>
  ψ x.1 * (if x.2.1 = x.2.2.1 then (Real.sqrt (p x.2.1) : ℂ) else 0) * (if x.2.2.2 = b0 then 1 else 0)

/-- C07-46: U maps |ψ⟩_A|Ψ_*⟩_{FR}|0⟩_H to |Ψ_*⟩_{AR}|0⟩_F|ψ⟩_H, U⁻¹U = id, U preserves the norm,
and Tr_{F,R,H} of the output is Σ_b p(b)|b⟩⟨b| on A for every normalized ψ. -/

theorem regPerm_inState (p : B → ℝ) (b0 : B) (ψ : B → ℂ) (x : B × B × B × B) :
    regPerm (inState p b0 ψ) x =
      (if x.1 = x.2.2.1 then (Real.sqrt (p x.1) : ℂ) else 0) * (if x.2.1 = b0 then 1 else 0) * ψ x.2.2.2 := by
  simp only [regPerm, inState]
  by_cases h : x.1 = x.2.2.1
  · rw [if_pos h]; ring
  · rw [if_neg h]; ring

/-- C07-46: U maps |ψ⟩_A|Ψ_*⟩_{FR}|0⟩_H to |Ψ_*⟩_{AR}|0⟩_F|ψ⟩_H, U⁻¹U = id, U preserves the norm,
and Tr_{F,R,H} of the output is Σ_b p(b)|b⟩⟨b| on A for every normalized ψ. -/
theorem reversible_export (p : B → ℝ) (hp : ∀ b, 0 ≤ p b) (b0 : B) (ψ : B → ℂ)
    (hψ : ∑ h, Complex.normSq (ψ h) = 1) :
    (∀ Ψ : B × B × B × B → ℂ, regPermInv (regPerm Ψ) = Ψ) ∧
      (∀ Ψ : B × B × B × B → ℂ, ∑ x, Complex.normSq (regPerm Ψ x) = ∑ x, Complex.normSq (Ψ x)) ∧
      (∀ a a' : B, ∑ f, ∑ r, ∑ h, regPerm (inState p b0 ψ) (a, f, r, h) *
          starRingEnd ℂ (regPerm (inState p b0 ψ) (a', f, r, h)) = if a = a' then (p a : ℂ) else 0) := by
  refine ⟨fun Ψ => rfl, fun Ψ => ?_, fun a a' => ?_⟩
  · let e : B × B × B × B ≃ B × B × B × B :=
      { toFun := fun x => (x.2.2.2, x.1, x.2.2.1, x.2.1), invFun := fun x => (x.2.1, x.2.2.2, x.2.2.1, x.1),
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    exact Fintype.sum_equiv e _ _ (fun x => rfl)
  · have hterm : ∀ f r h : B, regPerm (inState p b0 ψ) (a, f, r, h) *
        starRingEnd ℂ (regPerm (inState p b0 ψ) (a', f, r, h)) =
        (if f = b0 then 1 else 0) * ((if a = r then (Real.sqrt (p a) : ℂ) else 0) *
          starRingEnd ℂ (if a' = r then (Real.sqrt (p a') : ℂ) else 0)) * (ψ h * starRingEnd ℂ (ψ h)) := by
      intro f r h
      rw [regPerm_inState, regPerm_inState]
      simp only [map_mul]
      split_ifs <;> simp <;> ring
    have fac : ∀ X Y Z : B → ℂ, ∑ f, ∑ r, ∑ h, X f * Y r * Z h = (∑ f, X f) * (∑ r, Y r) * (∑ h, Z h) := by
      intro X Y Z; symm
      rw [Finset.sum_mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl (fun f _ => ?_)
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [Finset.mul_sum]
    simp_rw [hterm]
    rw [fac (fun f => if f = b0 then (1:ℂ) else 0)
      (fun r => (if a = r then (Real.sqrt (p a) : ℂ) else 0) * starRingEnd ℂ (if a' = r then (Real.sqrt (p a') : ℂ) else 0))
      (fun h => ψ h * starRingEnd ℂ (ψ h))]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, one_mul]
    have hs : ∑ h, ψ h * starRingEnd ℂ (ψ h) = 1 := by
      simp_rw [Complex.mul_conj]; rw [← Complex.ofReal_sum, hψ, Complex.ofReal_one]
    rw [hs, mul_one]
    by_cases haa : a = a'
    · subst haa
      rw [if_pos rfl, Finset.sum_eq_single a]
      · rw [if_pos rfl, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hp a)]
      · intro r _ hr; rw [if_neg (Ne.symm hr), zero_mul]
      · intro h; exact absurd (Finset.mem_univ a) h
    · rw [if_neg haa]
      apply Finset.sum_eq_zero; intro r _
      by_cases h1 : a = r
      · have h2 : ¬ a' = r := fun h2 => haa (h1.trans h2.symm)
        simp [h2]
      · simp [h1]
end Export

/-! ### C10-35: matrix units and the S₃ permutation algebra -/

/-- C10-35(a): P_a S_{ab} P_b = E_{ab} with S_{ab} the permutation matrix of the transposition (a b)
(identity when a = b), P_a = E_{aa}. -/
theorem matrix_units : ∀ a b : Fin 3,
    Matrix.single a a (1:ℤ) * (Equiv.swap a b).permMatrix ℤ * Matrix.single b b 1 = Matrix.single a b 1 := by
  intro a b; ext i j
  simp only [Matrix.mul_apply, Matrix.single_apply, Equiv.Perm.permMatrix, Equiv.toPEquiv_apply,
    PEquiv.toMatrix_apply, Option.mem_def, Option.some.injEq]
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;> decide

/-- C10-35(a): the nine matrix units span M₃: every matrix is Σ_{ab} M_{ab} E_{ab}. -/
theorem units_span (M : Matrix (Fin 3) (Fin 3) ℚ) : M = ∑ a, ∑ b, M a b • Matrix.single a b (1:ℚ) := by
  ext i j; simp [Matrix.sum_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

/-- C10-35(b): the six 3×3 permutation matrices satisfy Σ_σ sgn(σ) P_σ = 0. -/
theorem s3_relation : ∑ σ : Equiv.Perm (Fin 3), (Equiv.Perm.sign σ : ℤ) • σ.permMatrix ℤ = 0 := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.zero_apply]
  revert i j; decide

/-- C10-35(b): the product of permutation matrices is a permutation matrix, so their span is closed
under multiplication and equals the algebra they generate. -/
theorem s3_closed (σ τ : Equiv.Perm (Fin 3)) : σ.permMatrix ℚ * τ.permMatrix ℚ = (τ * σ).permMatrix ℚ :=
  (Matrix.permMatrix_mul τ σ).symm

/-- C10-35(b): the five permutation matrices other than the identity... more precisely, the matrices of
id, (0 1), (0 2), (1 2), (0 1 2) are linearly independent; with the relation above the span is 5-dim. -/
theorem s3_independent (c : Fin 5 → ℚ)
    (h : c 0 • (1 : Matrix (Fin 3) (Fin 3) ℚ) + c 1 • (Equiv.swap (0:Fin 3) 1).permMatrix ℚ +
      c 2 • (Equiv.swap (0:Fin 3) 2).permMatrix ℚ + c 3 • (Equiv.swap (1:Fin 3) 2).permMatrix ℚ +
      c 4 • (Equiv.swap (0:Fin 3) 1 * Equiv.swap 1 2).permMatrix ℚ = 0) : ∀ i, c i = 0 := by
  have e : ∀ i j : Fin 3, (c 0 • (1 : Matrix (Fin 3) (Fin 3) ℚ) + c 1 • (Equiv.swap (0:Fin 3) 1).permMatrix ℚ +
      c 2 • (Equiv.swap (0:Fin 3) 2).permMatrix ℚ + c 3 • (Equiv.swap (1:Fin 3) 2).permMatrix ℚ +
      c 4 • (Equiv.swap (0:Fin 3) 1 * Equiv.swap 1 2).permMatrix ℚ) i j = 0 := by rw [h]; intro i j; rfl
  have g : ∀ i j : Fin 3, _ := fun i j => e i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Equiv.Perm.permMatrix, Equiv.toPEquiv_apply,
    PEquiv.toMatrix_apply, Option.mem_def, Option.some.injEq, smul_eq_mul] at g
  have g00 := g 0 0; have g01 := g 0 1; have g02 := g 0 2; have g12 := g 1 2; have g10 := g 1 0
  simp (config := {decide := true}) [Equiv.swap_apply_def] at g00 g01 g02 g12 g10
  intro i; fin_cases i <;> simp <;> linarith

/-! ### C11-94: invariant forms on the tetrahedral sum-zero representation -/

def c1 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2
def c2 : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 2 3

theorem c1_sign : Equiv.Perm.sign c1 = 1 := by decide
theorem c2_sign : Equiv.Perm.sign c2 = 1 := by decide

/-- C11-94: a bilinear form B on ℝ⁴ invariant under the even permutations (A₄ ⊂ S₄) restricts on the
sum-zero subspace to a scalar multiple of the Euclidean inner product. -/
theorem invariant_form_scalar (B : Fin 4 → Fin 4 → ℝ)
    (hB : ∀ σ : Equiv.Perm (Fin 4), Equiv.Perm.sign σ = 1 → ∀ i j, B (σ i) (σ j) = B i j) :
    ∃ a : ℝ, ∀ x y : Fin 4 → ℝ, ∑ i, x i = 0 → ∑ i, y i = 0 →
      ∑ i, ∑ j, x i * B i j * y j = a * ∑ i, x i * y i := by
  have h1 := hB c1 c1_sign
  have h2 := hB c2 c2_sign
  have v1 : ∀ i j, B (c1 i) (c1 j) = B i j := h1
  have v2 : ∀ i j, B (c2 i) (c2 j) = B i j := h2
  have ev1 : c1 0 = 1 ∧ c1 1 = 2 ∧ c1 2 = 0 ∧ c1 3 = 3 := by decide
  have ev2 : c2 0 = 0 ∧ c2 1 = 2 ∧ c2 2 = 3 ∧ c2 3 = 1 := by decide
  obtain ⟨a0, a1, a2, a3⟩ := ev1
  obtain ⟨b0, b1, b2, b3⟩ := ev2
  have d1 := v1 0 0; have d2 := v1 1 1; have d3 := v2 2 2
  have o1 := v1 0 1; have o2 := v1 1 2; have o3 := v1 0 2; have o4 := v1 1 0
  have o5 := v1 0 3; have o6 := v1 1 3; have o7 := v1 3 0; have o8 := v1 3 1
  have o9 := v2 1 2; have o10 := v2 0 1; have o11 := v2 0 2; have o12 := v2 1 3; have o13 := v2 2 1
  have o14 := v2 1 0; have o15 := v2 2 0
  simp only [a0, a1, a2, a3, b0, b1, b2, b3] at d1 d2 d3 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15
  refine ⟨B 0 0 - B 0 1, fun x y hx hy => ?_⟩
  simp only [Fin.sum_univ_four] at hx hy ⊢
  have hx' : x 3 = -(x 0 + x 1 + x 2) := by linarith
  have hy' : y 3 = -(y 0 + y 1 + y 2) := by linarith
  rw [hx', hy']
  have e11 : B 1 1 = B 0 0 := by linarith
  have e22 : B 2 2 = B 0 0 := by linarith
  have e33 : B 3 3 = B 0 0 := by linarith
  have f12 : B 1 2 = B 0 1 := by linarith
  have f20 : B 2 0 = B 0 1 := by linarith
  have f02 : B 0 2 = B 0 1 := by linarith
  have f10 : B 1 0 = B 0 1 := by linarith
  have f21 : B 2 1 = B 0 1 := by linarith
  have f23 : B 2 3 = B 0 1 := by linarith
  have f03 : B 0 3 = B 0 1 := by linarith
  have f13 : B 1 3 = B 0 1 := by linarith
  have f30 : B 3 0 = B 0 1 := by linarith
  have f31 : B 3 1 = B 0 1 := by linarith
  have f32 : B 3 2 = B 0 1 := by linarith
  rw [e11, e22, e33, f12, f20, f02, f10, f21, f23, f03, f13, f30, f31, f32]
  ring

/-! ### C12-65: finite-area Hamiltonian commutator -/

/-- C12-65: H[N] = Σ_j N_j T_j + diag(v_N) with commuting T_j. For x ≠ y with T_j(x, y) = 0 for j ≠ i,
[H[N], H[M]](x, y) = T_i(x, y)[N_i(v_M(y) − v_M(x)) − M_i(v_N(y) − v_N(x))]. -/
theorem area_commutator {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (T : Fin n → Matrix ι ι ℂ)
    (hc : ∀ j k, T j * T k = T k * T j) (N M : Fin n → ℂ) (vN vM : ι → ℂ) (i : Fin n) (x y : ι)
    (hloc : ∀ j, j ≠ i → T j x y = 0) :
    let HN := ∑ j, N j • T j + Matrix.diagonal vN
    let HM := ∑ j, M j • T j + Matrix.diagonal vM
    (HN * HM - HM * HN) x y = T i x y * (N i * (vM y - vM x) - M i * (vN y - vN x)) := by
  intro HN HM
  have prod : ∀ A C : Fin n → ℂ, (∑ j, A j • T j) * (∑ k, C k • T k) = ∑ j, ∑ k, (A j * C k) • (T j * T k) := by
    intro A C
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hTT : (∑ j, N j • T j) * (∑ k, M k • T k) = (∑ k, M k • T k) * (∑ j, N j • T j) := by
    rw [prod, prod, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [hc, mul_comm]
  have hDD : Matrix.diagonal vN * Matrix.diagonal vM = Matrix.diagonal vM * Matrix.diagonal vN := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]; congr 1; ext; ring
  have e : HN * HM - HM * HN = ((∑ j, N j • T j) * Matrix.diagonal vM - Matrix.diagonal vM * (∑ j, N j • T j)) -
      ((∑ k, M k • T k) * Matrix.diagonal vN - Matrix.diagonal vN * (∑ k, M k • T k)) := by
    simp only [HN, HM, Matrix.add_mul, Matrix.mul_add]; rw [hTT, hDD]; abel
  rw [e]
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  have s1 : ∀ (c : Fin n → ℂ), ∑ j, c j * T j x y = c i * T i x y := by
    intro c; rw [Finset.sum_eq_single i]
    · intro j _ hj; rw [hloc j hj, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [s1 N, s1 M]; ring

/-! ### C12-79: rotated-contour covariance -/

/-- C12-79: K = O diag(λ) Oᵀ with O orthogonal and λ_i ≠ 0; R = O diag(ρ) with ρ_i² = sign λ_i. Then
R |diag λ|⁻¹ Rᵀ = K⁻¹ (plain transpose). -/
theorem rotated_contour {n : Type*} [Fintype n] [DecidableEq n] (O : Matrix n n ℂ) (hO : Oᵀ * O = 1)
    (hO' : O * Oᵀ = 1) (lam : n → ℝ) (hl : ∀ i, lam i ≠ 0) (ρ : n → ℂ)
    (hρ : ∀ i, ρ i ^ 2 = if 0 < lam i then 1 else -1) :
    let K := O * Matrix.diagonal (fun i => (lam i : ℂ)) * Oᵀ
    let R := O * Matrix.diagonal ρ
    R * Matrix.diagonal (fun i => (((|lam i|)⁻¹ : ℝ) : ℂ)) * Rᵀ = K⁻¹ := by
  intro K R
  have hd : ∀ i, ρ i * (((|lam i|)⁻¹ : ℝ) : ℂ) * ρ i = ((lam i : ℂ)⁻¹) := by
    intro i
    rw [mul_comm, ← mul_assoc, ← sq, hρ i]
    rcases lt_or_gt_of_ne (hl i) with h | h
    · rw [if_neg (by linarith), abs_of_neg h]; push_cast; rw [inv_neg]; ring
    · rw [if_pos h, abs_of_pos h]; push_cast; ring
  have hX : R * Matrix.diagonal (fun i => (((|lam i|)⁻¹ : ℝ) : ℂ)) * Rᵀ =
      O * Matrix.diagonal (fun i => ((lam i : ℂ)⁻¹)) * Oᵀ := by
    simp only [R, Matrix.transpose_mul, Matrix.diagonal_transpose]
    rw [show O * Matrix.diagonal ρ * Matrix.diagonal (fun i => (((|lam i|)⁻¹ : ℝ) : ℂ)) * (Matrix.diagonal ρ * Oᵀ) =
      O * (Matrix.diagonal ρ * Matrix.diagonal (fun i => (((|lam i|)⁻¹ : ℝ) : ℂ)) * Matrix.diagonal ρ) * Oᵀ by
        simp only [Matrix.mul_assoc]]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    simp only [hd]
  rw [hX]; symm
  apply Matrix.inv_eq_right_inv
  simp only [K]
  rw [show O * Matrix.diagonal (fun i => (lam i : ℂ)) * Oᵀ * (O * Matrix.diagonal (fun i => ((lam i : ℂ)⁻¹)) * Oᵀ) =
    O * (Matrix.diagonal (fun i => (lam i : ℂ)) * (Oᵀ * O) * Matrix.diagonal (fun i => ((lam i : ℂ)⁻¹))) * Oᵀ by
      simp only [Matrix.mul_assoc]]
  rw [hO, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
  have : (fun i => (lam i : ℂ) * ((lam i : ℂ)⁻¹)) = fun _ => 1 := by
    ext i; exact mul_inv_cancel₀ (by exact_mod_cast hl i)
  rw [this, Matrix.diagonal_one, Matrix.mul_one, hO']

/-! ### C11-49: second-order log expansion -/

/-- C11-49: ζ = ½ ln(1 − 2ψ) satisfies |ζ + ψ + ψ²| ≤ 4|ψ|³/(1 − 2|ψ|) for |ψ| < 1/2, so
ζ = −ψ − ψ² + O(ψ³). -/
theorem conformal_expansion (ψ : ℝ) (h : |ψ| < 1 / 2) :
    |1 / 2 * Real.log (1 - 2 * ψ) + ψ + ψ ^ 2| ≤ 4 * |ψ| ^ 3 / (1 - 2 * |ψ|) := by
  have h2 : |2 * ψ| < 1 := by rw [abs_mul]; norm_num; linarith
  have hb := Real.abs_log_sub_add_sum_range_le h2 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb
  have e : 1 / 2 * Real.log (1 - 2 * ψ) + ψ + ψ ^ 2 =
      1 / 2 * (0 + (2 * ψ) ^ (0 + 1) / (0 + 1) + (2 * ψ) ^ (1 + 1) / (1 + 1) + Real.log (1 - 2 * ψ)) := by
    push_cast; ring
  rw [e, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  have hden : 0 < 1 - |2 * ψ| := by linarith
  calc 1 / 2 * |0 + (2 * ψ) ^ (0 + 1) / (0 + 1) + (2 * ψ) ^ (1 + 1) / (1 + 1) + Real.log (1 - 2 * ψ)|
      ≤ 1 / 2 * (|2 * ψ| ^ (2 + 1) / (1 - |2 * ψ|)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num); push_cast at hb ⊢; exact hb
    _ = 4 * |ψ| ^ 3 / (1 - 2 * |ψ|) := by
        rw [abs_mul, abs_two]; field_simp; ring

/-! ### C11-89: kernel reconstruction preserves mass -/

/-- C11-89: if K(x, y) ≥ 0 is measurable with ∫ K(x, y) dx = 1 for every y and f ≥ 0, then
∫∫ K(x, y) f(y) dy dx = ∫ f (Tonelli). -/
theorem kernel_mass {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : MeasureTheory.Measure X)
    (ν : MeasureTheory.Measure Y) [MeasureTheory.SFinite μ] [MeasureTheory.SFinite ν]
    (K : X → Y → ENNReal) (hK : Measurable (Function.uncurry K)) (f : Y → ENNReal) (hf : Measurable f)
    (h1 : ∀ y, ∫⁻ x, K x y ∂μ = 1) :
    ∫⁻ x, ∫⁻ y, K x y * f y ∂ν ∂μ = ∫⁻ y, f y ∂ν := by
  have hm : Measurable (Function.uncurry fun x y => K x y * f y) :=
    hK.mul (hf.comp measurable_snd)
  rw [MeasureTheory.lintegral_lintegral_swap hm.aemeasurable]
  congr 1; ext y
  have hKy : Measurable (fun x => K x y) := hK.comp (measurable_id.prodMk measurable_const)
  rw [MeasureTheory.lintegral_mul_const _ hKy, h1 y, one_mul]

/-! ### C12-03, C12-14: transverse equations from the constitutive derivative -/

/-- C12-03: if ΔΦ_b = div(∇Φ_b) and ΔΦ = div(Q'(z)∇Φ_b) with Q' = 1 + n_B (Q(z) = z + Q_⊥(z) and
Q_⊥' = n_B(z^{1/4}) by `Main.Galactic.Qperp_deriv`), then Δφ_⊥ = div(n_B ∇Φ_b) for φ_⊥ = Φ − Φ_b. -/
theorem transverse_poisson {F G : Type*} [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]
    (div : F →ₗ[ℝ] G) (lap : G → G) (Φ Φb : G) (gradΦb nBgrad : F)
    (hlin : lap (Φ - Φb) = lap Φ - lap Φb) (hb : lap Φb = div gradΦb)
    (hΦ : lap Φ = div (gradΦb + nBgrad)) : lap (Φ - Φb) = div nBgrad := by
  rw [hlin, hb, hΦ, map_add]; abel

/-- C12-14 (pointwise derivative): with z̃ = (e·g)²/a₀² and Q_⊥ = ∫₀ qint, the derivative of
a₀² Q_⊥(z̃) along v at g (with e·g ≠ 0) is 2 n_B(x̃)(e·g)(e·v), x̃ = z̃^{1/4}; summing with weights χ_P
gives 2 J_⊥ · v. -/
theorem constitutive_derivative (a0 eg ev : ℝ) (ha : 0 < a0) (heg : eg ≠ 0) :
    HasDerivAt (fun t : ℝ => a0 ^ 2 * ∫ s in (0:ℝ)..((eg + t * ev) ^ 2 / a0 ^ 2), Entropic.Main.Galactic.qint s)
      (2 * Entropic.Main.Galactic.nB (((eg) ^ 2 / a0 ^ 2) ^ ((1:ℝ)/4)) * eg * ev) 0 := by
  have hz : 0 < eg ^ 2 / a0 ^ 2 := by positivity
  have hQ := (Entropic.Main.Galactic.Qperp_deriv hz).1
  have hin : HasDerivAt (fun t : ℝ => (eg + t * ev) ^ 2 / a0 ^ 2) (2 * eg * ev / a0 ^ 2) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => eg + t * ev) ev 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const ev).const_add eg
    have : HasDerivAt (fun t : ℝ => (eg + t * ev) ^ 2) (2 * eg * ev) 0 := by
      convert h1.fun_pow 2 using 1; simp
    convert this.div_const (a0 ^ 2) using 1
  have hcomp := hQ.comp_of_eq (0:ℝ) hin (by simp)
  exact (hcomp.const_mul (a0 ^ 2)).congr_deriv (by field_simp)

/-! ### C03-71: cubic lattice symbol expansion -/

/-- C03-71: L_f(k) = 2w Σ_i [1 − cos(a k_i)] = w a²|k|² − (w a⁴/12) Σ_i k_i⁴ + O(a⁶k⁶), with the explicit
remainder bound 2|w| Σ_i (7/4320)|a k_i|⁶ when every |a k_i| ≤ 1. -/
theorem cubic_symbol (w a : ℝ) (k : Fin 3 → ℝ) (h : ∀ i, |a * k i| ≤ 1) :
    |2 * w * ∑ i, (1 - Real.cos (a * k i)) - (w * a ^ 2 * ∑ i, k i ^ 2 - w * a ^ 4 / 12 * ∑ i, k i ^ 4)| ≤
      2 * |w| * ∑ i, 7 / 4320 * |a * k i| ^ 6 := by
  have e : 2 * w * ∑ i, (1 - Real.cos (a * k i)) - (w * a ^ 2 * ∑ i, k i ^ 2 - w * a ^ 4 / 12 * ∑ i, k i ^ 4) =
      ∑ i, (-(2 * w)) * (Real.cos (a * k i) - (1 - (a * k i) ^ 2 / 2 + (a * k i) ^ 4 / 24)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_); ring
  rw [e, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [abs_mul, abs_neg, abs_mul, abs_two]
  have := Entropic.AppH10.cos_bound6 (h i)
  calc 2 * |w| * |Real.cos (a * k i) - (1 - (a * k i) ^ 2 / 2 + (a * k i) ^ 4 / 24)|
      ≤ 2 * |w| * (|a * k i| ^ 6 * (7 / 4320)) := by gcongr
    _ = 2 * |w| * (7 / 4320 * |a * k i| ^ 6) := by ring

end Entropic.Sweep.Alg
