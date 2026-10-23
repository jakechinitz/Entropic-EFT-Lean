import Entropic.AppQ.Algebra
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-! Appendix Q, finite models: the bond Hamiltonian and its coherent ground state (C15-47), separable
versus coherent bonds (C15-48), purification marginals (C15-49), the tridiagonal count operator
(C15-59), the three-facet fusion coisometry (C15-71), polar-normalized gluing (C15-73), the spin-1
pair spectrum (C15-05, multiplicities), and weight counts behind C15-12, C15-69, C15-70. -/

noncomputable section
namespace Entropic.AppQ.Fock
open Real Matrix
open scoped ComplexOrder

/-! ### C15-47: bond Hamiltonian on two fermion modes (basis |n_L n_R⟩, index 2n_L + n_R) -/

/-- Annihilators by Jordan–Wigner: c_L = a ⊗ I, c_R = Z ⊗ a (integer entries). -/
def cLF : Fin 4 → Fin 4 → ℤ := ![![0,0,1,0],![0,0,0,1],![0,0,0,0],![0,0,0,0]]
def cRF : Fin 4 → Fin 4 → ℤ := ![![0,1,0,0],![0,0,0,0],![0,0,0,-1],![0,0,0,0]]
def dlt (i j : Fin 4) : ℤ := if i = j then 1 else 0
/-- (A B)_{ij}, (A†B)_{ij}, (AB†)_{ij} for integer 4×4 tables. -/
def mm (A B : Fin 4 → Fin 4 → ℤ) (i j : Fin 4) : ℤ := (List.ofFn fun k => A i k * B k j).sum
def tr4 (A : Fin 4 → Fin 4 → ℤ) : Fin 4 → Fin 4 → ℤ := fun i j => A j i

/-- C15-47 (CAR): {c_L, c_L†} = {c_R, c_R†} = 1 and {c_L, c_R} = {c_L, c_R†} = 0. -/
theorem car : ∀ i j : Fin 4,
    mm cLF (tr4 cLF) i j + mm (tr4 cLF) cLF i j = dlt i j ∧ mm cRF (tr4 cRF) i j + mm (tr4 cRF) cRF i j = dlt i j ∧
      mm cLF cRF i j + mm cRF cLF i j = 0 ∧ mm cLF (tr4 cRF) i j + mm (tr4 cRF) cLF i j = 0 := by
  decide +kernel

def nLF : Fin 4 → Fin 4 → ℤ := mm (tr4 cLF) cLF
def nRF : Fin 4 → Fin 4 → ℤ := mm (tr4 cRF) cRF
def NF : Fin 4 → Fin 4 → ℤ := fun i j => nLF i j + nRF i j - dlt i j

/-- H_e = (n_L + n_R − 1)² + n_L + n_R − 2n_Ln_R − (c_L†c_R + c_R†c_L). -/
def HeF : Fin 4 → Fin 4 → ℤ := fun i j =>
  mm NF NF i j + nLF i j + nRF i j - 2 * mm nLF nRF i j - (mm (tr4 cLF) cRF i j + mm (tr4 cRF) cLF i j)

def HeX : Fin 4 → Fin 4 → ℤ := ![![1,0,0,0],![0,1,-1,0],![0,-1,1,0],![0,0,0,1]]

theorem He_explicit : ∀ i j : Fin 4, HeF i j = HeX i j := by decide +kernel

def He : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i j => (HeX i j : ℝ)

/-- C15-47: spectrum {0, 1, 1, 2} with eigenvectors |00⟩, |11⟩ (1), |01⟩+|10⟩ (0), |01⟩−|10⟩ (2);
the quadratic form is x₀₀² + x₁₁² + (x₀₁ − x₁₀)² ≥ 0, so H_e ⪰ 0 and its kernel is spanned by
(|01⟩ + |10⟩)/√2. -/
theorem bond_spectrum :
    He *ᵥ ![1,0,0,0] = ![1,0,0,0] ∧ He *ᵥ ![0,0,0,1] = ![0,0,0,1] ∧
      He *ᵥ ![0,1,1,0] = 0 ∧ He *ᵥ ![0,1,-1,0] = (2:ℝ) • ![0,1,-1,0] ∧
      (∀ x : Fin 4 → ℝ, x ⬝ᵥ (He *ᵥ x) = x 0 ^ 2 + x 3 ^ 2 + (x 1 - x 2) ^ 2) ∧
      (∀ x : Fin 4 → ℝ, He *ᵥ x = 0 → x 0 = 0 ∧ x 3 = 0 ∧ x 1 = x 2) := by
  refine ⟨?_, ?_, ?_, ?_, fun x => ?_, fun x hx => ?_⟩
  · ext i; fin_cases i <;> simp [He, HeX, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · ext i; fin_cases i <;> simp [He, HeX, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · ext i; fin_cases i <;> simp [He, HeX, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · ext i; fin_cases i <;> simp [He, HeX, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> norm_num
  · simp [He, HeX, Matrix.mulVec, dotProduct, Fin.sum_univ_four]; ring
  · have h0 := congrFun hx 0; have h1 := congrFun hx 1; have h3 := congrFun hx 3
    simp [He, HeX, Matrix.mulVec, dotProduct, Fin.sum_univ_four] at h0 h1 h3
    refine ⟨h0, h3, by linarith⟩

/-! ### C15-48: separable mixture versus coherent bond -/

/-- Partial trace over the right mode (index 2a + b). -/
def ptrR (ρ : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun a a' => ρ ⟨2 * a.val, by omega⟩ ⟨2 * a'.val, by omega⟩ + ρ ⟨2 * a.val + 1, by omega⟩ ⟨2 * a'.val + 1, by omega⟩

def rhoSep : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of ![![0,0,0,0],![0,1/2,0,0],![0,0,1/2,0],![0,0,0,0]]
def rhoOmega : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of ![![0,0,0,0],![0,1/2,1/2,0],![0,1/2,1/2,0],![0,0,0,0]]

/-- C15-48: both states have reduced state I/2 on the left mode (entropy ln 2), yet they differ;
ρ_Ω is pure (ρ² = ρ) while ρ_sep is not. -/
theorem separable_vs_coherent :
    ptrR rhoSep = (1/2 : ℝ) • 1 ∧ ptrR rhoOmega = (1/2 : ℝ) • 1 ∧ rhoSep ≠ rhoOmega ∧
      rhoOmega * rhoOmega = rhoOmega ∧ rhoSep * rhoSep ≠ rhoSep ∧
      -(2 * ((1/2 : ℝ) * Real.log (1/2))) = Real.log 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext a b; fin_cases a <;> fin_cases b <;> simp [ptrR, rhoSep] <;> norm_num
  · ext a b; fin_cases a <;> fin_cases b <;> simp [ptrR, rhoOmega] <;> norm_num
  · intro h; have := congrFun (congrFun h 1) 2; simp [rhoSep, rhoOmega] at this
  · ext i j; fin_cases i <;> fin_cases j <;> simp [rhoOmega, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num
  · intro h; have := congrFun (congrFun h 1) 1
    simp [rhoSep, Matrix.mul_apply, Fin.sum_univ_four] at this <;> norm_num at this
  · rw [one_div, Real.log_inv]; ring

/-- C15-49: the purification Σ_r √σ_r |r⟩|r⟩ has reduced state diag(σ). -/
theorem purification_marginal {n : Type*} [Fintype n] [DecidableEq n] (σ : n → ℝ) (hσ : ∀ r, 0 ≤ σ r)
    (r s : n) :
    ∑ t, ((if r = t then Real.sqrt (σ r) else 0) * (if s = t then Real.sqrt (σ s) else 0)) =
      if r = s then σ r else 0 := by
  by_cases h : r = s
  · subst h; simp [Finset.sum_ite_eq, Real.mul_self_sqrt (hσ r)]
  · rw [if_neg h]; apply Finset.sum_eq_zero; intro t _
    by_cases hr : r = t <;> by_cases hs : s = t
    · exact absurd (hr.trans hs.symm) h
    · simp [hs]
    · simp [hr]
    · simp [hr]

/-! ### C15-59: tridiagonal count operator -/

/-- Quadratic form of the tridiagonal matrix with diagonal a_n + a_{n+1} and off-diagonals −a_{n+1}. -/
def triQ (a ψ : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (M + 1), (a n + a (n + 1)) * ψ n ^ 2 - 2 * ∑ n ∈ Finset.range M, a (n + 1) * ψ n * ψ (n + 1)

/-- C15-59: with a₀ = a_{M+1} = 0 the form is Σ_{n<M} a_{n+1}(ψ_n − ψ_{n+1})². -/
theorem tri_sum_squares (a ψ : ℕ → ℝ) (M : ℕ) (h0 : a 0 = 0) (hM : a (M + 1) = 0) :
    triQ a ψ M = ∑ n ∈ Finset.range M, a (n + 1) * (ψ n - ψ (n + 1)) ^ 2 := by
  unfold triQ
  have e1 : ∑ n ∈ Finset.range (M + 1), a n * ψ n ^ 2 = ∑ n ∈ Finset.range M, a (n + 1) * ψ (n + 1) ^ 2 := by
    rw [Finset.sum_range_succ', h0]; simp
  have e2 : ∑ n ∈ Finset.range (M + 1), a (n + 1) * ψ n ^ 2 = ∑ n ∈ Finset.range M, a (n + 1) * ψ n ^ 2 := by
    rw [Finset.sum_range_succ, hM]; simp
  have e3 : ∑ n ∈ Finset.range M, a (n + 1) * (ψ n - ψ (n + 1)) ^ 2 =
      ∑ n ∈ Finset.range M, a (n + 1) * ψ n ^ 2 + ∑ n ∈ Finset.range M, a (n + 1) * ψ (n + 1) ^ 2 -
        2 * ∑ n ∈ Finset.range M, a (n + 1) * ψ n * ψ (n + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [e3, ← e1, ← e2, ← Finset.sum_add_distrib]
  congr 1; exact Finset.sum_congr rfl (fun n _ => by ring)

/-- C15-59: with a_n = √(n(M − n + 1)) the form is ⪰ 0 and vanishes only on constant vectors. -/
theorem flat_ground_state (M : ℕ) (ψ : ℕ → ℝ) :
    let a : ℕ → ℝ := fun n => Real.sqrt (n * ((M:ℝ) - n + 1))
    0 ≤ triQ a ψ M ∧ (triQ a ψ M = 0 → ∀ n, n ≤ M → ψ n = ψ 0) := by
  intro a
  have h0 : a 0 = 0 := by simp [a]
  have hM : a (M + 1) = 0 := by simp [a]
  have hpos : ∀ n, n < M → 0 < a (n + 1) := by
    intro n hn
    apply Real.sqrt_pos.mpr
    have : ((n:ℝ) + 1) ≤ M := by exact_mod_cast hn
    push_cast; nlinarith
  rw [tri_sum_squares a ψ M h0 hM]
  refine ⟨Finset.sum_nonneg (fun n _ => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)), fun h => ?_⟩
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun n _ => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))).mp h
  have step : ∀ n, n < M → ψ (n + 1) = ψ n := by
    intro n hn
    have := hz n (Finset.mem_range.mpr hn)
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 (hpos n hn).ne'
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1; linarith
  intro n hn
  induction n with
  | zero => rfl
  | succ k ih => rw [step k (by omega), ih (by omega)]

/-! ### C15-71: three-facet fusion coisometry -/

def c6 (r : Fin 7) : ℕ := Nat.choose 6 r.val

/-- Σ_{r₁+r₂+r₃=R} C(6,r₁)C(6,r₂)C(6,r₃) = C(18,R) (Vandermonde), checked for every R ≤ 18. -/
theorem vandermonde3 : ∀ R : Fin 19,
    (List.ofFn fun r1 : Fin 7 => (List.ofFn fun r2 : Fin 7 => (List.ofFn fun r3 : Fin 7 =>
      if r1.val + r2.val + r3.val = R.val then c6 r1 * c6 r2 * c6 r3 else 0).sum).sum).sum =
      Nat.choose 18 R.val := by decide +kernel

/-- F₃(R, r) = δ_{R, Σr} √(C(6,r₁)C(6,r₂)C(6,r₃)/C(18,R)). -/
def F3 (R : Fin 19) (r : Fin 7 × Fin 7 × Fin 7) : ℝ :=
  if r.1.val + r.2.1.val + r.2.2.val = R.val then
    Real.sqrt ((c6 r.1 * c6 r.2.1 * c6 r.2.2 : ℕ) / (Nat.choose 18 R.val : ℝ)) else 0

/-- C15-71: F₃F₃ᵀ = I₁₉. -/
theorem F3_coisometry (R R' : Fin 19) :
    ∑ r, F3 R r * F3 R' r = if R = R' then 1 else 0 := by
  by_cases h : R = R'
  · subst h
    rw [if_pos rfl]
    have hC : (0:ℝ) < Nat.choose 18 R.val := by exact_mod_cast Nat.choose_pos (by omega)
    have e : ∀ r : Fin 7 × Fin 7 × Fin 7, F3 R r * F3 R r =
        (if r.1.val + r.2.1.val + r.2.2.val = R.val then (c6 r.1 * c6 r.2.1 * c6 r.2.2 : ℕ) else 0 : ℕ) /
          (Nat.choose 18 R.val : ℝ) := by
      intro r; unfold F3; split_ifs
      · rw [Real.mul_self_sqrt (by positivity)]
      · simp
    simp only [e, ← Finset.sum_div]
    rw [div_eq_one_iff_eq hC.ne']
    have hv := vandermonde3 R
    simp only [List.sum_ofFn] at hv
    rw [Fintype.sum_prod_type, ← hv]; push_cast
    refine Finset.sum_congr rfl (fun r1 _ => ?_)
    rw [Fintype.sum_prod_type]
  · rw [if_neg h]
    apply Finset.sum_eq_zero; intro r _
    unfold F3; split_ifs with h1 h2 <;> first | exact absurd (Fin.ext (h1.symm.trans h2)) h | ring

/-! ### C15-73: polar-normalized gluing -/

section Polar
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- C15-73: if R has injective vecMul (equivalently R is surjective), RR† is positive definite, and with
T = (RR†)^{−1/2} built from the spectral decomposition, F = TR satisfies FF† = I and F† is an isometry. -/
theorem polar_gluing (R : Matrix m n ℂ) (hR : Function.Injective R.vecMul) :
    (R * Rᴴ).PosDef ∧ ∃ T : Matrix m m ℂ, Tᴴ = T ∧ (T * R) * (T * R)ᴴ = 1 ∧ (T * R)ᴴᴴ * (T * R)ᴴ = 1 := by
  have hS : (R * Rᴴ).PosDef := Matrix.PosDef.mul_conjTranspose_self R hR
  refine ⟨hS, ?_⟩
  set U : Matrix m m ℂ := (hS.1.eigenvectorUnitary : Matrix m m ℂ)
  set ev := hS.1.eigenvalues
  have hU1 : star U * U = 1 := Unitary.coe_star_mul_self hS.1.eigenvectorUnitary
  have hU2 : U * star U = 1 := Unitary.coe_mul_star_self hS.1.eigenvectorUnitary
  have hspec : R * Rᴴ = U * diagonal (fun i => ((ev i : ℝ) : ℂ)) * star U := by
    have := hS.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [Function.comp_def] using this
  set T : Matrix m m ℂ := U * diagonal (fun i => (((ev i) ^ (-(1:ℝ)/2) : ℝ) : ℂ)) * star U
  have hpos : ∀ i, 0 < ev i := hS.eigenvalues_pos
  have hTh : Tᴴ = T := by
    simp only [T, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
    have hs : (star fun i => (((ev i) ^ (-(1:ℝ)/2) : ℝ) : ℂ)) = fun i => (((ev i) ^ (-(1:ℝ)/2) : ℝ) : ℂ) := by
      funext i; simp
    rw [hs]
  have key : T * (R * Rᴴ) * T = 1 := by
    rw [hspec]
    simp only [T, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hU1, Matrix.one_mul, ← Matrix.mul_assoc (star U) U, hU1, Matrix.one_mul,
      ← Matrix.mul_assoc (diagonal _) (diagonal _), Matrix.diagonal_mul_diagonal,
      ← Matrix.mul_assoc (diagonal _) (diagonal _), Matrix.diagonal_mul_diagonal]
    have hd : (fun i => (((ev i) ^ (-(1:ℝ)/2) : ℝ) : ℂ) * ((ev i : ℝ) : ℂ) * (((ev i) ^ (-(1:ℝ)/2) : ℝ) : ℂ)) =
        fun _ => (1 : ℂ) := by
      funext i
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
      have h1 : (ev i) ^ (-(1:ℝ)/2) * ev i * (ev i) ^ (-(1:ℝ)/2) = 1 := by
        rw [mul_comm ((ev i) ^ (-(1:ℝ)/2)) (ev i), mul_assoc, ← Real.rpow_add (hpos i)]
        rw [show -(1:ℝ)/2 + -(1:ℝ)/2 = -1 by norm_num, Real.rpow_neg_one, mul_inv_cancel₀ (hpos i).ne']
      rw [h1]; simp
    rw [hd, Matrix.diagonal_one, Matrix.one_mul, hU2]
  have hF : (T * R) * (T * R)ᴴ = 1 := by
    rw [Matrix.conjTranspose_mul, hTh, Matrix.mul_assoc, ← Matrix.mul_assoc R, ← Matrix.mul_assoc]; exact key
  exact ⟨T, hTh, hF, by rw [Matrix.conjTranspose_conjTranspose]; exact hF⟩
end Polar

end Entropic.AppQ.Fock
