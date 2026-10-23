import Entropic.AppCDE.Frame
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! Appendix H.9b–H.15 kinematics in this range: Pauli gluing algebra, the diamond Dirac
cone, the cubic Dresselhaus term, Clifford dispersion, weak-field proper time, Johnson-graph
spectra (ledger C07-60, -92, -93, -95, -98, -101, -107, -120, -123). -/

noncomputable section
namespace Entropic.AppH1
open Matrix Complex
open scoped Kronecker

/-- Pauli matrices. -/
def σx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def σy : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]
def σz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
def sdot (a : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (a 0 : ℂ) • σx + (a 1 : ℂ) • σy + (a 2 : ℂ) • σz

/-- C07-95: (a·σ)(b·σ) = (a·b)I + i(a×b)·σ; so U_l†U_j = n_l·n_j I + i(n_l×n_j)·σ. -/
theorem pauli_product (a b : Fin 3 → ℝ) :
    sdot a * sdot b = ((a 0 * b 0 + a 1 * b 1 + a 2 * b 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      I • sdot ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sdot, σx, σy, σz, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    simp [Complex.ext_iff, I_sq] <;> constructor <;> ring

/-- U_j = −i n_j·σ is unitary when |n_j| = 1: U_j†U_j = (n·n)I = I. -/
theorem gluing_unitary (a : Fin 3 → ℝ) (ha : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 = 1) :
    sdot a * sdot a = 1 := by
  rw [pauli_product]
  have : a 0 * a 0 + a 1 * a 1 + a 2 * a 2 = 1 := by nlinarith
  rw [this]
  ext i j; fin_cases i <;> fin_cases j <;> simp [sdot, σx, σy, σz] <;> ring_nf

theorem sdot_add (a b : Fin 3 → ℝ) : sdot (a + b) = sdot a + sdot b := by
  simp only [sdot, Pi.add_apply]; push_cast; simp only [add_smul]; abel

theorem sdot_smul (c : ℝ) (a : Fin 3 → ℝ) : sdot (c • a) = (c : ℂ) • sdot a := by
  simp only [sdot, Pi.smul_apply, smul_eq_mul]; push_cast; simp only [smul_add, smul_smul]

theorem sdot_sum {ι : Type*} (s : Finset ι) (a : ι → Fin 3 → ℝ) :
    sdot (∑ j ∈ s, a j) = ∑ j ∈ s, sdot (a j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sdot]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, sdot_add, ih]

/-- C07-92, C07-101: Σ_j U_j = −iΣ_j n_j·σ = 0 for the tetrahedral frame (so the uniform
balanced states are exact zero modes and Q(0) = 0). -/
theorem gluing_sum_zero : ∑ j : Fin 4, sdot (Entropic.AppCDE.d j) = 0 := by
  rw [← sdot_sum]
  have : ∑ j : Fin 4, Entropic.AppCDE.d j = 0 := by
    funext a; simp only [Finset.sum_apply, Pi.zero_apply]; exact Entropic.AppCDE.frame_sum_zero a
  rw [this]; simp [sdot]

/-- C07-93: the linear term of Q(k) = tΣ_j U_j e^{ik·d_j}, d_j = (√3a/4)n_j, is
t·Σ_j (−i n_j·σ)(i k·d_j) = t(√3a/4)Σ_j (n_j·k)(n_j·σ) = (ta/√3) σ·k, by Σ n nᵀ = (4/3)I. -/
theorem dirac_cone_linear (k : Fin 3 → ℝ) (t a : ℝ) :
    ∑ j : Fin 4, ((t * (Real.sqrt 3 * a / 4) * (∑ c, Entropic.AppCDE.d j c * k c) : ℝ) : ℂ) •
      sdot (Entropic.AppCDE.d j) = ((t * a / Real.sqrt 3 : ℝ) : ℂ) • sdot k := by
  have hfr : ∑ j : Fin 4, (∑ c, Entropic.AppCDE.d j c * k c) • Entropic.AppCDE.d j = (4/3 : ℝ) • k := by
    funext b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have : ∀ j : Fin 4, (∑ c, Entropic.AppCDE.d j c * k c) * Entropic.AppCDE.d j b =
        ∑ c, (Entropic.AppCDE.d j c * Entropic.AppCDE.d j b) * k c := by
      intro j; rw [Finset.sum_mul]; congr 1; ext c; ring
    simp_rw [this]; rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, Entropic.AppCDE.frame_identity]
    simp [ite_mul]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 3 := by positivity
  have e : ∀ j : Fin 4, ((t * (Real.sqrt 3 * a / 4) * (∑ c, Entropic.AppCDE.d j c * k c) : ℝ) : ℂ) •
      sdot (Entropic.AppCDE.d j) = ((t * (Real.sqrt 3 * a / 4) : ℝ) : ℂ) •
        sdot ((∑ c, Entropic.AppCDE.d j c * k c) • Entropic.AppCDE.d j) := by
    intro j; rw [sdot_smul, smul_smul]; push_cast; ring_nf
  simp_rw [e, ← Finset.smul_sum, ← sdot_sum, hfr, sdot_smul, smul_smul]
  congr 1; push_cast; field_simp; rw [show (Real.sqrt 3 : ℂ) ^ 2 = ((Real.sqrt 3 ^ 2 : ℝ) : ℂ) by
    push_cast; ring, h3]; push_cast; ring

/-- C07-98: with a = k_x², b = k_y², c = k_z² ≥ 0, |κ|² = a(b−c)² + b(c−a)² + c(a−b)² ≤ (a+b+c)³/4,
so |κ| ≤ 1/2 on the unit sphere, with equality along ⟨110⟩ and κ = 0 along ⟨100⟩, ⟨111⟩. -/
theorem dresselhaus_bound {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * (b - c) ^ 2 + b * (c - a) ^ 2 + c * (a - b) ^ 2 ≤ (a + b + c) ^ 3 / 4 := by
  nlinarith [mul_nonneg ha (sq_nonneg (a - b - c)), mul_nonneg hb (sq_nonneg (b - c - a)),
    mul_nonneg hc (sq_nonneg (c - a - b)), mul_nonneg (mul_nonneg ha hb) hc,
    mul_nonneg ha (sq_nonneg (b - c)), mul_nonneg hb (sq_nonneg (c - a)), mul_nonneg hc (sq_nonneg (a - b)),
    sq_nonneg (a + b + c), mul_nonneg (add_nonneg (add_nonneg ha hb) hc) (sq_nonneg (a - b)),
    mul_nonneg (add_nonneg (add_nonneg ha hb) hc) (sq_nonneg (b - c)),
    mul_nonneg (add_nonneg (add_nonneg ha hb) hc) (sq_nonneg (c - a))]

theorem dresselhaus_extremes :
    (1:ℝ) * (1 - 0) ^ 2 + 1 * (0 - 1) ^ 2 + 0 * (1 - 1) ^ 2 = (1 + 1 + 0) ^ 3 / 4 ∧
      (1:ℝ) * (0 - 0) ^ 2 + 0 * (0 - 1) ^ 2 + 0 * (1 - 0) ^ 2 = 0 ∧
      (1:ℝ) * (1 - 1) ^ 2 + 1 * (1 - 1) ^ 2 + 1 * (1 - 1) ^ 2 = 0 := by norm_num

/-- C07-107: for a Hermitian Bloch matrix with D(−k) = conj D(k), D(−k) = D(k)ᵀ has the same
characteristic polynomial, hence the same spectrum: band speeds are even in k. -/
theorem reality_even_spectrum {n : Type*} [Fintype n] [DecidableEq n] (D Dm : Matrix n n ℂ)
    (hH : Dᴴ = D) (hR : Dm = D.map (starRingEnd ℂ)) : Dm.charpoly = D.charpoly := by
  have : Dm = D.transpose := by
    rw [hR]; ext i j
    have := congrFun (congrFun hH j) i
    simp [Matrix.conjTranspose_apply] at this
    simp [Matrix.map_apply, Matrix.transpose_apply, ← this]
  rw [this, Matrix.charpoly_transpose]

/-- C07-120: if {γ^μ, γ^ν} = −2g^{μν}I then (γ^μp_μ)² = −(g^{μν}p_μp_ν)I; with
g = diag(−1,1,1,1), p = (−E/c, 𝐩) and (γ·p − mc)ψ = 0, ψ ≠ 0, one gets E² = c²|𝐩|² + m²c⁴. -/
theorem clifford_square {k : Type*} [Fintype k] [DecidableEq k] (γ : Fin 4 → Matrix k k ℂ)
    (g : Fin 4 → Fin 4 → ℂ) (hg : ∀ μ ν, g μ ν = g ν μ)
    (hcl : ∀ μ ν, γ μ * γ ν + γ ν * γ μ = (-2 * g μ ν) • (1 : Matrix k k ℂ)) (p : Fin 4 → ℂ) :
    (∑ μ, p μ • γ μ) * (∑ μ, p μ • γ μ) = (-(∑ μ, ∑ ν, g μ ν * p μ * p ν)) • (1 : Matrix k k ℂ) := by
  have h2 : (2 : ℂ) • ((∑ μ, p μ • γ μ) * (∑ μ, p μ • γ μ)) =
      ∑ μ, ∑ ν, (p μ * p ν) • (γ μ * γ ν + γ ν * γ μ) := by
    rw [Finset.sum_mul_sum, two_smul]
    conv_rhs => simp only [smul_add, Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν _ => ?_))
      rw [smul_mul_smul_comm]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν _ => ?_))
      rw [smul_mul_smul_comm, mul_comm (p ν)]
  simp_rw [hcl, smul_smul] at h2
  simp_rw [← Finset.sum_smul] at h2
  have h2' : (2 : ℂ) • ((∑ μ, p μ • γ μ) * (∑ μ, p μ • γ μ)) =
      (2 : ℂ) • ((-(∑ μ, ∑ ν, g μ ν * p μ * p ν)) • (1 : Matrix k k ℂ)) := by
    rw [h2, smul_smul]; congr 1
    rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun ν _ => by ring)
  exact smul_right_injective _ (two_ne_zero) h2'

theorem dirac_dispersion {E c m px py pz : ℝ} (hc : c ≠ 0)
    (h : -(-(E / c) ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2) = (m * c) ^ 2) :
    E ^ 2 = c ^ 2 * (px ^ 2 + py ^ 2 + pz ^ 2) + m ^ 2 * c ^ 4 := by
  field_simp at h; nlinarith [h]

/-- C07-123: dτ/dt = √(1 + 2Φε − (1 − 2Ψε)v²ε) with ε = 1/c² has slope Φ − v²/2 at ε = 0,
so S_d = ∫dt[−mc² + ½mv² − mΦ + O(c⁻²)]. -/
theorem proper_time_slope (Φ Ψ v : ℝ) :
    HasDerivAt (fun ε : ℝ => Real.sqrt (1 + 2 * Φ * ε - (1 - 2 * Ψ * ε) * v ^ 2 * ε))
      (Φ - v ^ 2 / 2) 0 := by
  have hin : HasDerivAt (fun ε : ℝ => 1 + 2 * Φ * ε - (1 - 2 * Ψ * ε) * v ^ 2 * ε)
      (2 * Φ - v ^ 2) 0 := by
    have h1 := ((hasDerivAt_id (0:ℝ)).const_mul (2 * Φ)).const_add 1
    have h2 := ((((hasDerivAt_id (0:ℝ)).const_mul (2 * Ψ)).const_sub 1).mul_const (v ^ 2)).mul
      (hasDerivAt_id (0:ℝ))
    have := h1.sub h2
    convert this using 1
    · funext ε; simp
    · simp
  have := hin.sqrt (by simp)
  convert this using 1; simp; ring

/-! ### Johnson-graph edge spectra (C07-60) -/

/-- The 21 two-subsets of {0,…,6}, listed. -/
def pairs : Fin 21 → Fin 7 × Fin 7 := fun i =>
  ![(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),
    (3,4),(3,5),(3,6),(4,5),(4,6),(5,6)] i

def inter (i j : Fin 21) : ℕ :=
  (if (pairs i).1 = (pairs j).1 then 1 else 0) + (if (pairs i).1 = (pairs j).2 then 1 else 0) +
    (if (pairs i).2 = (pairs j).1 then 1 else 0) + (if (pairs i).2 = (pairs j).2 then 1 else 0)

/-- `inter` is the size of the intersection of the two listed pairs. -/
theorem inter_eq (i j : Fin 21) :
    inter i j = (({(pairs i).1, (pairs i).2} : Finset (Fin 7)) ∩ {(pairs j).1, (pairs j).2}).card := by
  revert i j; decide

def A1 : Matrix (Fin 21) (Fin 21) ℤ := Matrix.of fun i j => if inter i j = 1 then 1 else 0
def A0 : Matrix (Fin 21) (Fin 21) ℤ := Matrix.of fun i j => if inter i j = 0 then 1 else 0

theorem mul_entry (M N : Matrix (Fin 21) (Fin 21) ℤ) (i j : Fin 21) :
    (M * N) i j = (List.ofFn fun k => M i k * N k j).sum := by
  rw [Matrix.mul_apply, List.sum_ofFn]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A1_sq_entry : ∀ i j : Fin 21, (List.ofFn fun k => A1 i k * A1 k j).sum =
    (if i = j then 10 else 0) + 5 * A1 i j + 4 * A0 i j := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A0_sq_entry : ∀ i j : Fin 21, (List.ofFn fun k => A0 i k * A0 k j).sum =
    (if i = j then 10 else 0) + 3 * A0 i j + 6 * A1 i j := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A10_entry : ∀ i j : Fin 21, (List.ofFn fun k => A1 i k * A0 k j).sum =
    4 * A1 i j + 6 * A0 i j := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A01_entry : ∀ i j : Fin 21, (List.ofFn fun k => A0 i k * A1 k j).sum =
    4 * A1 i j + 6 * A0 i j := by decide +kernel

theorem diag_zero : ∀ i : Fin 21, A1 i i = 0 ∧ A0 i i = 0 := by decide

/-- The strongly-regular-graph relations of J(7,2) and its complement K(7,2). -/
theorem A1_sq : A1 * A1 = (10:ℤ) • (1 : Matrix (Fin 21) (Fin 21) ℤ) + (5:ℤ) • A1 + (4:ℤ) • A0 := by
  ext i j; rw [mul_entry, A1_sq_entry]
  by_cases h : i = j <;>
    simp only [h, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, if_true, if_false] <;> ring

theorem A0_sq : A0 * A0 = (10:ℤ) • (1 : Matrix (Fin 21) (Fin 21) ℤ) + (3:ℤ) • A0 + (6:ℤ) • A1 := by
  ext i j; rw [mul_entry, A0_sq_entry]
  by_cases h : i = j <;>
    simp only [h, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, if_true, if_false] <;> ring

theorem A10 : A1 * A0 = (4:ℤ) • A1 + (6:ℤ) • A0 := by
  ext i j; rw [mul_entry, A10_entry]; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem A01 : A0 * A1 = (4:ℤ) • A1 + (6:ℤ) • A0 := by
  ext i j; rw [mul_entry, A01_entry]; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem trace_A1 : A1.trace = 0 := by simp [Matrix.trace, Matrix.diag, (diag_zero _).1]
theorem trace_A0 : A0.trace = 0 := by simp [Matrix.trace, Matrix.diag, (diag_zero _).2]

theorem num (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : Matrix (Fin 21) (Fin 21) ℤ) = ((OfNat.ofNat n : ℤ)) • (1 : Matrix (Fin 21) (Fin 21) ℤ) := by
  rw [zsmul_eq_mul, mul_one]; norm_cast

/-- C07-60: (A₁ + 2)(A₁ − 3)(A₁ − 10) = 0, Tr A₁ = 0, Tr A₁² = 210; (A₀ + 4)(A₀ − 1)(A₀ − 10) = 0,
Tr A₀ = 0, Tr A₀² = 210. -/
theorem johnson_polynomials :
    (A1 + 2) * (A1 - 3) * (A1 - 10) = 0 ∧ A1.trace = 0 ∧ (A1 * A1).trace = 210 ∧
      (A0 + 4) * (A0 - 1) * (A0 - 10) = 0 ∧ A0.trace = 0 ∧ (A0 * A0).trace = 210 := by
  have hp1 : (A1 + 2) * (A1 - 3) * (A1 - 10) =
      A1 * (A1 * A1) + (-11:ℤ) • (A1 * A1) + (4:ℤ) • A1 + (60:ℤ) • (1 : Matrix (Fin 21) (Fin 21) ℤ) := by
    rw [num 2, num 3, num 10]; noncomm_ring
  have hp0 : (A0 + 4) * (A0 - 1) * (A0 - 10) =
      A0 * (A0 * A0) + (-7:ℤ) • (A0 * A0) + (-34:ℤ) • A0 + (40:ℤ) • (1 : Matrix (Fin 21) (Fin 21) ℤ) := by
    rw [num 4, num 10]; noncomm_ring
  refine ⟨?_, trace_A1, ?_, ?_, trace_A0, ?_⟩
  · rw [hp1, A1_sq]
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, A1_sq, A10, smul_add, smul_smul]
    module
  · rw [A1_sq]; simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, trace_A1, trace_A0,
      Fintype.card_fin, smul_zero]; norm_num
  · rw [hp0, A0_sq]
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, A0_sq, A01, smul_add, smul_smul]
    module
  · rw [A0_sq]; simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, trace_A1, trace_A0,
      Fintype.card_fin, smul_zero]; norm_num

/-- With eigenvalues restricted to the roots, the multiplicities (m₋, m₊, m₁₀) solve
m₋ + m₊ + m₁₀ = 21, Σλ m = 0, Σλ² m = 210, whose unique solution is (14, 6, 1) for A₁ and
(6, 14, 1) for A₀. -/
theorem johnson_multiplicities :
    (∀ a b c : ℤ, a + b + c = 21 → -2 * a + 3 * b + 10 * c = 0 → 4 * a + 9 * b + 100 * c = 210 →
      a = 14 ∧ b = 6 ∧ c = 1) ∧
    (∀ a b c : ℤ, a + b + c = 21 → -4 * a + 1 * b + 10 * c = 0 → 16 * a + 1 * b + 100 * c = 210 →
      a = 6 ∧ b = 14 ∧ c = 1) := by
  constructor <;> intro a b c h1 h2 h3 <;> refine ⟨by omega, by omega, by omega⟩


/-! ### Relational frame gauge covariance (C07-76) -/

section Gauge
variable {G ι : Type*} [Group G]

/-- g_{cc'} := R_c U_{cc'} R_{c'}⁻¹. -/
def relFrame (R : ι → G) (U : ι → ι → G) (c c' : ι) : G := R c * U c c' * (R c')⁻¹

/-- C07-76: g_{c'c} = g_{cc'}⁻¹ when U_{c'c} = U_{cc'}⁻¹. -/
theorem relFrame_inv (R : ι → G) (U : ι → ι → G) (hU : ∀ c c', U c' c = (U c c')⁻¹) (c c' : ι) :
    relFrame R U c' c = (relFrame R U c c')⁻¹ := by
  rw [relFrame, relFrame, hU c c']; group

/-- Under R_c ↦ h_cR_c, g_{cc'} ↦ h_c g_{cc'} h_{c'}⁻¹. -/
theorem relFrame_gauge (R h : ι → G) (U : ι → ι → G) (c c' : ι) :
    relFrame (fun x => h x * R x) U c c' = h c * relFrame R U c c' * (h c')⁻¹ := by
  simp [relFrame, mul_assoc]

/-- A loop product based at c is R_c U_loop R_c⁻¹. -/
theorem relFrame_loop (R : ι → G) (U : ι → ι → G) (c₁ c₂ c₃ : ι) :
    relFrame R U c₁ c₂ * relFrame R U c₂ c₃ * relFrame R U c₃ c₁ =
      R c₁ * (U c₁ c₂ * U c₂ c₃ * U c₃ c₁) * (R c₁)⁻¹ := by
  simp [relFrame, mul_assoc]

/-- The conjugacy class of the loop product is gauge invariant. -/
theorem relFrame_loop_conj (R h : ι → G) (U : ι → ι → G) (c₁ c₂ c₃ : ι) :
    IsConj (relFrame R U c₁ c₂ * relFrame R U c₂ c₃ * relFrame R U c₃ c₁)
      (relFrame (fun x => h x * R x) U c₁ c₂ * relFrame (fun x => h x * R x) U c₂ c₃ *
        relFrame (fun x => h x * R x) U c₃ c₁) := by
  rw [isConj_iff]
  refine ⟨h c₁, ?_⟩
  simp only [relFrame_gauge]; group

end Gauge


/-! ### Electron calibration algebra (C07-11, -28, -29, -31, -32) -/

/-- C07-11: Tr((Π ⊗ Π')(ρ ⊗ ρ')) = Tr(Πρ)Tr(Π'ρ'); iterating gives the seven-fold product. -/
theorem trace_kron_factor {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (P ρ : Matrix m m ℂ) (P' ρ' : Matrix n n ℂ) :
    ((P ⊗ₖ P') * (ρ ⊗ₖ ρ')).trace = (P * ρ).trace * (P' * ρ').trace := by
  rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]

/-- −ln of a product of positive factors is the sum of the −ln's. -/
theorem neg_log_prod {ι : Type*} (s : Finset ι) (t : ι → ℝ) (ht : ∀ i ∈ s, 0 < t i) :
    -Real.log (∏ i ∈ s, t i) = ∑ i ∈ s, -Real.log (t i) := by
  rw [Real.log_prod (fun i hi => (ht i hi).ne'), ← Finset.sum_neg_distrib]

/-- C07-28: m c² = (3/2)(ħ/τ)(−ln(1−r)) fixes τ = −(3/2)(ħ/(mc²)) ln(1−r), L = cτ. -/
theorem electron_calibration {ħ τ m c r : ℝ} (hτ : τ ≠ 0) (hmc : m * c ^ 2 ≠ 0)
    (h : m * c ^ 2 = (3/2) * (-(ħ / τ) * Real.log (1 - r))) :
    τ = -(3/2) * (ħ / (m * c ^ 2)) * Real.log (1 - r) := by
  have hm : m ≠ 0 := left_ne_zero_of_mul hmc
  have hc : c ≠ 0 := fun h0 => hmc (by simp [h0])
  have h2 := h; field_simp at h2
  field_simp; linear_combination h2

/-- C07-29: |−ln(1−r) − r − r²/2| ≤ |r|³/(1 − |r|) for |r| < 1. -/
theorem log_small_r {r : ℝ} (hr : |r| < 1) :
    |-Real.log (1 - r) - (r + r ^ 2 / 2)| ≤ |r| ^ 3 / (1 - |r|) := by
  have := Real.abs_log_sub_add_sum_range_le hr 2
  have e : ∑ i ∈ Finset.range 2, r ^ (i + 1) / (i + 1) = r + r ^ 2 / 2 := by
    simp [Finset.sum_range_succ]; norm_num
  rw [e] at this
  rw [show -Real.log (1 - r) - (r + r ^ 2 / 2) = -((r + r ^ 2 / 2) + Real.log (1 - r)) by ring, abs_neg]
  simpa using this

/-- C07-31: G⁽⁰⁾ := c³(L⁽⁰⁾)²/ħ with L⁽⁰⁾ = −(3/2)(ħ/(mc)) ln(1−r) equals (9/4)(ħc/m²)ln²(1−r). -/
theorem baseline_newton {ħ m c r : ℝ} (hħ : ħ ≠ 0) (hm : m ≠ 0) (hc : c ≠ 0) :
    c ^ 3 * (-(3/2) * (ħ / (m * c)) * Real.log (1 - r)) ^ 2 / ħ =
      (9/4) * (ħ * c / m ^ 2) * Real.log (1 - r) ^ 2 := by
  field_simp; ring

/-- C07-32: τ = Zτ⁽⁰⁾, L = cτ give L = ZL⁽⁰⁾ and G = c³L²/ħ = Z²G⁽⁰⁾. -/
theorem Ze_scaling (Z τ0 c ħ : ℝ) :
    c * (Z * τ0) = Z * (c * τ0) ∧ c ^ 3 * (c * (Z * τ0)) ^ 2 / ħ = Z ^ 2 * (c ^ 3 * (c * τ0) ^ 2 / ħ) := by
  constructor <;> ring

end Entropic.AppH1
