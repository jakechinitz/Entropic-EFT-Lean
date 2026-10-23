import Entropic.AppH1.Algebra
import Entropic.AppCDE.ElectronNumerics
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Appendix H.10: scalar identities, selection rules, symbols, gaps and numerics
(ledger C08-15, -19, -21 … -23, -29, -35, -37, -38, -41, -46 … -49, -56 … -58, -65, -68, -98). -/

noncomputable section
namespace Entropic.AppH10
open Real

/-- C08-15: with δS = −(2S∞/c²)Φ, G = c²κ/(8πγS∞) and Z_S = 2κS∞/c², the static capacity integrand
−(γ/2)|∇δS|² + κρδS equals Z_S(−|∇Φ|²/(8πG) − ρΦ) pointwise (g2 := |∇Φ|²). -/
theorem static_capacity {γ κ S c ρ Φ g2 : ℝ} (hγ : γ ≠ 0) (hκ : κ ≠ 0) (hS : S ≠ 0) (hc : c ≠ 0) :
    -(γ / 2) * ((2 * S / c ^ 2) ^ 2 * g2) + κ * ρ * (-(2 * S / c ^ 2) * Φ) =
      (2 * κ * S / c ^ 2) * (-g2 / (8 * π * (c ^ 2 * κ / (8 * π * γ * S))) - ρ * Φ) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp; ring

/-- C08-19: 0 < u < 1 gives α = √(1−u) ∈ (0,1) and α²¹ > 0. -/
theorem edge_factor_pos {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    0 < Real.sqrt (1 - u) ∧ Real.sqrt (1 - u) < 1 ∧ 0 < Real.sqrt (1 - u) ^ 21 := by
  have hp : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.mpr (by linarith)
  refine ⟨hp, ?_, pow_pos hp _⟩
  rw [Real.sqrt_lt' one_pos]; linarith

/-- C08-21 … C08-23 (dimension bookkeeping): 4·4 = 7 + 1 + 3 + 5, 3·3 = 1 + 3 + 5, and
shift (3) + symmetric spatial tensor (1 + 5) = 9. -/
theorem fiber_dimensions : 4 * 4 = 7 + 1 + 3 + 5 ∧ 3 * 3 = 1 + 3 + 5 ∧ 3 + (1 + 5) = 1 + 3 + 5 ∧
    (∀ N : ℕ, 2 * (3 * N) + 1 = 6 * N + 1) ∧ 2 * 3 + 1 = 7 := by
  refine ⟨rfl, rfl, rfl, fun N => by ring, rfl⟩

/-! ### Roots-of-unity filter (C08-29) -/

/-- Σ_{r<3} ω^{rJ} = 3 if 3 ∣ J and 0 otherwise, ω = e^{2πi/3}. -/
theorem cube_root_sum (J : ℕ) :
    ∑ r ∈ Finset.range 3, Complex.exp (2 * π * Complex.I / 3) ^ (r * J) =
      if 3 ∣ J then 3 else 0 := by
  have hω : IsPrimitiveRoot (Complex.exp (2 * π * Complex.I / 3)) 3 := by
    simpa using Complex.isPrimitiveRoot_exp 3 (by norm_num)
  have hrw : ∀ r : ℕ, Complex.exp (2 * π * Complex.I / 3) ^ (r * J) =
      (Complex.exp (2 * π * Complex.I / 3) ^ J) ^ r := by
    intro r; rw [← pow_mul, Nat.mul_comm r J]
  simp_rw [hrw]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    rw [pow_mul, hω.pow_eq_one, one_pow]; simp
  · have hprim : IsPrimitiveRoot (Complex.exp (2 * π * Complex.I / 3) ^ J) 3 := by
      apply hω.pow_of_coprime
      exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h))
    exact hprim.geom_sum_eq_zero (by norm_num)

/-- C08-29: Σ_{J ∈ 3ℕ} a_J = (1/3) Σ_{r=0}^{2} Σ_J a_J e^{2πirJ/3} for finitely supported a. -/
theorem roots_filter (s : Finset ℕ) (a : ℕ → ℂ) :
    ∑ J ∈ s.filter (fun J => 3 ∣ J), a J =
      (1/3) * ∑ r ∈ Finset.range 3, ∑ J ∈ s, a J * Complex.exp (2 * π * Complex.I / 3) ^ (r * J) := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, cube_root_sum, Finset.sum_filter]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  split_ifs <;> ring

/-! ### Frozen areas: the 3ℕ selection rule (C08-35) -/

/-- Two multiples of 3 at distance ≤ 2 coincide. -/
theorem selection (j j' : ℕ) (h : 3 ∣ j) (h' : 3 ∣ j') (hd : j ≤ j' + 2) (hd' : j' ≤ j + 2) : j = j' := by
  omega

/-- C08-35: if M changes an edge spin by at most 2 (M j j' = 0 for |j − j'| > 2), its compression to
spins in 3ℕ is diagonal and commutes with every operator diagonal in the spin. -/
theorem frozen_areas {ι : Type*} [Fintype ι] [DecidableEq ι] (spin : ι → ℕ) (hinj : Function.Injective spin)
    (M A : Matrix ι ι ℂ) (hM : ∀ i i', (spin i' + 2 < spin i ∨ spin i + 2 < spin i') → M i i' = 0)
    (hA : ∀ i i', i ≠ i' → A i i' = 0) (h3 : ∀ i, 3 ∣ spin i) : M * A = A * M := by
  have hdiag : ∀ i i', i ≠ i' → M i i' = 0 := by
    intro i i' hne
    apply hM
    by_contra hc; push_neg at hc
    exact hne (hinj (selection _ _ (h3 i) (h3 i') hc.1 hc.2))
  ext i k
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single i (fun b _ hb => by rw [hdiag i b (Ne.symm hb), zero_mul]) (by simp),
    Finset.sum_eq_single k (fun b _ hb => by rw [hdiag b k hb, mul_zero]) (by simp)]
  by_cases hik : i = k
  · subst hik; ring
  · rw [hA i k hik]; ring

/-! ### Symbol expansion and periodicity (C08-37, C08-38) -/

/-- Sixth-order cosine bound from the exponential remainder: |cos y − (1 − y²/2 + y⁴/24)| ≤ 7|y|⁶/4320. -/
theorem cos_bound6 {y : ℝ} (hy : |y| ≤ 1) :
    |Real.cos y - (1 - y ^ 2 / 2 + y ^ 4 / 24)| ≤ |y| ^ 6 * (7 / 4320) := by
  have hn : ‖(y : ℂ) * Complex.I‖ ≤ 1 := by simpa using hy
  have hb := Complex.exp_bound hn (n := 6) (by norm_num)
  have hs : ∑ m ∈ Finset.range 6, ((y : ℂ) * Complex.I) ^ m / (m.factorial : ℂ) =
      ((1 - y ^ 2 / 2 + y ^ 4 / 24 : ℝ) : ℂ) + ((y - y ^ 3 / 6 + y ^ 5 / 120 : ℝ) : ℂ) * Complex.I := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    push_cast
    ring_nf
    have i3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
    have i4 : Complex.I ^ 4 = 1 := by rw [show (4:ℕ) = 2 + 2 from rfl, pow_add, Complex.I_sq]; ring
    have i5 : Complex.I ^ 5 = Complex.I := by rw [pow_succ, i4, one_mul]
    rw [Complex.I_sq, i3, i4, i5]
    ring
  rw [hs] at hb
  have hre : (Complex.exp ((y : ℂ) * Complex.I) - (((1 - y ^ 2 / 2 + y ^ 4 / 24 : ℝ) : ℂ) +
      ((y - y ^ 3 / 6 + y ^ 5 / 120 : ℝ) : ℂ) * Complex.I)).re = Real.cos y - (1 - y ^ 2 / 2 + y ^ 4 / 24) := by
    simp [Complex.exp_ofReal_mul_I_re, ← Complex.ofReal_pow]
  rw [← hre]
  refine (Complex.abs_re_le_norm _).trans (hb.trans (le_of_eq ?_))
  simp [Nat.factorial]; norm_num

/-- C08-37: (2/9)(1 − cos 3ξ) = ξ² − (3/4)ξ⁴ + O(ξ⁶), explicitly with |error| ≤ (567/1440)|ξ|⁶·(1/… )
for |ξ| ≤ 1/3. -/
theorem symbol_expansion {ξ : ℝ} (hξ : |ξ| ≤ 1/3) :
    |(2/9) * (1 - Real.cos (3 * ξ)) - (ξ ^ 2 - (3/4) * ξ ^ 4)| ≤ (2/9) * (7/4320) * 729 * |ξ| ^ 6 := by
  have h3 : |3 * ξ| ≤ 1 := by rw [abs_mul]; norm_num; linarith
  have hb := cos_bound6 h3
  have e : (2/9) * (1 - Real.cos (3 * ξ)) - (ξ ^ 2 - (3/4) * ξ ^ 4) =
      -(2/9) * (Real.cos (3 * ξ) - (1 - (3 * ξ) ^ 2 / 2 + (3 * ξ) ^ 4 / 24)) := by ring
  rw [e, abs_mul, show |(-(2/9) : ℝ)| = 2/9 by norm_num]
  have : |3 * ξ| ^ 6 = 729 * |ξ| ^ 6 := by rw [abs_mul]; norm_num; ring
  rw [this] at hb
  nlinarith [abs_nonneg ξ]

/-- C08-38: the symbol (2/9)(1 − cos 3ξ) is 2π/3-periodic. -/
theorem symbol_periodic (ξ : ℝ) :
    (2/9) * (1 - Real.cos (3 * (ξ + 2 * π / 3))) = (2/9) * (1 - Real.cos (3 * ξ)) := by
  rw [show 3 * (ξ + 2 * π / 3) = 3 * ξ + 2 * π by ring, Real.cos_add_two_pi]

/-! ### Periodic-cube gaps (C08-41) -/

/-- The cosine mode is an eigenvector of the cycle Laplacian: f(x+1) + f(x−1) − 2f(x) =
−2(1 − cos(2π/L)) f(x) for f(x) = cos(2πx/L + φ). -/
theorem cycle_eigen (L x φ : ℝ) :
    Real.cos (2 * π * (x + 1) / L + φ) + Real.cos (2 * π * (x - 1) / L + φ) - 2 * Real.cos (2 * π * x / L + φ) =
      -(2 * (1 - Real.cos (2 * π / L))) * Real.cos (2 * π * x / L + φ) := by
  have e1 : 2 * π * (x + 1) / L + φ = (2 * π * x / L + φ) + 2 * π / L := by ring
  have e2 : 2 * π * (x - 1) / L + φ = (2 * π * x / L + φ) - 2 * π / L := by ring
  rw [e1, e2, Real.cos_add, Real.cos_sub]; ring

theorem sqrt2_b : (1.41421356 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.41421357 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- C08-41 values: 6(1 − cos(2π/L)) at L = 8, 16, 32, 64 is 1.757…, 0.4567…, 0.1153…, 0.02889…. -/
theorem cube_gaps :
    1.757 < 6 * (1 - Real.cos (2 * π / 8)) ∧ 6 * (1 - Real.cos (2 * π / 8)) < 1.758 ∧
    0.456 < 6 * (1 - Real.cos (2 * π / 16)) ∧ 6 * (1 - Real.cos (2 * π / 16)) < 0.457 ∧
    0.115 < 6 * (1 - Real.cos (2 * π / 32)) ∧ 6 * (1 - Real.cos (2 * π / 32)) < 0.116 ∧
    0.0288 < 6 * (1 - Real.cos (2 * π / 64)) ∧ 6 * (1 - Real.cos (2 * π / 64)) < 0.0289 := by
  rw [show 2 * π / 8 = π / 4 by ring, show 2 * π / 16 = π / 8 by ring, show 2 * π / 32 = π / 16 by ring,
    show 2 * π / 64 = π / 32 by ring, Real.cos_pi_div_four, Real.cos_pi_div_eight,
    Real.cos_pi_div_sixteen, Real.cos_pi_div_thirty_two]
  obtain ⟨a1, a2⟩ := sqrt2_b
  have b1 : (1.847759 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by rw [Real.lt_sqrt (by norm_num)]; nlinarith
  have b2 : Real.sqrt (2 + Real.sqrt 2) < 1.847760 := by rw [Real.sqrt_lt' (by norm_num)]; nlinarith
  have c1 : (1.961570 : ℝ) < Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
    rw [Real.lt_sqrt (by norm_num)]; nlinarith
  have c2 : Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) < 1.961571 := by
    rw [Real.sqrt_lt' (by norm_num)]; nlinarith
  have d1 : (1.990369 : ℝ) < Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) := by
    rw [Real.lt_sqrt (by norm_num)]; nlinarith
  have d2 : Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) < 1.990370 := by
    rw [Real.sqrt_lt' (by norm_num)]; nlinarith
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith⟩

/-! ### Cell operators and fusion-tree gaps (C08-46 … C08-49) -/

/-- C08-46, C08-47: for orthogonal R, Σ_{ab} R_ab² = 3; so P V² P = 16·3 g² = 48g² and
H_eff = −48g²/(4λ) = −12g²/λ. -/
theorem orth_frobenius (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R.transpose * R = 1) : ∑ a, ∑ b, R a b ^ 2 = 3 := by
  have := congrArg Matrix.trace hR
  rw [Matrix.trace_one, Fintype.card_fin] at this
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply] at this
  rw [Finset.sum_comm]; push_cast at this; simpa [sq] using this

theorem second_order_coefficient (g lam : ℝ) (hl : lam ≠ 0) :
    (4 * 4 : ℝ) * 3 = 48 ∧ (3 : ℝ) * (3 + 1) / 3 = 4 ∧ 48 * g ^ 2 / (4 * lam) = 12 * g ^ 2 / lam := by
  refine ⟨by norm_num, by norm_num, by field_simp; ring⟩

/-- C08-48: P(J₁·J₂)P = ½[J₁₂(J₁₂+1) − 2·3·4] on Inv(V₃^{⊗4}); spectrum {−12, −11, −9, −6, −2, 3, 9}. -/
theorem shape_spectrum :
    (List.range 7).map (fun J : ℕ => ((J * (J + 1) : ℤ) - 24) / 2) = [-12, -11, -9, -6, -2, 3, 9] ∧
    ∀ J : ℕ, (J * (J + 1) - 24 : ℚ) / 2 = ((J * (J + 1) : ℚ) - 3 * 4 - 3 * 4) / 2 := by
  refine ⟨by decide, fun J => by ring⟩

/-- C08-49: q_J = ½[S(S+1) − J(J+1)] with S = j_L + j_R vanishes at J = S, is ≥ 0 for J ≤ S, and
q_J ≥ S ≥ 6 for J ≤ S − 1 (gap ≥ 6κ). -/
theorem fusion_gap (S J : ℕ) (hS : 6 ≤ S) :
    ((S * (S + 1) : ℚ) - S * (S + 1)) / 2 = 0 ∧
      (J ≤ S → 0 ≤ ((S * (S + 1) : ℚ) - J * (J + 1)) / 2) ∧
      (J + 1 ≤ S → 6 ≤ ((S * (S + 1) : ℚ) - J * (J + 1)) / 2) := by
  refine ⟨by ring, fun h => ?_, fun h => ?_⟩
  · have : (J : ℚ) ≤ S := by exact_mod_cast h
    have : (0:ℚ) ≤ J := by positivity
    nlinarith
  · have h1 : (J : ℚ) + 1 ≤ S := by exact_mod_cast h
    have h6 : (6 : ℚ) ≤ S := by exact_mod_cast hS
    have : (0:ℚ) ≤ J := by positivity
    nlinarith

/-! ### Block length (C08-56 … C08-58) and fixed CDT edge (C08-98) -/

/-- C08-56, C08-57: L_block = √(4 ln 2 · N₀) L_* lies in [3.3, 5.3] L_* for N₀ ∈ [4, 10]. -/
theorem block_length {N0 : ℝ} (h4 : 4 ≤ N0) (h10 : N0 ≤ 10) :
    3.3 < Real.sqrt (4 * Real.log 2 * N0) ∧ Real.sqrt (4 * Real.log 2 * N0) < 5.3 := by
  have l1 := Real.log_two_gt_d9; have l2 := Real.log_two_lt_d9
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; nlinarith
  · rw [Real.sqrt_lt' (by norm_num)]; nlinarith

/-- C08-58: k L_block = (k L_*)(L_block/L_*) ≤ 5.3 k L_*. -/
theorem momentum_condition {k Ls Lb : ℝ} (hk : 0 ≤ k) (hLs : 0 < Ls) (hb : Lb ≤ 5.3 * Ls) :
    k * Lb ≤ 5.3 * (k * Ls) := by nlinarith

/-- C08-98: a² = (16 ln 2/√3)L_*² gives a = 2.530 L_* (the AppH1 cell-edge bracket). -/
theorem cdt_edge : 2.530 < Real.sqrt (16 * Real.log 2 / Real.sqrt 3) ∧
    Real.sqrt (16 * Real.log 2 / Real.sqrt 3) < 2.531 := by
  obtain ⟨-, -, h1, h2⟩ := Entropic.AppH1.cell_edge
  constructor <;> linarith

/-! ### TT projector (C08-65) and reflection positivity (C08-68) -/

/-- C08-65: for a symmetric idempotent P with Tr P = 2 (P = I − k̂k̂ᵀ), the TT kernel
P^TT_{ij,kl} = ½(P_ik P_jl + P_il P_jk − P_ij P_kl) has full trace Σ_{ij} P^TT_{ij,ij} = 2. -/
theorem tt_trace (P : Matrix (Fin 3) (Fin 3) ℝ) (hs : P.transpose = P) (hi : P * P = P) (ht : P.trace = 2) :
    ∑ i, ∑ j, (1/2) * (P i i * P j j + P i j * P j i - P i j * P i j) = 2 := by
  have hsym : ∀ i j, P j i = P i j := fun i j => by
    have := congrFun (congrFun hs i) j; simpa [Matrix.transpose_apply] using this
  have h2 : ∑ i, P i i = 2 := ht
  calc ∑ i, ∑ j, (1/2 : ℝ) * (P i i * P j j + P i j * P j i - P i j * P i j)
      = ∑ i, ∑ j, ((1/2 : ℝ) * P i i) * P j j :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [hsym i j]; ring))
    _ = ∑ i, ((1/2 : ℝ) * P i i) * ∑ j, P j j := by simp_rw [Finset.mul_sum]
    _ = 2 := by rw [← Finset.sum_mul, ← Finset.mul_sum, h2]; norm_num

/-- The TT kernel acting on a symmetric tensor X: P^TT X = P X P − ½ Tr(PX) P. -/
def ttMap (P X : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  P * X * P - ((1/2) * (P * X).trace) • P

/-- Entrywise, Σ_{kl} P^TT_{ij,kl} X_kl = (P X P − ½Tr(PX)P)_ij for symmetric P and X. -/
theorem ttMap_apply (P X : Matrix (Fin 3) (Fin 3) ℝ) (hs : P.transpose = P) (hX : X.transpose = X)
    (i j : Fin 3) :
    ∑ k, ∑ l, (1/2) * (P i k * P j l + P i l * P j k - P i j * P k l) * X k l = ttMap P X i j := by
  have hsym : ∀ a b, P b a = P a b := fun a b => by
    have := congrFun (congrFun hs a) b; simpa [Matrix.transpose_apply] using this
  have hXs : ∀ a b, X b a = X a b := fun a b => by
    have := congrFun (congrFun hX a) b; simpa [Matrix.transpose_apply] using this
  simp only [ttMap, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.trace, Matrix.diag,
    smul_eq_mul, Fin.sum_univ_three]
  simp only [hsym j, hXs 1 0, hXs 2 0, hXs 2 1, hsym 1 0, hsym 2 0, hsym 2 1]
  ring

/-- C08-65: P^TT is idempotent and Frobenius-self-adjoint on tensors when P² = P, Pᵀ = P, Tr P = 2. -/
theorem tt_projector (P X Y : Matrix (Fin 3) (Fin 3) ℝ) (hi : P * P = P) (ht : P.trace = 2) :
    ttMap P (ttMap P X) = ttMap P X ∧ (ttMap P X * Y).trace = (X * ttMap P Y).trace := by
  have hi' : ∀ M : Matrix (Fin 3) (Fin 3) ℝ, P * (P * M) = P * M := fun M => by
    rw [← Matrix.mul_assoc, hi]
  have htr : (P * (X * P)).trace = (P * X).trace := by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc, hi, Matrix.trace_mul_comm]
  constructor
  · unfold ttMap
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sub,
      Matrix.trace_smul, Matrix.mul_assoc, hi', hi, htr, ht, smul_eq_mul]
    have : (1/2 : ℝ) * ((P * X).trace - 1/2 * (P * X).trace * 2) = 0 := by ring
    rw [this, zero_smul, sub_zero]
  · unfold ttMap
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sub,
      Matrix.trace_smul, Matrix.mul_assoc, smul_eq_mul]
    rw [Matrix.trace_mul_comm P (X * (P * Y)), Matrix.trace_mul_comm X P]
    simp only [Matrix.mul_assoc]; ring

/-- C08-68 (finite form): for reflection-supported data τᵢ ≥ 0, the reflected covariance
e^{−a|τᵢ + τⱼ|} factorizes, so ⟨Θf, C f⟩ = (Σ fᵢ e^{−aτᵢ})² ≥ 0. -/
theorem reflection_positive {ι : Type*} (s : Finset ι) (f τ : ι → ℝ) (a : ℝ) (hτ : ∀ i ∈ s, 0 ≤ τ i) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, f i * f j * Real.exp (-a * |τ i - (-τ j)|) := by
  have : ∑ i ∈ s, ∑ j ∈ s, f i * f j * Real.exp (-a * |τ i - (-τ j)|) =
      (∑ i ∈ s, f i * Real.exp (-a * τ i)) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => ?_))
    rw [sub_neg_eq_add, abs_of_nonneg (add_nonneg (hτ i hi) (hτ j hj)), mul_add, Real.exp_add]; ring
  rw [this]; positivity


/-- C08-16, C08-17: u := 8η_*/49 = 0.00487621949…, α := √(1−u) = 0.99755891079…, α²¹ = 0.94996936342…. -/
theorem marked_edge_values {η : ℝ} (h : Entropic.FiniteModel.ClosureStationary η) :
    0.0048762194 < 8 * η / 49 ∧ 8 * η / 49 < 0.0048762195 ∧
    0.9975589107953 < Real.sqrt (1 - 8 * η / 49) ∧ Real.sqrt (1 - 8 * η / 49) < 0.9975589107954 ∧
    0.94996936342 < Real.sqrt (1 - 8 * η / 49) ^ 21 ∧ Real.sqrt (1 - 8 * η / 49) ^ 21 < 0.94996936343 := by
  obtain ⟨a, b⟩ := Entropic.AppCDE.eta_bracket h
  have s1 : (0.9975589107953 : ℝ) < Real.sqrt (1 - 8 * η / 49) := by
    rw [Real.lt_sqrt (by norm_num)]; nlinarith
  have s2 : Real.sqrt (1 - 8 * η / 49) < 0.9975589107954 := by
    rw [Real.sqrt_lt' (by norm_num)]; nlinarith
  refine ⟨by linarith, by linarith, s1, s2, ?_, ?_⟩
  · calc (0.94996936342 : ℝ) < 0.9975589107953 ^ 21 := by norm_num
      _ < _ := by gcongr
  · calc Real.sqrt (1 - 8 * η / 49) ^ 21 < 0.9975589107954 ^ 21 := by
          gcongr
      _ < 0.94996936343 := by norm_num

end Entropic.AppH10
