import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-! Appendix B: elementary algebra, spin/mismatch arithmetic and the homogeneous
minimum (ledger C04). Each theorem names its ledger ID. -/

noncomputable section
namespace Entropic.AppB
open Real Filter Topology

/-! ### A.1, B.1 conventions -/

/-- C04-01: with x⁰ = ct, (c³/16πG)·c = c⁴/16πG. -/
theorem adm_coefficient (c G : ℝ) : c ^ 3 / (16 * π * G) * c = c ^ 4 / (16 * π * G) := by ring

/-- C04-02: two sites per cell V* = L*³ and four-volume V*·(L*/c) = L*⁴/c. -/
theorem cell_density (L c : ℝ) : L ^ 3 * (L / c) = L ^ 4 / c := by ring

/-- C04-04: G* = c³L*²/ħ with L* = −(3/2) Z_e λ_e ln(1 − e^{−7g}) equals
(9/4)(ħc/m_e²) Z_e² ln²(1 − e^{−7g}); and L* > 0 for g > 0, Z_e, λ_e > 0. -/
theorem Gstar_closed_form (c ħ me Ze g : ℝ) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hm : me ≠ 0) :
    let L := -(3/2) * Ze * (ħ / (me * c)) * Real.log (1 - Real.exp (-7 * g))
    c ^ 3 * L ^ 2 / ħ = 9/4 * (ħ * c / me ^ 2) * Ze ^ 2 * Real.log (1 - Real.exp (-7 * g)) ^ 2 := by
  intro L; simp only [L]; field_simp; ring

theorem Lstar_pos {Ze lam g : ℝ} (hZ : 0 < Ze) (hl : 0 < lam) (hg : 0 < g) :
    0 < -(3/2) * Ze * lam * Real.log (1 - Real.exp (-7 * g)) := by
  have h1 : Real.exp (-7 * g) < 1 := by
    have := Real.exp_lt_exp.mpr (show -7 * g < 0 by linarith); rwa [Real.exp_zero] at this
  have h0 : 0 < 1 - Real.exp (-7 * g) := by linarith
  have hlog : Real.log (1 - Real.exp (-7 * g)) < 0 :=
    Real.log_neg h0 (by linarith [Real.exp_pos (-7 * g)])
  have : 0 < (3/2) * Ze * lam * (-Real.log (1 - Real.exp (-7 * g))) :=
    mul_pos (by positivity) (by linarith)
  linarith

/-- C04-05: q = S/S∞ = 1 − δS/S∞ lies in [0,1] when 0 ≤ S ≤ S∞. -/
theorem occupancy {S Sinf : ℝ} (hS : 0 < Sinf) (h0 : 0 ≤ S) (h1 : S ≤ Sinf) :
    S / Sinf = 1 - (Sinf - S) / Sinf ∧ 0 ≤ S / Sinf ∧ S / Sinf ≤ 1 := by
  refine ⟨by field_simp; ring, div_nonneg h0 hS.le, (div_le_one hS).mpr h1⟩

/-- C04-07: χ = −T^μ_μ/c² for a perfect fluid (−,+,+,+): T^μ_μ = −ρc² + 3p, so χ = ρ − 3p/c². -/
theorem trace_source (ρ p c : ℝ) (hc : c ≠ 0) : -(-ρ * c ^ 2 + 3 * p) / c ^ 2 = ρ - 3 * p / c ^ 2 := by
  field_simp; ring

/-- C04-12: regular tetrahedral normals (n_i·n_i = 1, n_i·n_j = −1/3) give
|Σ m_i n_i|² = (4Σ² − S²)/3, as a Gram-matrix identity. -/
theorem closure_norm (m₁ m₂ m₃ m₄ : ℝ) :
    (m₁^2 + m₂^2 + m₃^2 + m₄^2) + 2 * (-1/3) * (m₁*m₂ + m₁*m₃ + m₁*m₄ + m₂*m₃ + m₂*m₄ + m₃*m₄)
      = (4 * (m₁^2 + m₂^2 + m₃^2 + m₄^2) - (m₁ + m₂ + m₃ + m₄)^2) / 3 := by ring

/-- C04-13 (abstracted): with ⟨A_i·A_i⟩ = j(j+1), ⟨A_i⟩ = m_i n_i and product-state
factorization ⟨A_i·A_k⟩ = m_i m_k n_i·n_k (i ≠ k), ⟨C·C⟩ = 4j(j+1) − (S² − Σ²)/3. -/
theorem closure_expectation (j m₁ m₂ m₃ m₄ : ℝ) :
    4 * (j * (j + 1)) + 2 * (-1/3) * (m₁*m₂ + m₁*m₃ + m₁*m₄ + m₂*m₃ + m₂*m₄ + m₃*m₄)
      = 4 * j * (j + 1) - ((m₁ + m₂ + m₃ + m₄)^2 - (m₁^2 + m₂^2 + m₃^2 + m₄^2)) / 3 := by ring

theorem closure_expectation_j3 (m₁ m₂ m₃ m₄ : ℝ) :
    4 * (3:ℝ) * (3 + 1) = 48 := by norm_num

/-! ### B.3–B.4 spin and mismatch arithmetic (Casimir level) -/

/-- C04-43/C04-56: on V_J ⊂ V_j ⊗ V_j, (J_L − J̃_R)² = 4j(j+1) − J(J+1) and
Q_f = ½[(J_L − J̃_R)² − 2j] = ½[2j(2j+1) − J(J+1)]. -/
def Qf (j J : ℝ) : ℝ := (1/2) * ((4 * j * (j + 1) - J * (J + 1)) - 2 * j)

theorem Qf_eq (j J : ℝ) : Qf j J = (1/2) * (2 * j * (2 * j + 1) - J * (J + 1)) := by
  unfold Qf; ring

theorem Qf_heisenberg (j J : ℝ) : Qf j J = j ^ 2 + j * (j + 1) - J * (J + 1) / 2 := by
  unfold Qf; ring

/-- Q_f ≥ 0 on every J ≤ 2j, with kernel exactly J = 2j (J ≥ 0). -/
theorem Qf_nonneg {j J : ℝ} (hJ0 : 0 ≤ J) (hJ : J ≤ 2 * j) : 0 ≤ Qf j J := by
  rw [Qf_eq]; nlinarith

theorem Qf_zero_iff {j J : ℝ} (hJ0 : 0 ≤ J) (hj : 0 ≤ j) : Qf j J = 0 ↔ J = 2 * j := by
  rw [Qf_eq]; constructor
  · intro h; nlinarith [sq_nonneg (J - 2 * j)]
  · rintro rfl; ring

/-- C04-45: j₀ = 3/2 gives 6, 5, 3, 0 on J = 0, 1, 2, 3. -/
theorem Qf_three_halves : Qf (3/2) 0 = 6 ∧ Qf (3/2) 1 = 5 ∧ Qf (3/2) 2 = 3 ∧ Qf (3/2) 3 = 0 := by
  unfold Qf; norm_num

/-- C04-57: spin-3 bond, 9 − J_a·J_b = 21 − J(J+1)/2 gives 21,20,18,15,11,6,0. -/
def bond (J : ℝ) : ℝ := 9 - (J * (J + 1) - 24) / 2

theorem bond_table : bond 0 = 21 ∧ bond 1 = 20 ∧ bond 2 = 18 ∧ bond 3 = 15 ∧
    bond 4 = 11 ∧ bond 5 = 6 ∧ bond 6 = 0 := by unfold bond; norm_num

/-- C04-52: Σ_{a<b}(9 − J_a·J_b) = ½[(3N)(3N+1) − J_tot²] when J_tot² = 12N + 2Σ_{a<b}J_a·J_b. -/
theorem all_pairs (N P Jtot2 : ℝ) (hJ : Jtot2 = 12 * N + 2 * P) :
    9 * (N * (N - 1) / 2) - P = (1/2) * ((3 * N) * (3 * N + 1) - Jtot2) := by
  subst hJ; ring

/-! ### B.3 homogeneous minimum (C04-38, C04-46, C04-47, C04-48) -/

/-- C04-48: at fixed total ρ, mixing any J < 3 block costs κ(6ρ₀ + 5ρ₁ + 3ρ₂). -/
def Vmin (r u κ ρ₀ ρ₁ ρ₂ ρ₃ : ℝ) : ℝ :=
  let ρ := ρ₀ + ρ₁ + ρ₂ + ρ₃
  r * ρ + u / 2 * ρ ^ 2 + 6 * κ * ρ₀ + 5 * κ * ρ₁ + 3 * κ * ρ₂

theorem mixed_exclusion (r u κ ρ₀ ρ₁ ρ₂ ρ₃ : ℝ) :
    Vmin r u κ ρ₀ ρ₁ ρ₂ ρ₃ - Vmin r u κ 0 0 0 (ρ₀ + ρ₁ + ρ₂ + ρ₃) = κ * (6 * ρ₀ + 5 * ρ₁ + 3 * ρ₂) := by
  unfold Vmin; ring

theorem mixed_exclusion_pos {r u κ ρ₀ ρ₁ ρ₂ ρ₃ : ℝ} (hκ : 0 < κ) (h0 : 0 ≤ ρ₀) (h1 : 0 ≤ ρ₁)
    (h2 : 0 ≤ ρ₂) (hpos : 0 < ρ₀ ∨ 0 < ρ₁ ∨ 0 < ρ₂) :
    Vmin r u κ 0 0 0 (ρ₀ + ρ₁ + ρ₂ + ρ₃) < Vmin r u κ ρ₀ ρ₁ ρ₂ ρ₃ := by
  have := mixed_exclusion r u κ ρ₀ ρ₁ ρ₂ ρ₃
  rcases hpos with h | h | h <;> nlinarith

/-- C04-46: with r < 0 < u, κ > 0, the unique global minimizer on ρ_J ≥ 0 is ρ₃ = −r/u, others 0. -/
theorem homogeneous_minimum {r u κ : ℝ} (hr : r < 0) (hu : 0 < u) (hκ : 0 < κ)
    {ρ₀ ρ₁ ρ₂ ρ₃ : ℝ} (h0 : 0 ≤ ρ₀) (h1 : 0 ≤ ρ₁) (h2 : 0 ≤ ρ₂) (h3 : 0 ≤ ρ₃) :
    Vmin r u κ 0 0 0 (-r / u) ≤ Vmin r u κ ρ₀ ρ₁ ρ₂ ρ₃ ∧
      (Vmin r u κ ρ₀ ρ₁ ρ₂ ρ₃ = Vmin r u κ 0 0 0 (-r / u) →
        ρ₀ = 0 ∧ ρ₁ = 0 ∧ ρ₂ = 0 ∧ ρ₃ = -r / u) := by
  have hm := mixed_exclusion r u κ ρ₀ ρ₁ ρ₂ ρ₃
  set ρ := ρ₀ + ρ₁ + ρ₂ + ρ₃
  have hq : Vmin r u κ 0 0 0 ρ - Vmin r u κ 0 0 0 (-r / u) = u / 2 * (ρ + r / u) ^ 2 := by
    unfold Vmin; field_simp; ring
  have hsq : 0 ≤ u / 2 * (ρ + r / u) ^ 2 := by positivity
  have hmix : 0 ≤ κ * (6 * ρ₀ + 5 * ρ₁ + 3 * ρ₂) := by positivity
  refine ⟨by linarith, fun heq => ?_⟩
  have h6 : κ * (6 * ρ₀ + 5 * ρ₁ + 3 * ρ₂) = 0 := by linarith
  have h7 : u / 2 * (ρ + r / u) ^ 2 = 0 := by linarith
  have hsum : 6 * ρ₀ + 5 * ρ₁ + 3 * ρ₂ = 0 := (mul_eq_zero.mp h6).resolve_left hκ.ne'
  have e0 : ρ₀ = 0 := by linarith
  have e1 : ρ₁ = 0 := by linarith
  have e2 : ρ₂ = 0 := by linarith
  have hρ : ρ + r / u = 0 := by
    have hu2 : u / 2 ≠ 0 := by positivity
    have := (mul_eq_zero.mp h7).resolve_left hu2
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  refine ⟨e0, e1, e2, ?_⟩
  have h' : ρ₀ + ρ₁ + ρ₂ + ρ₃ + r / u = 0 := hρ
  rw [e0, e1, e2] at h'; rw [neg_div]; linarith

/-- C04-38/C04-47: at the pure-J* point, ∂V/∂ρ_J = r_J − (w/u) r_{J*}; with
r_J = r + c_J κ and u_J = w = u this is c_J κ: 6κ, 5κ, 3κ. -/
theorem block_mass (r κ u cJ : ℝ) (hu : u ≠ 0) :
    (r + cJ * κ) - (u / u) * r = cJ * κ := by field_simp; ring

/-! ### B.4 finite-dimensional operator identities (C04-64, C04-70, C04-71) -/

section Ops
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
open Matrix

/-- C04-64: if F†F = P (projector, P² = P), FF† = 1 and T = Σ_{J<3} e^{-c_J s} P_J + P with
P_J P = 0, then F T F† = 1 (finite s changes nothing on the isolated face). Stated for
T = R + P with R P = 0. -/
theorem isolated_face (F : Matrix m n ℂ) (P R : Matrix n n ℂ) (hFP : Fᴴ * F = P)
    (hFF : F * Fᴴ = 1) (hRP : R * P = 0) (hRh : Rᴴ = R) (hPh : Pᴴ = P) :
    F * (R + P) * Fᴴ = 1 := by
  -- F R F† = F (F†F R ... ) : use F = F F† F = F P
  have hF : F = F * P := by rw [← hFP, ← Matrix.mul_assoc, hFF, Matrix.one_mul]
  have hFR : F * R = 0 := by
    have : F * R = F * P * R := by rw [← hF]
    have hPR : P * R = 0 := by
      have := congrArg conjTranspose hRP
      simpa [conjTranspose_mul, hRh, hPh] using this
    rw [this, Matrix.mul_assoc, hPR, Matrix.mul_zero]
  rw [Matrix.mul_add, Matrix.add_mul, hFR, Matrix.zero_mul, zero_add, ← hF, hFF]

/-- C04-71: an isometry U ψ = F P ψ ⊗ |0⟩ + |∅⟩ ⊗ C ψ with orthogonal flags has
U†U = (FP)†(FP) + C†C; isometry forces C†C = 1 − P when F†F = P and P² = P. -/
theorem retained_output (F : Matrix m n ℂ) (C : Matrix m n ℂ) (P : Matrix n n ℂ)
    (hFP : Fᴴ * F = P) (hP : P * P = P) (hPh : Pᴴ = P)
    (hiso : (F * P)ᴴ * (F * P) + Cᴴ * C = 1) : Cᴴ * C = 1 - P := by
  have : (F * P)ᴴ * (F * P) = P := by
    rw [conjTranspose_mul, hPh, Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ, hFP, hP, hP]
  rw [this] at hiso
  rw [← hiso]; abel

/-- C04-70: conversely with C†C = 1 − P the sharp pair map is an isometry. -/
theorem sharp_pair_isometry (F C : Matrix m n ℂ) (P : Matrix n n ℂ)
    (hFP : Fᴴ * F = P) (hP : P * P = P) (hPh : Pᴴ = P) (hC : Cᴴ * C = 1 - P) :
    (F * P)ᴴ * (F * P) + Cᴴ * C = 1 := by
  rw [conjTranspose_mul, hPh, Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ, hFP, hP, hP, hC]; abel

end Ops

/-! ### C.5-type area factor and refinement scalings (C04-60, C04-61) -/

/-- C04-60: Z_A(N) = √(3N/(3N+1)); Z_A(1) = √3/2 and Z_A(N) → 1. -/
def ZA (N : ℝ) : ℝ := Real.sqrt (3 * N / (3 * N + 1))

theorem ZA_one : ZA 1 = Real.sqrt 3 / 2 := by
  unfold ZA
  rw [show (3:ℝ) * 1 / (3 * 1 + 1) = 3 / 4 by norm_num, Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4),
    show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem ZA_tendsto_one : Tendsto (fun N : ℕ => ZA N) atTop (𝓝 1) := by
  have h : Tendsto (fun N : ℕ => (3 * (N:ℝ)) / (3 * N + 1)) atTop (𝓝 1) := by
    have : Tendsto (fun N : ℕ => 1 - 1 / (3 * (N:ℝ) + 1)) atTop (𝓝 (1 - 0)) := by
      apply Tendsto.sub tendsto_const_nhds
      apply Tendsto.div_atTop tendsto_const_nhds
      apply tendsto_atTop_add_const_right
      exact Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
    refine (tendsto_congr' ?_).mp (by simpa using this)
    filter_upwards with N
    have : (3 * (N:ℝ) + 1) ≠ 0 := by positivity
    field_simp; ring
  have := h.sqrt
  simpa [ZA] using this

/-- C04-61: exponent arithmetic of the refinement witness: −2 + 1/4 = −7/4,
μ·μ^{−7/8} = μ^{1/8}, (μ^{1/8})² = μ^{1/4}. -/
theorem refinement_exponents {μ : ℝ} (hμ : 0 < μ) :
    μ * μ ^ (-(7:ℝ)/8) = μ ^ ((1:ℝ)/8) ∧ (μ ^ ((1:ℝ)/8)) ^ 2 = μ ^ ((1:ℝ)/4) ∧
      ((-2:ℝ) + 1/4 = -7/4) := by
  refine ⟨?_, ?_, by norm_num⟩
  · rw [← Real.rpow_one_add' hμ.le (by norm_num)]; norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hμ.le]; norm_num

/-! ### B.5 maximum entropy (C04-77) -/

/-- C04-77: H(p) ≤ ln|M| for any probability vector on a finite set. -/
theorem max_entropy {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (h1 : ∑ i, p i = 1) : ∑ i, Real.negMulLog (p i) ≤ Real.log (Fintype.card ι) := by
  -- Gibbs: Σ p log(1/(n p)) ≤ log Σ p·1/(n p) ≤ 0 via concavity: use −x log x ≤ x(log(1/n)·(-1))... use
  -- negMulLog x ≤ x * log n + (1/n - x)  ... from log y ≤ y - 1 with y = 1/(n x)
  set n : ℝ := (Fintype.card ι : ℝ)
  have hn : 0 < n := by simp [n, Fintype.card_pos]
  have key : ∀ i, Real.negMulLog (p i) ≤ p i * Real.log n + (1 / n - p i) := by
    intro i
    rcases (hp i).eq_or_lt with h | h
    · rw [← h]; simp; positivity
    · unfold Real.negMulLog
      have := Real.log_le_sub_one_of_pos (show 0 < 1 / (n * p i) by positivity)
      rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_mul hn.ne' h.ne'] at this
      have hmul := mul_le_mul_of_nonneg_left this h.le
      have : p i * (1 / (n * p i) - 1) = 1 / n - p i := by field_simp
      nlinarith
  calc ∑ i, Real.negMulLog (p i) ≤ ∑ i, (p i * Real.log n + (1 / n - p i)) :=
        Finset.sum_le_sum (fun i _ => key i)
    _ = Real.log n := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, h1, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul]
        field_simp; ring

end Entropic.AppB
