import Entropic.EFT.Edge.TetrahedralFrame
import Entropic.EFT.Edge.Kernel
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basis
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Appendix C frame identities and finite operator algebra (ledger C05-01, -02, -07, -23,
-24, -68). -/

noncomputable section
namespace Entropic.AppCDE
open Entropic.EFT.Edge

/-! ### Tetrahedral / diamond frame (C05-01, -02, -23, -24) -/

/-- Unit frame d_i = raw_i/√3 (raw = (1,1,1),(1,−1,−1),(−1,1,−1),(−1,−1,1)). The face
normals of the regular tetrahedron are −d_i; every identity below is even in d. -/
def d (i : Fin 4) (a : Fin 3) : ℝ := (rawNormal i a : ℝ) / Real.sqrt 3

theorem sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem d_mul (i j : Fin 4) (a b : Fin 3) :
    d i a * d j b = (rawNormal i a * rawNormal j b : ℤ) / 3 := by
  unfold d; push_cast; rw [div_mul_div_comm, ← pow_two, sqrt3_sq]

/-- |d_i| = 1 and d_i·d_j = −1/3 for i ≠ j. -/
theorem d_dot (i j : Fin 4) : ∑ a, d i a * d j a = if i = j then 1 else -1/3 := by
  simp_rw [d_mul, ← Finset.sum_div]
  have h := rawNormal_dot i j
  rw [← Int.cast_sum, h]; split_ifs <;> norm_num

/-- Frame identity Σ_i d_i d_iᵀ = (4/3) I₃ (C05-01, C05-23). -/
theorem frame_identity (a b : Fin 3) : ∑ i, d i a * d i b = if a = b then 4/3 else 0 := by
  simp_rw [d_mul, ← Finset.sum_div]
  rw [← Int.cast_sum, rawNormal_outer a b]; split_ifs <;> norm_num

theorem frame_sum_zero (a : Fin 3) : ∑ i, d i a = 0 := by
  unfold d; rw [← Finset.sum_div, ← Int.cast_sum, rawNormal_sum_zero a]; simp

/-- Quadratic form: Σ_i (d_i·u)² = (4/3)|u|². -/
theorem frame_quadratic (u : Fin 3 → ℝ) :
    ∑ i, (∑ a, d i a * u a) ^ 2 = 4/3 * ∑ a, u a ^ 2 := by
  have : ∀ i, (∑ a, d i a * u a) ^ 2 = ∑ a, ∑ b, (d i a * d i b) * (u a * u b) := by
    intro i; rw [sq, Finset.sum_mul_sum]; congr 1; ext a; congr 1; ext b; ring
  simp_rw [this]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 4))), ← Finset.sum_mul, frame_identity]
  simp [Fin.sum_univ_three, ite_mul, Finset.mul_sum]; ring

/-- Transverse fraction (C05-02): for a unit vector u, (1/4)Σ(d_i·u)² = 1/3, so
f_⊥ = 1 − 1/3 = 2/3 and f_⊥⁻¹ = 3/2. -/
theorem transverse_fraction (u : Fin 3 → ℝ) (hu : ∑ a, u a ^ 2 = 1) :
    (1/4) * ∑ i, (∑ a, d i a * u a) ^ 2 = 1/3 ∧
      1 - (1/4) * ∑ i, (∑ a, d i a * u a) ^ 2 = 2/3 ∧
      (1 - (1/4) * ∑ i, (∑ a, d i a * u a) ^ 2)⁻¹ = 3/2 := by
  rw [frame_quadratic, hu]; norm_num

/-- Local Green tensor (C05-24): G_loc = G₀·(1/4)Σ d dᵀ = (G₀/3) δ, and its transverse trace
with P_⊥ = δ − r rᵀ (|r| = 1) is (2/3) G₀, for any value of G₀. -/
theorem green_transverse (G0 : ℝ) (r : Fin 3 → ℝ) (hr : ∑ a, r a ^ 2 = 1) :
    (∀ a b, G0 * ((1/4) * ∑ i, d i a * d i b) = if a = b then G0 / 3 else 0) ∧
      ∑ a, ∑ b, ((if a = b then 1 else 0) - r a * r b) * (G0 * ((1/4) * ∑ i, d i a * d i b))
        = 2/3 * G0 := by
  have hG : ∀ a b, G0 * ((1/4) * ∑ i, d i a * d i b) = if a = b then G0 / 3 else 0 := by
    intro a b; rw [frame_identity]; split_ifs <;> ring
  refine ⟨hG, ?_⟩
  simp_rw [hG]
  simp only [Fin.sum_univ_three, Fin.isValue] at hr ⊢
  simp; linear_combination (-G0/3) * hr

/-! ### Return operator (C05-07) -/

/-- Singlet projector |u⟩⟨u| on ℝ⁷, u = (1,…,1)/√7: all entries 1/7. -/
def Psing : Matrix (Fin 7) (Fin 7) ℝ := Matrix.of fun _ _ => 1/7

theorem Psing_idem : Psing * Psing = Psing := by
  ext i j; simp [Psing, Matrix.mul_apply]

theorem Psing_symm : Psing.transpose = Psing := by ext i j; simp [Psing]

theorem Psing_trace : Psing.trace = 1 := by simp [Psing, Matrix.trace]

/-- Psing = |u⟩⟨u| with u = (1/√7)·𝟙. -/
theorem Psing_outer (i j : Fin 7) :
    Psing i j = (1 / Real.sqrt 7) * (1 / Real.sqrt 7) := by
  simp only [Psing, Matrix.of_apply]
  have h7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  field_simp; rw [h7]

def Rret : Matrix (Fin 7) (Fin 7) ℝ := 1 + ((2/3) * (1/3) : ℝ) • Psing

/-- Σ_ret = Tr R_ret = 7 + 2/9 = 65/9. -/
theorem Sigma_ret : Rret.trace = 65/9 := by
  rw [Rret, Matrix.trace_add, Matrix.trace_smul, Psing_trace, Matrix.trace_one]
  simp; norm_num

theorem Sigma_ret_matches : Rret.trace = SigmaReturn := by
  rw [Sigma_ret, SigmaReturn_closed]

/-! ### Face-label algebra (C05-68) -/

def E (m : Fin 7) : Matrix (Fin 7) (Fin 7) ℝ := Matrix.single m m 1

theorem E_apply (m i j : Fin 7) : E m i j = if i = m ∧ j = m then 1 else 0 := by
  simp [E, Matrix.single_apply, eq_comm]

theorem E_mul (m n : Fin 7) : E m * E n = if m = n then E m else 0 := by
  ext i j
  simp only [Matrix.mul_apply, E_apply]
  by_cases h : m = n
  · subst h; rw [if_pos rfl, E_apply]
    rw [Finset.sum_eq_single m (fun k _ hk => by simp [hk]) (by simp)]
    by_cases hi : i = m <;> by_cases hj : j = m <;> simp [hi, hj]
  · rw [if_neg h, Matrix.zero_apply]
    apply Finset.sum_eq_zero; intro k _
    by_cases hk : k = m
    · subst hk; simp [h]
    · simp [hk]

theorem E_comm (m n : Fin 7) : E m * E n = E n * E m := by
  by_cases h : m = n
  · rw [h]
  · rw [E_mul, E_mul, if_neg h, if_neg (Ne.symm h)]

theorem E_span (c : Fin 7 → ℝ) : ∑ m, c m • E m = Matrix.diagonal c := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, E_apply, smul_eq_mul, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; rw [if_pos rfl, Finset.sum_eq_single i (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
    simp
  · rw [if_neg h]; apply Finset.sum_eq_zero; intro k _
    by_cases hk : i = k
    · subst hk; simp [Ne.symm h]
    · simp [hk]

theorem E_sum : ∑ m, E m = 1 := by
  have := E_span (fun _ => 1)
  simp only [one_smul] at this
  rw [this, Matrix.diagonal_one]

theorem E_independent (c : Fin 7 → ℝ) (h : ∑ m, c m • E m = 0) : c = 0 := by
  rw [E_span] at h; ext i; simpa using congrFun (congrFun h i) i

end Entropic.AppCDE
