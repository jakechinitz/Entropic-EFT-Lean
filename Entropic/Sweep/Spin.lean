import Entropic.AppP.Spin
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Chunk 14 sweep, spin-3/2 pair (C07-49, C09-06, C07-79, C04-44, C04-73, C09-14, C04-39).

All matrices are in the ladder basis of `Entropic.AppP.Spin`. The ladder basis vectors have squared
norms proportional to w = (36, 12, 3, 1) on one slot, so the tensor-product inner product is
⟨x, y⟩_W = Σ_i W_i x_i y_i with W = w ⊗ w. Self-adjointness and positivity are stated for ⟨·,·⟩_W.
Integer identities are checked entrywise by kernel evaluation. -/

noncomputable section
namespace Entropic.Sweep.SpinPair
open Matrix Entropic.AppP.Spin

def L0F : Fin 16 → Fin 16 → ℤ :=
  ![![5760, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2880, 0, 0, 2880, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1152, 0, 0, 2304, 0, 0, 1152, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 288, 0, 0, 864, 0, 0, 864, 0, 0, 288, 0, 0, 0],
    ![0, 2880, 0, 0, 2880, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1728, 0, 0, 3456, 0, 0, 1728, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 864, 0, 0, 2592, 0, 0, 2592, 0, 0, 864, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1152, 0, 0, 1728, 0, 0, 1152, 0, 0],
    ![0, 0, 1152, 0, 0, 2304, 0, 0, 1152, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 864, 0, 0, 2592, 0, 0, 2592, 0, 0, 864, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 2304, 0, 0, 3456, 0, 0, 2304, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2880, 0, 0, 2880, 0],
    ![0, 0, 0, 288, 0, 0, 864, 0, 0, 864, 0, 0, 288, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1152, 0, 0, 1728, 0, 0, 1152, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2880, 0, 0, 2880, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5760]]
def L12F : Fin 16 → Fin 16 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 576, 0, 0, -576, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 576, 0, 0, 0, 0, 0, -576, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 288, 0, 0, 288, 0, 0, -288, 0, 0, -288, 0, 0, 0],
    ![0, -576, 0, 0, 576, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 288, 0, 0, 288, 0, 0, -288, 0, 0, -288, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 576, 0, 0, 0, 0, 0, -576, 0, 0],
    ![0, 0, -576, 0, 0, 0, 0, 0, 576, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -288, 0, 0, -288, 0, 0, 288, 0, 0, 288, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 576, 0, 0, -576, 0],
    ![0, 0, 0, -288, 0, 0, -288, 0, 0, 288, 0, 0, 288, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -576, 0, 0, 0, 0, 0, 576, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -576, 0, 0, 576, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def L20F : Fin 16 → Fin 16 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 192, 0, 0, -256, 0, 0, 192, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 288, 0, 0, -96, 0, 0, -96, 0, 0, 288, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -192, 0, 0, 256, 0, 0, -192, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -96, 0, 0, 32, 0, 0, 32, 0, 0, -96, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 192, 0, 0, -192, 0, 0, 192, 0, 0],
    ![0, 0, 192, 0, 0, -256, 0, 0, 192, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -96, 0, 0, 32, 0, 0, 32, 0, 0, -96, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -256, 0, 0, 256, 0, 0, -256, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 288, 0, 0, -96, 0, 0, -96, 0, 0, 288, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 192, 0, 0, -192, 0, 0, 192, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def L24F : Fin 16 → Fin 16 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 288, 0, 0, -288, 0, 0, 288, 0, 0, -288, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -288, 0, 0, 288, 0, 0, -288, 0, 0, 288, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 288, 0, 0, -288, 0, 0, 288, 0, 0, -288, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -288, 0, 0, 288, 0, 0, -288, 0, 0, 288, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def GF : Fin 16 → Fin 16 → ℤ :=
  ![![69120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 46656, 0, 0, 22464, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 25920, 0, 0, 27648, 0, 0, 1728, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 9504, 0, 0, 16416, 0, 0, 4320, 0, 0, -2592, 0, 0, 0],
    ![0, 22464, 0, 0, 46656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 20736, 0, 0, 41472, 0, 0, 20736, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 16416, 0, 0, 37152, 0, 0, 25056, 0, 0, 4320, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 25920, 0, 0, 20736, 0, 0, 1728, 0, 0],
    ![0, 0, 1728, 0, 0, 27648, 0, 0, 25920, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 4320, 0, 0, 25056, 0, 0, 37152, 0, 0, 16416, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 27648, 0, 0, 41472, 0, 0, 27648, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 46656, 0, 0, 22464, 0],
    ![0, 0, 0, -2592, 0, 0, 4320, 0, 0, 16416, 0, 0, 9504, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1728, 0, 0, 20736, 0, 0, 25920, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22464, 0, 0, 46656, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69120]]

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem L0_chk : ∀ i j : Fin 16, L0F i j = -(M3F i j - 56 * M2F i j + 1008 * MzF i j - 5760 * (if i = j then 1 else 0)) := by
  decide +kernel
theorem L12_chk : ∀ i j : Fin 16, L12F i j = M3F i j - 44 * M2F i j + 480 * MzF i j := by decide +kernel
theorem L20_chk : ∀ i j : Fin 16, L20F i j = -(M3F i j - 36 * M2F i j + 288 * MzF i j) := by decide +kernel
theorem L24_chk : ∀ i j : Fin 16, L24F i j = M3F i j - 32 * M2F i j + 240 * MzF i j := by decide +kernel

theorem L0_lit : L0 = Matrix.of L0F := by
  have e0 : L0 = -(M3 - (56:ℤ) • M2 + (1008:ℤ) • Mz - (5760:ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ)) := by
    simp only [L0, num16 12, num16 20, num16 24]; rw [← M3_eq, ← M2_eq]; noncomm_ring
  rw [e0]; ext i j
  simp only [M3, M2, Mz, Matrix.neg_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.of_apply, Matrix.one_apply, smul_eq_mul]
  rw [L0_chk i j]

theorem L12_lit : L12 = Matrix.of L12F := by
  have e : L12 = M3 - (44:ℤ) • M2 + (480:ℤ) • Mz := by
    simp only [L12, num16 20, num16 24]; rw [← M3_eq, ← M2_eq]; noncomm_ring
  rw [e]; ext i j
  simp only [M3, M2, Mz, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  rw [L12_chk i j]

theorem L20_lit : L20 = Matrix.of L20F := by
  have e : L20 = -(M3 - (36:ℤ) • M2 + (288:ℤ) • Mz) := by
    simp only [L20, num16 12, num16 24]; rw [← M3_eq, ← M2_eq]; noncomm_ring
  rw [e]; ext i j
  simp only [M3, M2, Mz, Matrix.neg_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul]
  rw [L20_chk i j]

theorem L24_lit : L24 = Matrix.of L24F := by
  have e : L24 = M3 - (32:ℤ) • M2 + (240:ℤ) • Mz := by
    simp only [L24, num16 12, num16 20]; rw [← M3_eq, ← M2_eq]; noncomm_ring
  rw [e]; ext i j
  simp only [M3, M2, Mz, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  rw [L24_chk i j]

/-! ### C07-49, C09-06: the orthogonal splitting C¹⁶ = V₃ ⊕ Q -/

theorem Y_add_L0 : Y + L0 = (5760:ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) := by
  rw [Y_of, L0_lit]; ext i j
  simp only [YF, Matrix.add_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have := L0_chk i j
  have hN : ∀ i j : Fin 16, NmF i j = M3F i j - 56 * M2F i j + 1008 * MzF i j - 5760 * (if i = j then 1 else 0) := by
    decide +kernel
  rw [this, hN i j]; split_ifs <;> ring

/-- C07-49, C09-06: with P_Q = Y/5760 and P₃ = L₀/5760 (L₀ = −(M−12)(M−20)(M−24), M = 4Q_f):
P_Q + P₃ = I, P_Q P₃ = P₃ P_Q = 0, P₃² = P₃, P_Q² = P_Q, Tr P₃ = 7, Tr P_Q = 9 (16 = 7 + 9).
`AppP.Spin.multiplicities` and `AppP.Spin.total_spin` identify the summands: P₃ is the J = 3
eigenspace of the total Casimir (multiplicity 7) and P_Q = P₂ + P₁ + P₀ (5 + 3 + 1). -/
theorem projector_split :
    Y + L0 = (5760:ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) ∧ Y * L0 = 0 ∧ L0 * Y = 0 ∧
      L0 * L0 = (5760:ℤ) • L0 ∧ Y * Y = (5760:ℤ) • Y ∧ L0.trace = 7 * 5760 ∧ Y.trace = 9 * 5760 := by
  have hL : L0 = (5760:ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) - Y := by rw [← Y_add_L0]; abel
  have hY := Y_idem
  refine ⟨Y_add_L0, ?_, ?_, ?_, hY, multiplicities.1, Y_trace⟩
  · rw [hL, Matrix.mul_sub, hY, Matrix.mul_smul, Matrix.mul_one, sub_self]
  · rw [hL, Matrix.sub_mul, hY, Matrix.smul_mul, Matrix.one_mul, sub_self]
  · rw [hL, show ((5760:ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) - Y) * ((5760:ℤ) • 1 - Y) =
        (5760 * 5760 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) - (2 * 5760 : ℤ) • Y + Y * Y by
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
          Matrix.mul_one, smul_smul]; module, hY]
    rw [smul_sub, smul_smul]; module

/-! ### Weighted inner product: self-adjointness and positivity of Q_f -/

def w1 : Fin 4 → ℤ := ![36, 12, 3, 1]
def wv (i : Fin 16) : ℤ := w1 (hi i) * w1 (lo i)
def Wm : Matrix (Fin 16) (Fin 16) ℤ := Matrix.diagonal wv

theorem wv_pos : ∀ i, 0 < wv i := by decide +kernel

theorem single_adjoint : ∀ i j : Fin 4, w1 i * JmF i j = w1 j * JpF j i := by decide +kernel

theorem selfadj_chk : ∀ i j : Fin 16, wv i * MzF i j = wv j * MzF j i := by decide +kernel

/-- J₋ is the ⟨·,·⟩_w-adjoint of J₊ (one slot), and M = 4Q_f is ⟨·,·⟩_W-self-adjoint: (W M)ᵀ = W M. -/
theorem selfadjoint : (Wm * Mz)ᵀ = Wm * Mz := by
  ext i j
  simp only [Wm, Matrix.transpose_apply, Matrix.diagonal_mul, Mz, Matrix.of_apply]
  exact (selfadj_chk i j).symm

theorem psd_chk : ∀ i j : Fin 16, 552960 * (wv i * MzF i j) =
    5 * (List.ofFn fun k => L12F k i * wv k * L12F k j).sum +
    27 * (List.ofFn fun k => L20F k i * wv k * L20F k j).sum +
    10 * (List.ofFn fun k => L24F k i * wv k * L24F k j).sum := by decide +kernel

/-- Spectral sum-of-squares form: 552960·W M = 5 L₁₂ᵀ W L₁₂ + 27 L₂₀ᵀ W L₂₀ + 10 L₂₄ᵀ W L₂₄
(the coefficients are 552960·λ/d_λ² for λ = 12, 20, 24). -/
theorem WM_apply (A : Matrix (Fin 16) (Fin 16) ℤ) (i j : Fin 16) : (Wm * A) i j = wv i * A i j :=
  Matrix.diagonal_mul wv A i j

theorem LWL_apply (L : Matrix (Fin 16) (Fin 16) ℤ) (i j : Fin 16) :
    (Lᵀ * Wm * L) i j = ∑ k, L k i * wv k * L k j := by
  rw [Matrix.mul_apply]; congr 1; ext k; rw [Wm, Matrix.mul_diagonal, Matrix.transpose_apply]

theorem psd_identity : (552960:ℤ) • (Wm * Mz) =
    (5:ℤ) • (L12ᵀ * Wm * L12) + (27:ℤ) • (L20ᵀ * Wm * L20) + (10:ℤ) • (L24ᵀ * Wm * L24) := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, WM_apply, LWL_apply, L12_lit, L20_lit,
    L24_lit, Mz, Matrix.of_apply]
  have h := psd_chk i j
  simp only [List.sum_ofFn] at h
  exact h

abbrev φ : Matrix (Fin 16) (Fin 16) ℤ →+* Matrix (Fin 16) (Fin 16) ℝ := (Int.castRingHom ℝ).mapMatrix

theorem φ_apply (A : Matrix (Fin 16) (Fin 16) ℤ) (i j : Fin 16) : φ A i j = (A i j : ℝ) := rfl

theorem φ_smul (k : ℤ) (A : Matrix (Fin 16) (Fin 16) ℤ) : φ (k • A) = (k : ℝ) • φ A := by
  ext i j; simp only [φ_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul]

theorem tendsto_exp_neg (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun s : ℝ => Real.exp (-c * s)) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun s : ℝ => -c * s) Filter.atTop Filter.atBot := by
    have := Filter.tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop hc Filter.tendsto_id)
    refine this.congr (fun s => ?_); simp only [Function.comp, id]; ring
  exact Real.tendsto_exp_atBot.comp h1

theorem quad_nonneg (L : Matrix (Fin 16) (Fin 16) ℤ) (x : Fin 16 → ℝ) :
    0 ≤ x ⬝ᵥ (φ (Lᵀ * Wm * L) *ᵥ x) := by
  have e : φ (Lᵀ * Wm * L) = (φ L)ᵀ * Matrix.diagonal (fun i => (wv i : ℝ)) * φ L := by
    rw [map_mul, map_mul]; congr 2
    all_goals (ext i j; first | rfl | (rw [φ_apply]; simp only [Wm, Matrix.diagonal_apply]; split_ifs <;> simp))
  rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_nonneg fun i _ => by
    have := wv_pos i
    have h : (0:ℝ) < wv i := by exact_mod_cast this
    nlinarith [sq_nonneg ((φ L *ᵥ x) i)]

/-- C07-79 (positivity): ⟨x, Q_f x⟩_W ≥ 0 for every real x, i.e. Q_f = M/4 is positive semidefinite in
the tensor-product inner product. -/
theorem Qf_psd (x : Fin 16 → ℝ) : 0 ≤ x ⬝ᵥ (φ (Wm * Mz) *ᵥ x) := by
  have h := congrArg φ psd_identity
  simp only [φ_smul, map_add] at h
  have key : (552960:ℝ) * (x ⬝ᵥ (φ (Wm * Mz) *ᵥ x)) =
      5 * (x ⬝ᵥ (φ (L12ᵀ * Wm * L12) *ᵥ x)) + 27 * (x ⬝ᵥ (φ (L20ᵀ * Wm * L20) *ᵥ x)) +
        10 * (x ⬝ᵥ (φ (L24ᵀ * Wm * L24) *ᵥ x)) := by
    have := congrArg (fun A => x ⬝ᵥ (A *ᵥ x)) h
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul] at this
    push_cast at this
    linarith
  have := quad_nonneg L12 x; have := quad_nonneg L20 x; have := quad_nonneg L24 x
  nlinarith

/-! ### Real spectral projectors and the transfer semigroup e^{−sQ_f} -/

def Qr : Matrix (Fin 16) (Fin 16) ℝ := (1/4 : ℝ) • φ Mz
def P3 : Matrix (Fin 16) (Fin 16) ℝ := (1/5760 : ℝ) • φ L0
def P2 : Matrix (Fin 16) (Fin 16) ℝ := (1/1152 : ℝ) • φ L12
def P1 : Matrix (Fin 16) (Fin 16) ℝ := (1/640 : ℝ) • φ L20
def P0 : Matrix (Fin 16) (Fin 16) ℝ := (1/1152 : ℝ) • φ L24


theorem eig_real : Qr * P3 = 0 ∧ Qr * P2 = (3:ℝ) • P2 ∧ Qr * P1 = (5:ℝ) • P1 ∧ Qr * P0 = (6:ℝ) • P0 := by
  obtain ⟨e0, e12, e20, e24⟩ := eigen_relations
  have m : ∀ A : Matrix (Fin 16) (Fin 16) ℤ, ∀ a b : ℝ, (a • φ Mz) * (b • φ A) = (a * b) • φ (Mz * A) := by
    intro A a b; rw [map_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Qr, P3, m, e0, map_zero, smul_zero]
  · rw [Qr, P2, m, e12, φ_smul, smul_smul, smul_smul]; norm_num
  · rw [Qr, P1, m, e20, φ_smul, smul_smul, smul_smul]; norm_num
  · rw [Qr, P0, m, e24, φ_smul, smul_smul, smul_smul]; norm_num

theorem resolution_real : P3 + P2 + P1 + P0 = 1 := by
  have h := congrArg φ resolution.1
  simp only [map_add, φ_smul, map_one] at h
  simp only [P3, P2, P1, P0]
  have : (1:Matrix (Fin 16) (Fin 16) ℝ) = (1/5760 : ℝ) • ((5760:ℤ):ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) := by
    rw [smul_smul]; norm_num
  rw [this, ← h]
  simp only [smul_add, smul_smul]; norm_num

theorem exp_mul_eigen (A P : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) (h : A * P = c • P) :
    NormedSpace.exp A * P = Real.exp c • P := by
  have hpow : ∀ k : ℕ, A ^ k * P = c ^ k • P := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Matrix.mul_assoc, ih, Matrix.mul_smul, h, smul_smul, pow_succ]
  open scoped Norms.Operator in
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).mul_right P
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) c).smul_const P
  rw [← Real.exp_eq_exp_ℝ] at h2
  have h3 : HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹ • A ^ k) * P) (Real.exp c • P) := by
    simp_rw [Matrix.smul_mul, hpow, smul_smul]; simpa [smul_eq_mul] using h2
  exact h1.unique h3

/-- C04-44, C04-73: T_s = e^{−sQ_f} = P₃ + e^{−3s}P₂ + e^{−5s}P₁ + e^{−6s}P₀ for every real s. -/
theorem transfer_formula (s : ℝ) :
    NormedSpace.exp (-s • Qr) = P3 + Real.exp (-3 * s) • P2 + Real.exp (-5 * s) • P1 + Real.exp (-6 * s) • P0 := by
  obtain ⟨q3, q2, q1, q0⟩ := eig_real
  have e : ∀ (P : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ), Qr * P = c • P →
      NormedSpace.exp (-s • Qr) * P = Real.exp (-c * s) • P := by
    intro P c h; apply exp_mul_eigen
    rw [Matrix.smul_mul, h, smul_smul]; ring_nf
  calc NormedSpace.exp (-s • Qr) = NormedSpace.exp (-s • Qr) * (P3 + P2 + P1 + P0) := by
        rw [resolution_real, Matrix.mul_one]
    _ = _ := by
        rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_add, e P3 0 (by rw [q3, zero_smul]), e P2 3 q2, e P1 5 q1,
          e P0 6 q0]
        simp

/-- C04-44: the semigroup law T_s T_t = T_{s+t}. -/
theorem transfer_semigroup (s t : ℝ) :
    NormedSpace.exp (-s • Qr) * NormedSpace.exp (-t • Qr) = NormedSpace.exp (-(s + t) • Qr) := by
  rw [← Matrix.exp_add_of_commute]
  · congr 1; rw [neg_add, add_smul]
  · exact (Commute.refl Qr).smul_left _ |>.smul_right _

/-- C04-44: T_s → P₃ (the projector onto ker Q_f = V₃) as s → ∞. -/
theorem transfer_limit :
    Filter.Tendsto (fun s : ℝ => NormedSpace.exp (-s • Qr)) Filter.atTop (nhds P3) := by
  simp_rw [transfer_formula]
  have t := tendsto_exp_neg
  have h := ((tendsto_const_nhds (x := P3)).add ((t 3 (by norm_num)).smul_const P2)).add
    ((t 5 (by norm_num)).smul_const P1) |>.add ((t 6 (by norm_num)).smul_const P0)
  simpa using h

/-- C07-79: F₃ e^{−sQ_f} F₃† = I on V₃ for every real s (Q_f annihilates V₃), and
C04-73: (I − T_s) acts on V_J as 1 − e^{−c_J s} with (c₂, c₁, c₀) = (3, 5, 6). -/
theorem fixed_on_V3 (s : ℝ) :
    NormedSpace.exp (-s • Qr) * P3 = P3 ∧
      (1 - NormedSpace.exp (-s • Qr)) * P2 = (1 - Real.exp (-3 * s)) • P2 ∧
      (1 - NormedSpace.exp (-s • Qr)) * P1 = (1 - Real.exp (-5 * s)) • P1 ∧
      (1 - NormedSpace.exp (-s • Qr)) * P0 = (1 - Real.exp (-6 * s)) • P0 := by
  obtain ⟨q3, q2, q1, q0⟩ := eig_real
  have e : ∀ (P : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ), Qr * P = c • P →
      NormedSpace.exp (-s • Qr) * P = Real.exp (-c * s) • P := by
    intro P c h; apply exp_mul_eigen
    rw [Matrix.smul_mul, h, smul_smul]; ring_nf
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e P3 0 (by rw [q3, zero_smul])]; simp
  · rw [Matrix.sub_mul, Matrix.one_mul, e P2 3 q2, sub_smul, one_smul]
  · rw [Matrix.sub_mul, Matrix.one_mul, e P1 5 q1, sub_smul, one_smul]
  · rw [Matrix.sub_mul, Matrix.one_mul, e P0 6 q0, sub_smul, one_smul]

/-- C04-73 (scalar content): ℓ_J²(s) = 1 − e^{−c_J s} lies in (0, 1) for every finite s > 0, so
ℓ_J² = 1 for all J holds for no finite s > 0, and ℓ_J²(s) → 1 as s → ∞. -/
theorem dilation_weights (c : ℝ) (hc : 0 < c) :
    (∀ s : ℝ, 0 < s → 0 < 1 - Real.exp (-c * s) ∧ 1 - Real.exp (-c * s) < 1) ∧
      Filter.Tendsto (fun s : ℝ => 1 - Real.exp (-c * s)) Filter.atTop (nhds 1) := by
  refine ⟨fun s hs => ⟨?_, ?_⟩, ?_⟩
  · have : Real.exp (-c * s) < 1 := by
      calc Real.exp (-c * s) < Real.exp 0 := Real.exp_lt_exp.mpr (by nlinarith)
        _ = 1 := Real.exp_zero
    linarith
  · linarith [Real.exp_pos (-c * s)]
  · have h := tendsto_exp_neg c hc
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub h

/-- C07-79 (kernel): for real x, Q_f x = 0 iff P₃ x = x; ker Q_f = V₃. -/
theorem kernel_V3 (x : Fin 16 → ℝ) : Qr *ᵥ x = 0 ↔ P3 *ᵥ x = x := by
  obtain ⟨q3, q2, q1, q0⟩ := eig_real
  constructor
  · intro hx
    have hP : ∀ (P : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ), c ≠ 0 → Qr * P = c • P → P * Qr = Qr * P → P *ᵥ x = 0 := by
      intro P c hc h hcomm
      have : c • (P *ᵥ x) = 0 := by
        rw [← Matrix.smul_mulVec, ← h, ← hcomm, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
      exact (smul_eq_zero.mp this).resolve_left hc
    have c12 : P2 * Qr = Qr * P2 := by
      simp only [P2, Qr, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← map_mul]
      rw [show L12 * Mz = Mz * L12 by simp only [L12]; noncomm_ring, mul_comm (1/4 : ℝ)]
    have c20 : P1 * Qr = Qr * P1 := by
      simp only [P1, Qr, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← map_mul]
      rw [show L20 * Mz = Mz * L20 by simp only [L20]; noncomm_ring, mul_comm (1/4 : ℝ)]
    have c24 : P0 * Qr = Qr * P0 := by
      simp only [P0, Qr, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← map_mul]
      rw [show L24 * Mz = Mz * L24 by simp only [L24]; noncomm_ring, mul_comm (1/4 : ℝ)]
    have h2 := hP P2 3 (by norm_num) q2 c12
    have h1 := hP P1 5 (by norm_num) q1 c20
    have h0 := hP P0 6 (by norm_num) q0 c24
    have hr := congrArg (fun A => A *ᵥ x) resolution_real
    simp only [Matrix.add_mulVec, Matrix.one_mulVec, h2, h1, h0, add_zero] at hr
    exact hr
  · intro hx
    rw [← hx, Matrix.mulVec_mulVec, q3, Matrix.zero_mulVec]

/-! ### C09-14: exact leakage sum -/


theorem G_chk : ∀ i j : Fin 16,
    (List.ofFn fun k => (List.ofFn fun l => krF IdF HsF i l * L0F l k).sum * krF IdF HsF k j).sum +
    2 * ((List.ofFn fun k => (List.ofFn fun l => krF IdF JpF i l * L0F l k).sum * krF IdF JmF k j).sum +
      (List.ofFn fun k => (List.ofFn fun l => krF IdF JmF i l * L0F l k).sum * krF IdF JpF k j).sum) = GF i j := by
  decide +kernel

def G : Matrix (Fin 16) (Fin 16) ℤ :=
  kr 1 Hs * L0 * kr 1 Hs + (2:ℤ) • (kr 1 Jp * L0 * kr 1 Jm + kr 1 Jm * L0 * kr 1 Jp)

theorem G_lit : G = Matrix.of GF := by
  rw [G, L0_lit, one4, Hs, Jp, Jm, kr_of, kr_of, kr_of]; ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul16]
  exact G_chk i j

theorem leak_chk : ∀ i j : Fin 16,
    5 * 1152 * (List.ofFn fun k => (List.ofFn fun l => YF i l * GF l k).sum * YF k j).sum =
      21 * 5760 ^ 3 * L12F i j := by decide +kernel

/-- C09-14 (integer form): 5·1152 · Y G Y = 21·5760³ · L₁₂ with
G = (I⊗H)L₀(I⊗H) + 2[(I⊗J₊)L₀(I⊗J₋) + (I⊗J₋)L₀(I⊗J₊)]. -/
theorem leakage_int : (5 * 1152 : ℤ) • (Y * G * Y) = (21 * 5760 ^ 3 : ℤ) • L12 := by
  rw [Y_of, G_lit, L12_lit]; ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, mul16, Matrix.of_apply]
  exact leak_chk i j

/-- C09-14: with J^a Hermitian and P₃, P_Q orthogonal projectors, B_a = P₃J_R^aP_Q gives
Σ_a B_a†B_a = P_Q(Σ_a J_R^a P₃ J_R^a)P_Q = P_Q[J_z P₃ J_z + ½(J₊P₃J₋ + J₋P₃J₊)]_R P_Q, a basis-independent
expression. In the ladder basis (J_z = H/2) it equals (21/20)P₂, P₂ = L₁₂/1152 the J = 2 projector. -/
theorem leakage :
    let PQ : Matrix (Fin 16) (Fin 16) ℝ := (1/5760 : ℝ) • φ Y
    let JzR : Matrix (Fin 16) (Fin 16) ℝ := (1/2 : ℝ) • φ (kr 1 Hs)
    PQ * (JzR * P3 * JzR + (1/2 : ℝ) • (φ (kr 1 Jp) * P3 * φ (kr 1 Jm) + φ (kr 1 Jm) * P3 * φ (kr 1 Jp))) * PQ =
      (21/20 : ℝ) • P2 := by
  intro PQ JzR
  have h := congrArg φ leakage_int
  simp only [φ_smul, map_mul, G, map_add] at h
  simp only [PQ, JzR, P3, P2]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, smul_add, smul_smul] at h ⊢
  have h' := congrArg (fun A => ((1:ℝ) / (5 * 1152 * 5760 ^ 3 * 4)) • A) h
  simp only [smul_add, smul_smul] at h'
  push_cast at h'
  convert h' using 2 <;> norm_num

/-- C09-14 (isotropic weighting): if Σ_i ω_i^a ω_i^b = (ω²/3)δ^{ab} then
Σ_{i,a,b} ω_i^a ω_i^b X_{ab} = (ω²/3) Σ_a X_{aa}; with X_{ab} = B_a†B_b this gives (7/20)ω² P₂. -/
theorem isotropic_weighting {M : Type*} [AddCommGroup M] [Module ℝ M] (X : Fin 3 → Fin 3 → M)
    (ω : Fin 3 → Fin 3 → ℝ) (w2 : ℝ) (h : ∀ a b, ∑ i, ω i a * ω i b = if a = b then w2 / 3 else 0) :
    ∑ i, ∑ a, ∑ b, (ω i a * ω i b) • X a b = (w2 / 3) • ∑ a, X a a := by
  have e : ∑ i, ∑ a, ∑ b, (ω i a * ω i b) • X a b = ∑ a, ∑ b, (∑ i, ω i a * ω i b) • X a b := by
    rw [Finset.sum_comm]; congr 1; ext a; rw [Finset.sum_comm]; congr 1; ext b; rw [Finset.sum_smul]
  rw [e, Finset.smul_sum]; congr 1; ext a
  simp_rw [h, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem leakage_weighted (ω : Fin 3 → Fin 3 → ℝ) (w2 : ℝ)
    (h : ∀ a b, ∑ i, ω i a * ω i b = if a = b then w2 / 3 else 0) (S : Matrix (Fin 16) (Fin 16) ℝ)
    (B : Fin 3 → Fin 3 → Matrix (Fin 16) (Fin 16) ℝ) (hS : ∑ a, B a a = S) (hS' : S = (21/20 : ℝ) • P2) :
    ∑ i, ∑ a, ∑ b, (ω i a * ω i b) • B a b = ((7/20 : ℝ) * w2) • P2 := by
  rw [isotropic_weighting B ω w2 h, hS, hS', smul_smul]; ring_nf

/-! ### C04-39: dual generators -/

/-- C04-39: if [A, B] = iC then [−Aᵀ, −Bᵀ] = i(−Cᵀ); applied to the cyclic triples this gives the su(2)
relations for J^∨a = −(J^a)ᵀ. -/
theorem dual_commutator {n : Type*} [Fintype n] [DecidableEq n] (A B C : Matrix n n ℂ)
    (h : A * B - B * A = Complex.I • C) : (-Aᵀ) * (-Bᵀ) - (-Bᵀ) * (-Aᵀ) = Complex.I • (-Cᵀ) := by
  have : (-Aᵀ) * (-Bᵀ) - (-Bᵀ) * (-Aᵀ) = -(A * B - B * A)ᵀ := by
    simp only [neg_mul_neg, Matrix.transpose_sub, Matrix.transpose_mul]; abel
  rw [this, h, Matrix.transpose_smul, smul_neg]

def WdF : Fin 4 → Fin 4 → ℤ := ![![0, 0, 0, 1], ![0, 0, -1, 0], ![0, 1, 0, 0], ![-1, 0, 0, 0]]

theorem dual_chk : ∀ i j : Fin 4,
    (List.ofFn fun k => WdF i k * -HsF j k).sum = (List.ofFn fun k => HsF i k * WdF k j).sum ∧
    (List.ofFn fun k => WdF i k * -JpF j k).sum = (List.ofFn fun k => JpF i k * WdF k j).sum ∧
    (List.ofFn fun k => WdF i k * -JmF j k).sum = (List.ofFn fun k => JmF i k * WdF k j).sum ∧
    (List.ofFn fun k => WdF i k * WdF k j).sum = -(if i = j then 1 else 0) := by decide +kernel

/-- C04-39 (spin 3/2): the dual generators (−Hᵀ, −J₊ᵀ, −J₋ᵀ) are carried to (H, J₊, J₋) by the invertible
W (W² = −I), so the dual of V_{3/2} is equivalent to V_{3/2}. -/
theorem dual_equivalent :
    Matrix.of WdF * (-Hsᵀ) = Hs * Matrix.of WdF ∧ Matrix.of WdF * (-Jpᵀ) = Jp * Matrix.of WdF ∧
      Matrix.of WdF * (-Jmᵀ) = Jm * Matrix.of WdF ∧ Matrix.of WdF * Matrix.of WdF = -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    simp only [mul4, Matrix.neg_apply, Matrix.transpose_apply, Matrix.of_apply, Hs, Jp, Jm, Matrix.one_apply]
  · exact (dual_chk i j).1
  · exact (dual_chk i j).2.1
  · exact (dual_chk i j).2.2.1
  · rw [(dual_chk i j).2.2.2]

/-! ### C04-40 (highest weight, j = 3/2) -/

theorem top_chk : (∀ i : Fin 16, L0F i 0 = if i = 0 then 5760 else 0) ∧ (∀ i : Fin 16, MzF i 0 = 0) := by
  decide +kernel

/-- C04-40 (j = 3/2): the top product state |3/2,3/2⟩⊗|3/2,3/2⟩ (ladder index 0) lies in V₃:
P₃ e₀ = e₀ and Q_f e₀ = 0. -/
theorem top_state : (∀ i : Fin 16, L0 i 0 = if i = 0 then 5760 else 0) ∧ (∀ i : Fin 16, Mz i 0 = 0) := by
  rw [L0_lit]; exact top_chk

end Entropic.Sweep.SpinPair
