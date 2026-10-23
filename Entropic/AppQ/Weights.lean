import Entropic.AppQ.Fock
import Entropic.AppFG.Subadditivity
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Appendix Q, weights and numbers: the spin-1 pair spectrum (C15-05, multiplicities 5, 3, 1),
SU(2) weight counts behind the intertwiner dimensions and top-spin multiplicities (C15-12, C15-69,
C15-70; the reduction dim Inv = c₀ − c₁ and mult V_J = c_J − c_{J+1} is standard SU(2) theory and is
not formalized here), the calibration numbers of C.8 (C15-57), and additivity of entropy over
independent bonds (C15-45, classical form). -/

noncomputable section
namespace Entropic.AppQ.W
open Real

/-! ### C15-05: V₁ ⊗ V₁ in the ladder basis (J₊ unit entries, J₋ entries 2, 2, H = 2J_z = diag(2,0,−2)) -/

def H1 : Fin 3 → Fin 3 → ℤ := ![![2,0,0],![0,0,0],![0,0,-2]]
def P1 : Fin 3 → Fin 3 → ℤ := ![![0,1,0],![0,0,1],![0,0,0]]
def N1 : Fin 3 → Fin 3 → ℤ := ![![0,0,0],![2,0,0],![0,2,0]]
def hi3 (i : Fin 9) : Fin 3 := ⟨i.val / 3, by omega⟩
def lo3 (i : Fin 9) : Fin 3 := ⟨i.val % 3, by omega⟩
def k3 (A B : Fin 3 → Fin 3 → ℤ) : Fin 9 → Fin 9 → ℤ := fun i j => A (hi3 i) (hi3 j) * B (lo3 i) (lo3 j)

/-- 4 J_L·J_R = H⊗H + 2(J₊⊗J₋ + J₋⊗J₊). -/
def M1 : Fin 9 → Fin 9 → ℤ := fun i j => k3 H1 H1 i j + 2 * (k3 P1 N1 i j + k3 N1 P1 i j)
def d9 (i j : Fin 9) : ℤ := if i = j then 1 else 0
def mm9 (A B : Fin 9 → Fin 9 → ℤ) (i j : Fin 9) : ℤ := (List.ofFn fun k => A i k * B k j).sum
def sh (A : Fin 9 → Fin 9 → ℤ) (c : ℤ) : Fin 9 → Fin 9 → ℤ := fun i j => A i j + c * d9 i j
def tr9 (A : Fin 9 → Fin 9 → ℤ) : ℤ := (List.ofFn fun k => A k k).sum

/-- [J₊, J₋] = H for spin 1 in the ladder basis. -/
theorem ladder1 : ∀ i j : Fin 3,
    (List.ofFn fun k => P1 i k * N1 k j).sum - (List.ofFn fun k => N1 i k * P1 k j).sum = H1 i j := by
  decide +kernel

/-- C15-05: (M − 4)(M + 4)(M + 8) = 0, Tr M = 0, Tr M² = 192, and the Lagrange traces give
multiplicities 5 (J = 2, 4J_L·J_R = 4), 3 (J = 1, −4), 1 (J = 0, −8): V₁ ⊗ V₁ = V₀ ⊕ V₁ ⊕ V₂ with
multiplicity one each (dimensions 1 + 3 + 5 = 9). -/
theorem spin1_pair :
    (∀ i j : Fin 9, mm9 (mm9 (sh M1 (-4)) (sh M1 4)) (sh M1 8) i j = 0) ∧ tr9 M1 = 0 ∧ tr9 (mm9 M1 M1) = 192 ∧
      tr9 (mm9 (sh M1 4) (sh M1 8)) = 5 * 96 ∧ tr9 (mm9 (sh M1 (-4)) (sh M1 8)) = 3 * (-32) ∧
      tr9 (mm9 (sh M1 (-4)) (sh M1 4)) = 1 * 48 := by
  decide +kernel

/-! ### SU(2) weight counts -/

/-- Polynomial (coefficient-list) product. -/
def pmul (a b : List ℕ) : List ℕ :=
  (List.range (a.length + b.length - 1)).map fun k =>
    ((List.range (k + 1)).map fun i => a.getD i 0 * b.getD (k - i) 0).sum

/-- Weight polynomial of V_j: 2j + 1 unit coefficients (exponent shifted by j). -/
def wpoly (j : ℕ) : List ℕ := List.replicate (2 * j + 1) 1

/-- Coefficient of total weight k (shifted by the sum s of the spins) in the product. -/
def coeffAt (p : List ℕ) (s : ℕ) (k : ℤ) : ℕ := p.getD (Int.toNat (k + s)) 0

/-- C15-69 (weight counts): c₀ − c₁ = 7 for V₃^{⊗4}, 7 for V₃ ⊗ V₉^{⊗3}, 19 for V₉^{⊗4}. -/
theorem intertwiner_counts :
    (coeffAt (pmul (pmul (pmul (wpoly 3) (wpoly 3)) (wpoly 3)) (wpoly 3)) 12 0 : ℤ) -
        coeffAt (pmul (pmul (pmul (wpoly 3) (wpoly 3)) (wpoly 3)) (wpoly 3)) 12 1 = 7 ∧
      (coeffAt (pmul (pmul (pmul (wpoly 3) (wpoly 9)) (wpoly 9)) (wpoly 9)) 30 0 : ℤ) -
        coeffAt (pmul (pmul (pmul (wpoly 3) (wpoly 9)) (wpoly 9)) (wpoly 9)) 30 1 = 7 ∧
      (coeffAt (pmul (pmul (pmul (wpoly 9) (wpoly 9)) (wpoly 9)) (wpoly 9)) 36 0 : ℤ) -
        coeffAt (pmul (pmul (pmul (wpoly 9) (wpoly 9)) (wpoly 9)) (wpoly 9)) 36 1 = 19 := by
  decide +kernel

/-- C15-70: in V₃^{⊗3} the top weight 9 occurs once and weight 10 never. -/
theorem top_fusion : coeffAt (pmul (pmul (wpoly 3) (wpoly 3)) (wpoly 3)) 9 9 = 1 ∧
    coeffAt (pmul (pmul (wpoly 3) (wpoly 3)) (wpoly 3)) 9 10 = 0 := by decide +kernel

/-- C15-12 (weights, all N): for labels m_i ∈ {−3,…,3}, Σm_i ≤ 3N with equality iff every m_i = 3;
so the top weight 3N occurs exactly once and no larger weight occurs. -/
theorem top_weight (N : ℕ) (f : Fin N → Fin 7) :
    ∑ i, ((f i).val - 3 : ℤ) ≤ 3 * N ∧ (∑ i, ((f i).val - 3 : ℤ) = 3 * N ↔ ∀ i, (f i).val = 6) := by
  have hle : ∀ i, ((f i).val - 3 : ℤ) ≤ 3 := fun i => by have := (f i).isLt; omega
  have hsum : ∑ i, ((f i).val - 3 : ℤ) ≤ 3 * N := by
    calc ∑ i, ((f i).val - 3 : ℤ) ≤ ∑ _i : Fin N, (3:ℤ) := Finset.sum_le_sum (fun i _ => hle i)
      _ = 3 * N := by simp [mul_comm]
  refine ⟨by linarith, ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hz : ∑ i, (3 - ((f i).val - 3 : ℤ)) = 0 := by
      rw [Finset.sum_sub_distrib, h]; simp; ring
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by linarith [hle i])).mp hz
    intro i; have := this i (Finset.mem_univ i); omega
  · simp only [h]; simp; ring

/-! ### C15-57: calibration numbers (a = 2.56812077553 L*) -/

/-- C15-57: A_SL = (√3/4)a² ∈ (2.855824561, 2.855824562) and A_SL/(4 ln 2) ∈ (1.030020982, 1.030020984)
(quoted 1.03002). -/
theorem calibration_numbers :
    2.855824561 < Real.sqrt 3 / 4 * 2.56812077553 ^ 2 ∧ Real.sqrt 3 / 4 * 2.56812077553 ^ 2 < 2.855824562 ∧
      1.030020982 < Real.sqrt 3 / 4 * 2.56812077553 ^ 2 / (4 * Real.log 2) ∧
      Real.sqrt 3 / 4 * 2.56812077553 ^ 2 / (4 * Real.log 2) < 1.030020984 := by
  have s1 : (1.7320508075 : ℝ) < Real.sqrt 3 := by
    rw [show (1.7320508075:ℝ) = Real.sqrt (1.7320508075 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have s2 : Real.sqrt 3 < (1.7320508076 : ℝ) := by
    rw [show (1.7320508076:ℝ) = Real.sqrt (1.7320508076 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have l1 := Real.log_two_gt_d9; have l2 := Real.log_two_lt_d9
  have hp : 0 < 4 * Real.log 2 := by linarith
  refine ⟨by nlinarith, by nlinarith, ?_, ?_⟩
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

/-! ### C15-45 (classical form): additivity over independent bonds -/

section Bonds
open Entropic.AppFG.Info
variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- For a product law p ⊗ q the joint entropy is H(p) + H(q); a single cut bond (uniform on two
outcomes) contributes ln 2. -/
theorem product_entropy (p : X → ℝ) (q : Y → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ y, 0 ≤ q y)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ y, q y = 1) :
    Hjoint (fun x y => p x * q y) = H p + H q := by
  have hX : pX (fun x y => p x * q y) = p := by funext x; simp [pX, ← Finset.mul_sum, hq1]
  have hY : pY (fun x y => p x * q y) = q := by funext y; simp [pY, ← Finset.sum_mul, hp1]
  have := (subadditive_eq_iff (fun x y => p x * q y) (fun x y => mul_nonneg (hp x) (hq y))
    (by simp [← Finset.mul_sum, hq1, hp1])).mpr (fun x y => by rw [hX, hY])
  rw [this, hX, hY]

theorem cut_bond : H (fun _ : Fin 2 => (1/2 : ℝ)) = Real.log 2 := by
  simp [H, Real.negMulLog]
end Bonds

end Entropic.AppQ.W
