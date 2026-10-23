import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

/-! Shannon subadditivity and the stationary dressing kernel (ledger C06-51, -52, -53;
C03-13). For a joint law P on X × Y with marginals p_X, p_Y:
H(X,Y) ≤ H(X) + H(Y), with equality iff P = p_X ⊗ p_Y. Hence H(Y|X) = H(X,Y) − H(X) ≤ H(Y). -/

noncomputable section
set_option linter.unusedSectionVars false
namespace Entropic.AppFG.Info
open Real Finset

variable {X Y : Type*} [Fintype X] [Fintype Y]

def pX (P : X → Y → ℝ) (x : X) : ℝ := ∑ y, P x y
def pY (P : X → Y → ℝ) (y : Y) : ℝ := ∑ x, P x y
def Hjoint (P : X → Y → ℝ) : ℝ := ∑ x, ∑ y, negMulLog (P x y)
def H {Z : Type*} [Fintype Z] (p : Z → ℝ) : ℝ := ∑ z, negMulLog (p z)

/-- Pointwise Gibbs inequality: −P ln P + P ln a + P ln b ≤ ab − P for 0 ≤ P ≤ a, P ≤ b. -/
theorem pointwise {P a b : ℝ} (hP : 0 ≤ P) (ha : P ≤ a) (hb : P ≤ b) :
    negMulLog P + P * Real.log a + P * Real.log b ≤ a * b - P := by
  rcases hP.eq_or_lt with h | h
  · subst h; simp; nlinarith
  · have ha0 : 0 < a := lt_of_lt_of_le h ha
    have hb0 : 0 < b := lt_of_lt_of_le h hb
    have hr : 0 < a * b / P := by positivity
    have := Real.log_le_sub_one_of_pos hr
    rw [Real.log_div (by positivity) h.ne', Real.log_mul ha0.ne' hb0.ne'] at this
    unfold negMulLog
    have e : P * (a * b / P - 1) = a * b - P := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left this h.le]

theorem pointwise_eq {P a b : ℝ} (hP : 0 ≤ P) (ha : P ≤ a) (hb : P ≤ b)
    (heq : negMulLog P + P * Real.log a + P * Real.log b = a * b - P) : P = a * b := by
  rcases hP.eq_or_lt with h | h
  · subst h; simp at heq; rcases heq with h | h <;> simp [h]
  · have ha0 : 0 < a := lt_of_lt_of_le h ha
    have hb0 : 0 < b := lt_of_lt_of_le h hb
    have hr : 0 < a * b / P := by positivity
    by_contra hne
    have h1 : a * b / P ≠ 1 := by
      intro h1; apply hne; field_simp at h1; linarith
    have := Real.log_lt_sub_one_of_pos hr h1
    rw [Real.log_div (by positivity) h.ne', Real.log_mul ha0.ne' hb0.ne'] at this
    unfold negMulLog at heq
    have e : P * (a * b / P - 1) = a * b - P := by field_simp
    nlinarith [mul_lt_mul_of_pos_left this h]

theorem le_pX {P : X → Y → ℝ} (hP : ∀ x y, 0 ≤ P x y) (x : X) (y : Y) : P x y ≤ pX P x :=
  Finset.single_le_sum (f := fun y => P x y) (fun y _ => hP x y) (Finset.mem_univ y)

theorem le_pY {P : X → Y → ℝ} (hP : ∀ x y, 0 ≤ P x y) (x : X) (y : Y) : P x y ≤ pY P y :=
  Finset.single_le_sum (f := fun x => P x y) (fun x _ => hP x y) (Finset.mem_univ x)

theorem sum_mul_log_pX (P : X → Y → ℝ) :
    ∑ x, ∑ y, P x y * Real.log (pX P x) = -H (pX P) := by
  simp only [H, negMulLog, pX, neg_mul, Finset.sum_neg_distrib, neg_neg]
  refine Finset.sum_congr rfl (fun x _ => ?_); rw [Finset.sum_mul]

theorem sum_mul_log_pY (P : X → Y → ℝ) :
    ∑ x, ∑ y, P x y * Real.log (pY P y) = -H (pY P) := by
  rw [Finset.sum_comm]
  simp only [H, negMulLog, pY, neg_mul, Finset.sum_neg_distrib, neg_neg]
  refine Finset.sum_congr rfl (fun y _ => ?_); rw [Finset.sum_mul]

/-- Subadditivity: H(X,Y) ≤ H(X) + H(Y). -/
theorem subadditive (P : X → Y → ℝ) (hP : ∀ x y, 0 ≤ P x y) (h1 : ∑ x, ∑ y, P x y = 1) :
    Hjoint P ≤ H (pX P) + H (pY P) := by
  have hpt := fun x y => pointwise (hP x y) (le_pX hP x y) (le_pY hP x y)
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) =>
    Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => hpt x y))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  rw [sum_mul_log_pX, sum_mul_log_pY, h1] at hsum
  have hprod : ∑ x, ∑ y, pX P x * pY P y = 1 := by
    rw [← Finset.sum_mul_sum]
    have : ∑ y, pY P y = 1 := by simp only [pY]; rw [Finset.sum_comm]; exact h1
    rw [this, mul_one]; exact h1
  rw [hprod] at hsum
  unfold Hjoint; linarith

/-- Equality iff independence. -/
theorem subadditive_eq_iff (P : X → Y → ℝ) (hP : ∀ x y, 0 ≤ P x y) (h1 : ∑ x, ∑ y, P x y = 1) :
    Hjoint P = H (pX P) + H (pY P) ↔ ∀ x y, P x y = pX P x * pY P y := by
  constructor
  · intro heq x y
    set f := fun x y => pX P x * pY P y - P x y -
      (negMulLog (P x y) + P x y * Real.log (pX P x) + P x y * Real.log (pY P y))
    have hf : ∀ x y, 0 ≤ f x y := fun x y => by
      have := pointwise (hP x y) (le_pX hP x y) (le_pY hP x y); simp only [f]; linarith
    have hsum0 : ∑ x, ∑ y, f x y = 0 := by
      simp only [f, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [sum_mul_log_pX, sum_mul_log_pY, h1]
      have hprod : ∑ x, ∑ y, pX P x * pY P y = 1 := by
        rw [← Finset.sum_mul_sum]
        have : ∑ y, pY P y = 1 := by simp only [pY]; rw [Finset.sum_comm]; exact h1
        rw [this, mul_one]; exact h1
      rw [hprod]; unfold Hjoint at heq; linarith
    have hx0 : ∑ y, f x y = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
        Finset.sum_nonneg (fun y _ => hf x y))).mp hsum0 x (Finset.mem_univ x)
      exact this
    have hxy : f x y = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hf x y)).mp hx0 y (Finset.mem_univ y)
    exact pointwise_eq (hP x y) (le_pX hP x y) (le_pY hP x y) (by simp only [f] at hxy; linarith)
  · intro hind
    have hpt : ∀ x y, negMulLog (P x y) + P x y * Real.log (pX P x) + P x y * Real.log (pY P y) =
        pX P x * pY P y - P x y := by
      intro x y
      rw [hind x y]
      rcases (mul_nonneg (Finset.sum_nonneg fun y _ => hP x y)
        (Finset.sum_nonneg fun x _ => hP x y) : 0 ≤ pX P x * pY P y).eq_or_lt with h | h
      · rw [← h]; simp
      · have ha : 0 < pX P x := by
          rcases (Finset.sum_nonneg fun y _ => hP x y : 0 ≤ pX P x).eq_or_lt with h' | h'
          · have e : pX P x = 0 := h'.symm
            rw [e] at h; simp at h
          · exact h'
        have hb : 0 < pY P y := by
          rcases (Finset.sum_nonneg fun x _ => hP x y : 0 ≤ pY P y).eq_or_lt with h' | h'
          · have e : pY P y = 0 := h'.symm
            rw [e] at h; simp at h
          · exact h'
        unfold negMulLog; rw [Real.log_mul ha.ne' hb.ne']; ring
    have := Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
      Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => hpt x y))
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at this
    rw [sum_mul_log_pX, sum_mul_log_pY, h1] at this
    have hprod : ∑ x, ∑ y, pX P x * pY P y = 1 := by
      rw [← Finset.sum_mul_sum]
      have : ∑ y, pY P y = 1 := by simp only [pY]; rw [Finset.sum_comm]; exact h1
      rw [this, mul_one]; exact h1
    rw [hprod] at this; unfold Hjoint; linarith

/-! ### Stationary dressing kernel (C06-51, -52, C03-13) -/

variable {B : Type*} [Fintype B]

/-- C06-51/C03-13: the product kernel K_*(b,b′) = p(b′) is detailed-balanced and stochastic. -/
theorem product_kernel_detailed_balance (p : B → ℝ) (hp1 : ∑ b, p b = 1) :
    (∀ b b', p b * p b' = p b' * p b) ∧ (∀ _b : B, ∑ b', p b' = 1) ∧
      (∀ b', ∑ b, p b * p b' = p b') := by
  refine ⟨fun b b' => mul_comm _ _, fun _ => hp1, fun b' => by rw [← Finset.sum_mul, hp1, one_mul]⟩

/-- C06-52: for a stationary pair with marginal p and kernel K (P(b,b′) = p(b)K(b,b′)),
H(B′|B) := H(B,B′) − H(B) ≤ H(p) = g, with equality iff K(b,b′) = p(b′) whenever p(b) > 0. -/
theorem dressing_bound (p : B → ℝ) (K : B → B → ℝ) (hp : ∀ b, 0 ≤ p b) (hp1 : ∑ b, p b = 1)
    (hK : ∀ b b', 0 ≤ K b b') (hrow : ∀ b, ∑ b', K b b' = 1)
    (hstat : ∀ b', ∑ b, p b * K b b' = p b') :
    Hjoint (fun b b' => p b * K b b') - H p ≤ H p ∧
      (Hjoint (fun b b' => p b * K b b') - H p = H p ↔ ∀ b b', 0 < p b → K b b' = p b') := by
  set P := fun b b' => p b * K b b'
  have hP : ∀ b b', 0 ≤ P b b' := fun b b' => mul_nonneg (hp b) (hK b b')
  have hPx : pX P = p := by funext b; simp only [pX, P, ← Finset.mul_sum, hrow, mul_one]
  have hPy : pY P = p := by funext b'; exact hstat b'
  have h1 : ∑ b, ∑ b', P b b' = 1 := by
    simp only [P, ← Finset.mul_sum, hrow, mul_one, hp1]
  have hs := subadditive P hP h1
  rw [hPx, hPy] at hs
  refine ⟨by linarith, ?_⟩
  have hiff := subadditive_eq_iff P hP h1
  rw [hPx, hPy] at hiff
  constructor
  · intro h b b' hb
    have := (hiff.mp (by linarith)) b b'
    simp only [P] at this
    exact mul_left_cancel₀ hb.ne' this
  · intro h
    have : Hjoint P = H p + H p := hiff.mpr (fun b b' => by
      simp only [P]
      rcases (hp b).eq_or_lt with h0 | h0
      · rw [← h0]; ring
      · rw [h b b' h0])
    linarith

/-- C06-53 (each step): conditioning cannot raise entropy, H(Y|X) ≤ H(Y); so every conditional
entropy of a stationary process is ≤ H(p), and so is any limit (the entropy rate). -/
theorem conditional_le (P : X → Y → ℝ) (hP : ∀ x y, 0 ≤ P x y) (h1 : ∑ x, ∑ y, P x y = 1) :
    Hjoint P - H (pX P) ≤ H (pY P) := by
  have := subadditive P hP h1; linarith

theorem rate_le {c : ℕ → ℝ} {h Hp : ℝ} (hc : ∀ n, c n ≤ Hp)
    (hlim : Filter.Tendsto c Filter.atTop (nhds h)) : h ≤ Hp :=
  le_of_tendsto' hlim hc

end Entropic.AppFG.Info
