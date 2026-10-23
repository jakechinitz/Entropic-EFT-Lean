import Entropic.AppO.Flow
import Entropic.AppP.Records
import Entropic.AppIJ.Shells

/-! Chunk 14 sweep: C04-34, fused-label information cap (data processing plus maximum entropy). -/

noncomputable section
namespace Entropic.Sweep.Info
open Entropic.AppFG.Info Entropic.AppO Real Finset

variable {X Y Λ : Type*} [Fintype X] [Fintype Y] [Fintype Λ]

theorem term_kl {q a b : ℝ} (hq : 0 ≤ q) (ha : q ≤ a) (hb : q ≤ b) :
    q * Real.log q - q * Real.log a - q * Real.log b = q * (Real.log q - Real.log (a * b)) := by
  rcases hq.eq_or_lt with h | h
  · rw [← h]; simp
  · rw [Real.log_mul (by linarith) (by linarith)]; ring

/-- Mutual information in Kullback–Leibler form: I(Q) = Σ Q (ln Q − ln(Q_X Q_Y)). -/
theorem mi_kl (Q : X → Y → ℝ) (hQ : ∀ x y, 0 ≤ Q x y) :
    mutualInfo Q = ∑ x, ∑ y, Q x y * (Real.log (Q x y) - Real.log (pX Q x * pY Q y)) := by
  have hX : H (pX Q) = -∑ x, ∑ y, Q x y * Real.log (pX Q x) := by
    simp only [H, negMulLog, pX, neg_mul, Finset.sum_neg_distrib, neg_neg, ← Finset.sum_mul]
  have hY : H (pY Q) = -∑ x, ∑ y, Q x y * Real.log (pY Q y) := by rw [sum_mul_log_pY, neg_neg]
  have hJ : Hjoint Q = -∑ x, ∑ y, Q x y * Real.log (Q x y) := by
    simp only [Hjoint, negMulLog, neg_mul, Finset.sum_neg_distrib, neg_neg]
  rw [mutualInfo, hX, hY, hJ]
  have : ∀ x y, Q x y * (Real.log (Q x y) - Real.log (pX Q x * pY Q y)) =
      Q x y * Real.log (Q x y) - Q x y * Real.log (pX Q x) - Q x y * Real.log (pY Q y) := by
    intro x y
    refine (term_kl (hQ x y) ?_ ?_).symm
    · exact Finset.single_le_sum (f := fun y' => Q x y') (fun y' _ => hQ x y') (Finset.mem_univ y)
    · exact Finset.single_le_sum (f := fun x' => Q x' y) (fun x' _ => hQ x' y) (Finset.mem_univ x)
  simp only [this, Finset.sum_sub_distrib]; ring

/-- I(X;L) ≤ H(L). -/
theorem mi_le_H (P : X → Λ → ℝ) (hP : ∀ x l, 0 ≤ P x l) : mutualInfo P ≤ H (pY P) := by
  have h := H_le_joint (fun l x => P x l) (fun l x => hP x l)
  have e1 : pY (fun l x => P x l) = pX P := rfl
  have e2 : Hjoint (fun l x => P x l) = Hjoint P := by
    simp only [Hjoint]; exact Finset.sum_comm
  rw [e1, e2] at h
  unfold mutualInfo; linarith

variable [DecidableEq X]

/-- C04-34: if X — L — Y is Markov (P(x, y) = Σ_l P(x, l) K(y | l)) with full-support marginals of X and
L, then I(X;Y) ≤ I(X;L) ≤ H(L) ≤ ln |L|; with a seven-valued shared label, I(X;Y) ≤ ln 7. -/
theorem fused_label_cap [Nonempty Λ] (P : X → Λ → ℝ) (K : Λ → Y → ℝ) (hP : ∀ x l, 0 ≤ P x l)
    (h1 : ∑ x, ∑ l, P x l = 1) (hpX : ∀ x, 0 < pX P x) (hpL : ∀ l, 0 < pY P l)
    (hK : ∀ l y, 0 ≤ K l y) (hK1 : ∀ l, ∑ y, K l y = 1) :
    mutualInfo (fun x y => ∑ l, P x l * K l y) ≤ mutualInfo P ∧ mutualInfo P ≤ H (pY P) ∧
      H (pY P) ≤ Real.log (Fintype.card Λ) := by
  set Q : X → Y → ℝ := fun x y => ∑ l, P x l * K l y
  have hQ : ∀ x y, 0 ≤ Q x y := fun x y => Finset.sum_nonneg (fun l _ => mul_nonneg (hP x l) (hK l y))
  refine ⟨?_, mi_le_H P hP, ?_⟩
  · -- data processing on B = X × Λ, G = X × Y
    let Pd : X × Λ → ℝ := fun b => P b.1 b.2
    let Ps : X × Λ → ℝ := fun b => pX P b.1 * pY P b.2
    let M : X × Λ → X × Y → ℝ := fun b g => if b.1 = g.1 then K b.2 g.2 else 0
    have hM : ∀ b g, 0 ≤ M b g := fun b g => by simp only [M]; split_ifs; exact hK _ _; exact le_rfl
    have hM1 : ∀ b, ∑ g, M b g = 1 := by
      intro b; rw [Fintype.sum_prod_type]; simp only [M]
      rw [Finset.sum_eq_single b.1]
      · simp [hK1]
      · intro x _ hx; simp [Ne.symm hx]
      · simp
    have hdp := Entropic.AppP.data_processing Pd Ps M (fun b => hP _ _)
      (fun b => mul_pos (hpX _) (hpL _)) hM hM1
    have eD : ∀ g : X × Y, ∑ b, Pd b * M b g = Q g.1 g.2 := by
      intro g; rw [Fintype.sum_prod_type]; simp only [Pd, M, Q, mul_ite, mul_zero]
      rw [Finset.sum_eq_single g.1]
      · simp
      · intro x _ hx; simp [hx]
      · simp
    have eS : ∀ g : X × Y, ∑ b, Ps b * M b g = pX Q g.1 * pY Q g.2 := by
      intro g; rw [Fintype.sum_prod_type]; simp only [Ps, M, mul_ite, mul_zero]
      rw [Finset.sum_eq_single g.1]
      · simp only [if_true]
        have a1 : pX Q g.1 = pX P g.1 := by
          simp only [pX, Q]; rw [Finset.sum_comm]
          simp_rw [← Finset.mul_sum, hK1, mul_one]
        have a2 : pY Q g.2 = ∑ l, pY P l * K l g.2 := by
          simp only [pY, Q, Finset.sum_mul]; rw [Finset.sum_comm]
        rw [a1, a2, Finset.mul_sum]; congr 1; ext l; ring
      · intro x _ hx; simp [hx]
      · simp
    simp only [eD, eS] at hdp
    rw [mi_kl Q hQ, mi_kl P hP]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at hdp
    convert hdp using 2
  · have hsum : ∑ l, pY P l = 1 := by
      simp only [pY]; rw [Finset.sum_comm]; exact h1
    have := (Entropic.AppIJ.entropy_le_log_card (pY P) hpL hsum).1
    have e : H (pY P) = -∑ b, pY P b * Real.log (pY P b) := by
      simp only [H, negMulLog, neg_mul, Finset.sum_neg_distrib]
    rw [e]; exact this

/-- C04-34 with a seven-valued label: I(X;Y) ≤ ln 7. -/
theorem seven_label_cap (P : X → Fin 7 → ℝ) (K : Fin 7 → Y → ℝ) (hP : ∀ x l, 0 ≤ P x l)
    (h1 : ∑ x, ∑ l, P x l = 1) (hpX : ∀ x, 0 < pX P x) (hpL : ∀ l, 0 < pY P l)
    (hK : ∀ l y, 0 ≤ K l y) (hK1 : ∀ l, ∑ y, K l y = 1) :
    mutualInfo (fun x y => ∑ l, P x l * K l y) ≤ Real.log 7 := by
  obtain ⟨a, b, c⟩ := fused_label_cap P K hP h1 hpX hpL hK hK1
  simp only [Fintype.card_fin, Nat.cast_ofNat] at c
  linarith

end Entropic.Sweep.Info
