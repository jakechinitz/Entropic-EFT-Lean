import Entropic.AppCDE.Information

/-! Fixed-total-count fluctuations (ledger C05-36): N i.i.d. points with law p on a finite
set. For subregions A, B the counts C_A = Σ_i 1_A(x_i) have mean N p(A), variance
N p(A)(1 − p(A)), and covariance −N p(A)p(B) when A, B are disjoint. -/

noncomputable section
namespace Entropic.AppCDE.Sprinkling
open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {N : ℕ}

/-- Expectation under the product law p^{⊗N}. -/
def E (p : Ω → ℝ) (F : (Fin N → Ω) → ℝ) : ℝ := ∑ x : Fin N → Ω, (∏ k, p (x k)) * F x

theorem two_marginal (p : Ω → ℝ) (hp1 : ∑ ω, p ω = 1) {i j : Fin N} (hij : i ≠ j)
    (g h : Ω → ℝ) :
    E p (fun x => g (x i) * h (x j)) = (∑ ω, p ω * g ω) * (∑ ω, p ω * h ω) := by
  unfold E
  have : ∀ x : Fin N → Ω, (∏ k, p (x k)) * (g (x i) * h (x j)) =
      ∏ k, (p (x k) * (if k = i then g (x k) else if k = j then h (x k) else 1)) := by
    intro x
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => k = i)]
    rw [Finset.filter_eq' Finset.univ i, if_pos (Finset.mem_univ _), Finset.prod_singleton,
      if_pos rfl]
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ.filter fun k => ¬k = i) (fun k => k = j)]
    have hj : (Finset.univ.filter fun k => ¬k = i).filter (fun k => k = j) = {j} := by
      ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · intro h; subst h; exact ⟨hij.symm, rfl⟩
    rw [hj, Finset.prod_singleton, if_neg hij.symm, if_pos rfl]
    rw [Finset.prod_eq_one (fun k hk => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rw [if_neg hk.1, if_neg hk.2])]
    ring
  simp_rw [this]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (t := fun _ => Finset.univ)
    (f := fun k ω => p ω * (if k = i then g ω else if k = j then h ω else 1))]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => k = i ∨ k = j)]
  have hs : Finset.univ.filter (fun k : Fin N => k = i ∨ k = j) = {i, j} := by
    ext k; simp
  have hrest : ∏ k ∈ Finset.univ.filter (fun k : Fin N => ¬(k = i ∨ k = j)),
      ∑ ω, p ω * (if k = i then g ω else if k = j then h ω else 1) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hk
    simp only [if_neg hk.1, if_neg hk.2, mul_one, hp1]
  rw [hs, Finset.prod_pair hij, hrest, mul_one]
  simp [hij.symm]

theorem one_marginal (p : Ω → ℝ) (hp1 : ∑ ω, p ω = 1) (i : Fin N) (g : Ω → ℝ) :
    E p (fun x => g (x i)) = ∑ ω, p ω * g ω := prod_marginal p hp1 i g

theorem E_sum (p : Ω → ℝ) {ι : Type*} (s : Finset ι) (F : ι → (Fin N → Ω) → ℝ) :
    E p (fun x => ∑ i ∈ s, F i x) = ∑ i ∈ s, E p (F i) := by
  unfold E; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]

/-- Mean count: E[Σ_i g(x_i)] = N·E_p[g]. -/
theorem mean_count (p : Ω → ℝ) (hp1 : ∑ ω, p ω = 1) (g : Ω → ℝ) :
    E (N := N) p (fun x => ∑ i, g (x i)) = N * ∑ ω, p ω * g ω := by
  rw [E_sum]; simp_rw [one_marginal p hp1]; simp

/-- Second moment: E[(Σ_i g(x_i))(Σ_j h(x_j))] = N(N−1)E[g]E[h] + N·E[gh]. -/
theorem second_moment (p : Ω → ℝ) (hp1 : ∑ ω, p ω = 1) (g h : Ω → ℝ) :
    E (N := N) p (fun x => (∑ i, g (x i)) * (∑ j, h (x j))) =
      N * (N - 1) * ((∑ ω, p ω * g ω) * (∑ ω, p ω * h ω)) + N * ∑ ω, p ω * (g ω * h ω) := by
  rw [show (fun x : Fin N → Ω => (∑ i, g (x i)) * (∑ j, h (x j))) =
      fun x => ∑ i, ∑ j, g (x i) * h (x j) from funext fun x => Finset.sum_mul_sum _ _ _ _]
  rw [E_sum]; simp_rw [E_sum]
  have hrow : ∀ i : Fin N, ∑ j, E p (fun x => g (x i) * h (x j)) =
      (N - 1) * ((∑ ω, p ω * g ω) * (∑ ω, p ω * h ω)) + ∑ ω, p ω * (g ω * h ω) := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [show E p (fun x => g (x i) * h (x i)) = ∑ ω, p ω * (g ω * h ω) from
      one_marginal p hp1 i (fun ω => g ω * h ω)]
    rw [Finset.sum_congr rfl (fun j hj => two_marginal p hp1 (Ne.symm (Finset.ne_of_mem_erase hj)) g h)]
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · exact absurd i.isLt (by omega)
    · push_cast [Nat.cast_sub hpos]; ring
  simp_rw [hrow]; rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- For disjoint subregions A, B: Cov(C_A, C_B) = −N p(A)p(B); and Var(C_A) = N p(A)(1 − p(A)). -/
theorem count_moments (p : Ω → ℝ) (hp1 : ∑ ω, p ω = 1) (A B : Finset Ω) (hAB : Disjoint A B) :
    let pA := ∑ ω ∈ A, p ω
    let pB := ∑ ω ∈ B, p ω
    let CA := fun x : Fin N → Ω => ∑ i, (if x i ∈ A then (1:ℝ) else 0)
    let CB := fun x : Fin N → Ω => ∑ i, (if x i ∈ B then (1:ℝ) else 0)
    E p CA = N * pA ∧
      E p (fun x => CA x * CB x) - E p CA * E p CB = -(N * pA * pB) ∧
      E p (fun x => CA x * CA x) - E p CA * E p CA = N * pA * (1 - pA) := by
  intro pA pB CA CB
  have hA : ∑ ω, p ω * (if ω ∈ A then (1:ℝ) else 0) = pA := by
    simp [pA, Finset.sum_ite_mem, Finset.univ_inter]
  have hB : ∑ ω, p ω * (if ω ∈ B then (1:ℝ) else 0) = pB := by
    simp [pB, Finset.sum_ite_mem, Finset.univ_inter]
  have hAB0 : ∑ ω, p ω * ((if ω ∈ A then (1:ℝ) else 0) * (if ω ∈ B then 1 else 0)) = 0 := by
    apply Finset.sum_eq_zero; intro ω _
    by_cases ha : ω ∈ A
    · have : ω ∉ B := Finset.disjoint_left.mp hAB ha
      simp [ha, this]
    · simp [ha]
  have hAA : ∑ ω, p ω * ((if ω ∈ A then (1:ℝ) else 0) * (if ω ∈ A then 1 else 0)) = pA := by
    rw [← hA]; congr 1; ext ω; split_ifs <;> simp
  have mA := mean_count (N := N) p hp1 (fun ω => if ω ∈ A then (1:ℝ) else 0)
  have mB := mean_count (N := N) p hp1 (fun ω => if ω ∈ B then (1:ℝ) else 0)
  have sAB := second_moment (N := N) p hp1 (fun ω => if ω ∈ A then (1:ℝ) else 0)
    (fun ω => if ω ∈ B then (1:ℝ) else 0)
  have sAA := second_moment (N := N) p hp1 (fun ω => if ω ∈ A then (1:ℝ) else 0)
    (fun ω => if ω ∈ A then (1:ℝ) else 0)
  rw [hA] at mA; rw [hB] at mB
  rw [hA, hB, hAB0] at sAB; rw [hA, hAA] at sAA
  refine ⟨mA, ?_, ?_⟩
  · show E p (fun x => (∑ i, _) * (∑ j, _)) - _ = _
    rw [sAB, mA, mB]; ring
  · show E p (fun x => (∑ i, _) * (∑ j, _)) - _ = _
    rw [sAA, mA]; ring

end Entropic.AppCDE.Sprinkling
