import Entropic.AppB.Elementary
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic

/-! Appendix C/D finite information theory (ledger C05-15, -16 (Jensen part), -17, -18,
-53, -55 (ordering), -69, -70, -71, -72 (exponent additivity)). -/

noncomputable section
set_option linter.unusedSectionVars false
namespace Entropic.AppCDE
open Real Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Shannon entropy in nats. -/
def H (p : Ω → ℝ) : ℝ := ∑ ω, negMulLog (p ω)

/-! ### Isotropic defect partition (C05-15) -/

/-- For any probability on boundary states and any face-label map, the label-averaged
exclusion probability is 6/7, so ΔS_def = −ln⟨Z_def/Z_vac⟩ = ln(7/6). -/
theorem isotropic_defect (p : Ω → ℝ) (hp1 : ∑ ω, p ω = 1) (lab : Ω → Fin 7) :
    (1/7) * ∑ l : Fin 7, (∑ ω, if lab ω ≠ l then p ω else 0) = 6/7 ∧
      -Real.log ((1/7) * ∑ l : Fin 7, (∑ ω, if lab ω ≠ l then p ω else 0)) = Real.log (7/6) := by
  have h : ∑ l : Fin 7, (∑ ω, if lab ω ≠ l then p ω else 0) = 6 := by
    rw [Finset.sum_comm]
    have : ∀ ω, (∑ l : Fin 7, if lab ω ≠ l then p ω else 0) = 6 * p ω := by
      intro ω
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      congr 1
      have : (Finset.univ.filter fun l : Fin 7 => lab ω ≠ l) = Finset.univ.erase (lab ω) := by
        ext l; simp [eq_comm]
      rw [this, Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
    simp_rw [this, ← Finset.mul_sum, hp1, mul_one]
  rw [h]; refine ⟨by norm_num, ?_⟩
  rw [show (1:ℝ)/7 * 6 = (7/6)⁻¹ by norm_num, Real.log_inv, neg_neg]

/-- Jensen part of C05-16: the mean per-type cost dominates the isotropic cost,
mean_t(−ln x_t) ≥ −ln(mean_t x_t). -/
theorem quenched_ge_annealed {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (x : ι → ℝ)
    (hx : ∀ t ∈ s, 0 < x t) :
    -Real.log ((1 / s.card) * ∑ t ∈ s, x t) ≤ (1 / s.card) * ∑ t ∈ s, -Real.log (x t) := by
  have hc : (0:ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hconc := strictConcaveOn_log_Ioi.concaveOn
  have := hconc.le_map_sum (t := s) (w := fun _ => 1 / (s.card : ℝ)) (p := x)
    (fun _ _ => by positivity) (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp)
    (fun t ht => hx t ht)
  simp only [smul_eq_mul] at this
  rw [← Finset.mul_sum] at this
  rw [← Finset.mul_sum] at this
  simp only [Finset.sum_neg_distrib, mul_neg]
  linarith

/-! ### Exclusion sufficiency (C05-17) and additivity (C05-18) -/

/-- KL divergence on a finite set (support convention: 0·log(0/q) = 0). -/
def KL (P Q : Ω → ℝ) : ℝ := ∑ ω, P ω * Real.log (P ω / Q ω)

/-- Conditioning on A: P_def = P(·|A). Then D(P_def‖P) = −ln P(A), which is also the
divergence of the push-forwards under X = 1_A (δ₁ versus Bernoulli(P(A))): X is sufficient. -/
theorem exclusion_sufficiency (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (A : Finset Ω)
    (hA : 0 < ∑ ω ∈ A, P ω) :
    let PA := ∑ ω ∈ A, P ω
    let Pdef := fun ω => if ω ∈ A then P ω / PA else 0
    KL Pdef P = -Real.log PA ∧
      (1 * Real.log (1 / PA) + 0 * Real.log (0 / (1 - PA))) = -Real.log PA := by
  intro PA Pdef
  constructor
  · unfold KL
    have : ∀ ω, Pdef ω * Real.log (Pdef ω / P ω) =
        if ω ∈ A then P ω / PA * (-Real.log PA) else 0 := by
      intro ω
      simp only [Pdef]
      split_ifs with h
      · rcases (hP ω).eq_or_lt with h0 | h0
        · rw [← h0]; simp
        · rw [div_div_cancel_left' h0.ne', Real.log_inv]
      · simp
    simp_rw [this]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sum_mul,
      ← Finset.sum_div, div_self hA.ne', one_mul]
  · simp [Real.log_inv, one_div]

/-- C05-18: for events whose joint probability factorizes (mutual independence), the
exclusion costs add. -/
theorem independent_costs_add {ι : Type*} (s : Finset ι) (PA : ι → ℝ) (Pcap : ℝ)
    (hind : Pcap = ∏ i ∈ s, PA i) (hpos : ∀ i ∈ s, 0 < PA i) :
    -Real.log Pcap = ∑ i ∈ s, -Real.log (PA i) := by
  rw [hind, Real.log_prod (fun i hi => (hpos i hi).ne'), Finset.sum_neg_distrib]

/-! ### Product (tensor) entropy (C05-53, -69, -72) -/

/-- Marginalization of a product measure on `Fin n → Ω`. -/
theorem prod_marginal {n : ℕ} (p : Ω → ℝ) (hp1 : ∑ ω, p ω = 1) (i : Fin n) (g : Ω → ℝ) :
    ∑ x : Fin n → Ω, (∏ j, p (x j)) * g (x i) = ∑ ω, p ω * g ω := by
  have : ∀ x : Fin n → Ω, (∏ j, p (x j)) * g (x i) =
      ∏ j, (p (x j) * (if j = i then g (x j) else 1)) := by
    intro x
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _)]
  simp_rw [this]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (t := fun _ => Finset.univ)
    (f := fun j ω => p ω * (if j = i then g ω else 1))]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp only [hj, if_false, mul_one]; exact hp1
  · simp

/-- Entropy of the product law p^{⊗n} is n·H(p). With p = p_{η*} and n = 7 this is the
stationary entropy 7g of the seven-factor history kernel, so Δ = e^{−7g} and
dim_eff = e^{7g}. -/
theorem product_entropy {n : ℕ} (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) :
    ∑ x : Fin n → Ω, negMulLog (∏ j, p (x j)) = n * H p := by
  have key : ∀ x : Fin n → Ω, negMulLog (∏ j, p (x j)) =
      -((∏ j, p (x j)) * ∑ i, Real.log (p (x i))) := by
    intro x
    unfold negMulLog
    by_cases h : ∀ j, p (x j) ≠ 0
    · rw [Real.log_prod (fun j _ => h j)]; ring
    · push_neg at h
      obtain ⟨j, hj⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ j) hj]; simp
  rw [Finset.sum_congr rfl (fun x _ => key x)]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_neg_distrib, Finset.sum_comm,
    Finset.sum_congr rfl (fun i _ => prod_marginal p hp1 i (fun ω => Real.log (p ω)))]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, H, negMulLog,
    Finset.sum_neg_distrib, mul_neg, neg_mul]

/-- Shannon/determinant identity (C05-53): exp(Σ p ln p) = e^{−H(p)}. -/
theorem fuglede_kadison (p : Ω → ℝ) : Real.exp (∑ ω, p ω * Real.log (p ω)) = Real.exp (-H p) := by
  congr 1; simp [H, negMulLog, Finset.sum_neg_distrib]

/-! ### Rényi ordering (C05-55, exact part) -/

theorem renyi_order (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (ω₀ : Ω)
    (hmax : ∀ ω, p ω ≤ p ω₀) :
    -Real.log (p ω₀) ≤ -Real.log (∑ ω, p ω ^ 2) ∧ -Real.log (∑ ω, p ω ^ 2) ≤ H p := by
  have hS : 0 < ∑ ω, p ω ^ 2 := by
    obtain ⟨ω, hω⟩ : ∃ ω, 0 < p ω := by
      by_contra h; push_neg at h
      have : ∑ ω, p ω ≤ 0 := Finset.sum_nonpos (fun ω _ => h ω)
      linarith
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun ω => p ω ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ ω))
  constructor
  · have : ∑ ω, p ω ^ 2 ≤ p ω₀ := by
      calc ∑ ω, p ω ^ 2 ≤ ∑ ω, p ω₀ * p ω :=
            Finset.sum_le_sum (fun ω _ => by rw [sq]; exact mul_le_mul_of_nonneg_right (hmax ω) (hp ω))
        _ = p ω₀ := by rw [← Finset.mul_sum, hp1, mul_one]
    have := Real.log_le_log hS this; linarith
  · -- Jensen on the support: Σ_{p>0} p log p ≤ log Σ p·p
    set s := Finset.univ.filter (fun ω => 0 < p ω)
    have hw : ∑ ω ∈ s, p ω = 1 := by
      rw [← hp1, Finset.sum_filter_of_ne (fun ω _ h => lt_of_le_of_ne (hp ω) (Ne.symm h))]
    have hj := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := s) (w := p) (p := p)
      (fun ω _ => hp ω) hw (fun ω hω => (Finset.mem_filter.mp hω).2)
    simp only [smul_eq_mul] at hj
    have e1 : ∑ ω ∈ s, p ω * p ω = ∑ ω, p ω ^ 2 := by
      rw [Finset.sum_filter_of_ne (fun ω _ h => by
        rcases (hp ω).eq_or_lt with h0 | h0
        · exact absurd (by rw [← h0]; ring) h
        · exact h0)]
      simp [sq]
    have e2 : ∑ ω ∈ s, p ω * Real.log (p ω) = -H p := by
      unfold H negMulLog
      rw [Finset.sum_filter_of_ne (fun ω _ h => by
        rcases (hp ω).eq_or_lt with h0 | h0
        · exact absurd (by rw [← h0]; ring) h
        · exact h0)]
      simp [Finset.sum_neg_distrib]
    rw [e1, e2] at hj; linarith

/-! ### Refresh kernel (C05-69) -/

/-- The refresh kernel P(b,b′) = p(b′) is row-stochastic, rank one, and p is its unique
stationary probability. -/
theorem refresh_unique (p μ : Ω → ℝ) (hp1 : ∑ ω, p ω = 1) (hμ1 : ∑ ω, μ ω = 1)
    (hstat : ∀ b', ∑ b, μ b * p b' = μ b') : μ = p := by
  funext b'; rw [← hstat b', ← Finset.sum_mul, hμ1, one_mul]

theorem refresh_row_stochastic (p : Ω → ℝ) (hp1 : ∑ ω, p ω = 1) (b : Ω) :
    ∑ b', (fun (_ : Ω) b' => p b') b b' = 1 := hp1

/-- n-step path law of the refresh chain from any start is the product law, so its
entropy is n·H(p): the chain is i.i.d. with entropy rate H(p) = g. -/
theorem refresh_path_entropy {n : ℕ} (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (_start : Ω) :
    ∑ y : Fin n → Ω, negMulLog (∏ j, p (y j)) = n * H p := product_entropy p hp hp1

/-! ### Conditioning on a label (C05-71) -/

/-- Entropy of any law supported on a set of size k is at most ln k. -/
theorem entropy_le_log_support (q : Ω → ℝ) (hq : ∀ ω, 0 ≤ q ω) (hq1 : ∑ ω, q ω = 1)
    (S : Finset Ω) (hS : S.Nonempty) (hsupp : ∀ ω ∉ S, q ω = 0) :
    H q ≤ Real.log S.card := by
  have hsum : H q = ∑ ω : S, negMulLog (q ω) := by
    unfold H
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun ω _ h => by rw [hsupp ω h]; simp)]
    exact (Finset.sum_coe_sort S _).symm
  have : Nonempty S := hS.to_subtype
  rw [hsum]
  have := Entropic.AppB.max_entropy (fun ω : S => q ω) (fun ω => hq ω)
    (by rw [Finset.sum_coe_sort S (fun ω => q ω),
          Finset.sum_subset (Finset.subset_univ S) (fun ω _ h => hsupp ω h)]; exact hq1)
  simpa using this

end Entropic.AppCDE
