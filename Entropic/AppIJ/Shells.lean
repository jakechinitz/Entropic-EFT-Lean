import Entropic.ShellLadder
import Entropic.AppH1.Marked
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! Appendix I: shells, Fisher information, return times, singlet overlaps and the q^{N²} ladder
(ledger C10-01, -03 … -05, -07 … -10, -13, -15, -16, -18 … -20). -/

noncomputable section
namespace Entropic.AppIJ
open Real

/-- C10-01: an injection Fin 4 ↪ A exists iff |A| ≥ 4; with |A| = 7 − N this is N ≤ 3. -/
theorem shells_injective (A : Type*) [Fintype A] :
    Nonempty (Fin 4 ↪ A) ↔ 4 ≤ Fintype.card A := by
  rw [Function.Embedding.nonempty_iff_card_le, Fintype.card_fin]

theorem shells_count (N : ℕ) (hN : N ≤ 7) : 4 ≤ 7 - N ↔ N ≤ 3 := by omega

/-- C10-03: a function taking two distinct values on the support of a full-support law has
positive variance. -/
theorem variance_pos {ι : Type*} [Fintype ι] (p K : ι → ℝ) (hp : ∀ b, 0 < p b) (h1 : ∑ b, p b = 1)
    {b1 b2 : ι} (hK : K b1 ≠ K b2) : 0 < ∑ b, p b * (K b - ∑ c, p c * K c) ^ 2 := by
  set μ := ∑ c, p c * K c
  have hnn : ∀ b, 0 ≤ p b * (K b - μ) ^ 2 := fun b => mul_nonneg (hp b).le (sq_nonneg _)
  by_contra hle; push Not at hle
  have h0 : ∑ b, p b * (K b - μ) ^ 2 = 0 := le_antisymm hle (Finset.sum_nonneg (fun b _ => hnn b))
  have hz := fun b => (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hnn b)).mp h0 b (Finset.mem_univ _)
  have e : ∀ b, K b = μ := fun b => by
    have := hz b
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (hp b).ne'
    · exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)
  exact hK ((e b1).trans (e b2).symm)

/-- C10-04: for any finite nonempty family of positive values K_b, the closure equation
η⟨K⟩_η = 3/2 has a solution η > 0 (here ⟨K⟩_η is the Gibbs mean with weight e^{−ηK}). -/
theorem closure_solvable {ι : Type*} [Fintype ι] [Nonempty ι] (K : ι → ℝ) (hK : ∀ b, 0 < K b) :
    ∃ η > 0, η * ((∑ b, K b * Real.exp (-η * K b)) / ∑ b, Real.exp (-η * K b)) = 3 / 2 := by
  set f : ℝ → ℝ := fun η => η * ((∑ b, K b * Real.exp (-η * K b)) / ∑ b, Real.exp (-η * K b))
  have hZ : ∀ η, 0 < ∑ b, Real.exp (-η * K b) := fun η =>
    Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  have hcont : Continuous f := by
    apply Continuous.mul continuous_id
    apply Continuous.div (by fun_prop) (by fun_prop) (fun η => (hZ η).ne')
  obtain ⟨b0, -, hb0⟩ := Finset.exists_min_image Finset.univ K Finset.univ_nonempty
  set kmin := K b0
  have hkmin : 0 < kmin := hK b0
  have hmean : ∀ η, kmin ≤ (∑ b, K b * Real.exp (-η * K b)) / ∑ b, Real.exp (-η * K b) := by
    intro η
    rw [le_div_iff₀ (hZ η), Finset.mul_sum]
    exact Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_right (hb0 b (Finset.mem_univ _))
      (Real.exp_pos _).le)
  set η1 := 3 / (2 * kmin) + 1
  have hη1 : 0 < η1 := by positivity
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : 3 / 2 ≤ f η1 := by
    have := mul_le_mul_of_nonneg_left (hmean η1) hη1.le
    calc (3:ℝ) / 2 ≤ η1 * kmin := by
          simp only [η1]; rw [add_mul, show 3 / (2 * kmin) * kmin = 3 / 2 by field_simp]
          nlinarith
      _ ≤ f η1 := this
  obtain ⟨η, hη, hfη⟩ := intermediate_value_Icc (le_of_lt hη1) hcont.continuousOn ⟨by rw [hf0]; norm_num, hf1⟩
  refine ⟨η, ?_, hfη⟩
  rcases eq_or_lt_of_le hη.1 with h | h
  · subst h; rw [hf0] at hfη; norm_num at hfη
  · exact h

/-- C10-05: for p_η(b) = e^{−ηK(b)}/Z(η), d/dη ln p_η(b) = −(K(b) − ⟨K⟩_η), so the Fisher information
Σ p (∂ ln p)² equals Var(K) = ⟨s, s⟩ with s_b = √p_b (K(b) − ⟨K⟩). -/
theorem fisher_score {ι : Type*} [Fintype ι] [Nonempty ι] (K : ι → ℝ) (η : ℝ) (b : ι) :
    HasDerivAt (fun x => -x * K b - Real.log (∑ c, Real.exp (-x * K c)))
      (-(K b - (∑ c, K c * Real.exp (-η * K c)) / ∑ c, Real.exp (-η * K c))) η := by
  have hZ : 0 < ∑ c, Real.exp (-η * K c) :=
    Finset.sum_pos (fun c _ => Real.exp_pos _) Finset.univ_nonempty
  have hsum : HasDerivAt (fun x => ∑ c, Real.exp (-x * K c)) (∑ c, -(K c * Real.exp (-η * K c))) η := by
    apply HasDerivAt.fun_sum
    intro c _
    have := ((hasDerivAt_id' η).mul_const (-K c)).exp
    convert this using 1
    · funext x; ring_nf
    · ring_nf
  have h1 := ((hasDerivAt_id' η).mul_const (-K b)).sub (hsum.log hZ.ne')
  convert h1 using 1
  · funext x; simp only [Pi.sub_apply]; ring_nf
  · rw [Finset.sum_neg_distrib]; field_simp; ring

theorem fisher_eq_variance {ι : Type*} [Fintype ι] (p K : ι → ℝ) (hp : ∀ b, 0 ≤ p b) (μ : ℝ) :
    ∑ b, p b * (-(K b - μ)) ^ 2 = ∑ b, p b * (K b - μ) ^ 2 ∧
      ∑ b, (Real.sqrt (p b) * (K b - μ)) ^ 2 = ∑ b, p b * (K b - μ) ^ 2 := by
  constructor
  · exact Finset.sum_congr rfl (fun b _ => by ring)
  · exact Finset.sum_congr rfl (fun b _ => by rw [mul_pow, Real.sq_sqrt (hp b)])

/-- C10-07: 2·P(6,4) = 720 = 6!. -/
theorem first_shell_count : 2 * (6 * 5 * 4 * 3) = 720 ∧ Nat.factorial 6 = 720 ∧
    2 * (Nat.factorial 6 / Nat.factorial 2) = 720 := by decide

/-- C10-08: P(T = t) = p(1−p)^{t−1} sums to 1 and has mean 1/p (0 < p ≤ 1). -/
theorem geometric_return {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    HasSum (fun t : ℕ => p * (1 - p) ^ t) 1 ∧ HasSum (fun t : ℕ => ((t : ℝ) + 1) * (p * (1 - p) ^ t)) (1 / p) := by
  have h0 : 0 ≤ 1 - p := by linarith
  have h1 : 1 - p < 1 := by linarith
  have hg := hasSum_geometric_of_lt_one h0 h1
  constructor
  · convert hg.mul_left p using 1; field_simp; ring
  · have hn : ‖(1 - p : ℝ)‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
    have h2 := hasSum_coe_mul_geometric_of_norm_lt_one hn
    have := (h2.add hg).mul_left p
    convert this using 1
    · funext t; ring
    · field_simp; ring

/-- C10-09: Σ_b p_b·(1/p_b) = Ω for any full-support law on Ω states. -/
theorem kac_mean {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ b, 0 < p b) :
    ∑ b, p b * (1 / p b) = Fintype.card ι := by
  rw [Finset.sum_congr rfl (fun b _ => by rw [mul_one_div_cancel (hp b).ne']), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]

/-- C10-10: exp(Σ p ln(1/p)) = exp H(p) ≤ Ω, with equality iff p is uniform. -/
theorem entropy_le_log_card {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → ℝ) (hp : ∀ b, 0 < p b)
    (h1 : ∑ b, p b = 1) :
    -∑ b, p b * Real.log (p b) ≤ Real.log (Fintype.card ι) ∧
      (-∑ b, p b * Real.log (p b) = Real.log (Fintype.card ι) ↔ ∀ b, p b = 1 / Fintype.card ι) := by
  have hc : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set u : ι → ℝ := fun _ => 1 / Fintype.card ι
  have hu : ∀ b, 0 < u b := fun b => by positivity
  have hD := Entropic.AppH1.gibbs p u (fun b => (hp b).le) hu h1 (by
    simp only [u, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
  have key : ∑ b, p b * Real.log (p b / u b) = Real.log (Fintype.card ι) - (-∑ b, p b * Real.log (p b)) := by
    simp only [u]
    rw [Finset.sum_congr rfl (fun b _ => by
      rw [Real.log_div (hp b).ne' (by positivity), one_div, Real.log_inv, sub_neg_eq_add, mul_add])]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, h1, one_mul]; ring
  rw [key] at hD
  refine ⟨by linarith [hD.1], ⟨fun heq => ?_, fun hall => ?_⟩⟩
  · have := hD.2 (by linarith); intro b; exact congrFun this b
  · rw [Finset.sum_congr rfl (fun b _ => by rw [hall b]), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      one_div, Real.log_inv]
    field_simp

/-! ### Singlet projector and ordered incidences (C10-13, C10-15) -/

/-- C10-13: Q = I − uu* with u = 7^{−1/2}Σe_m has ⟨e_a, Q e_b⟩ = δ_ab − 1/7 and ‖Qe_a‖² = 6/7. -/
theorem singlet_complement (a b : Fin 7) :
    ((if a = b then (1:ℝ) else 0) - 1 / 7) = (if a = b then 1 else 0) - (1 / Real.sqrt 7) * (1 / Real.sqrt 7) ∧
      ∑ c : Fin 7, ((if c = a then (1:ℝ) else 0) - 1/7) ^ 2 = 6 / 7 := by
  constructor
  · rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]
  · rw [Fin.sum_univ_seven]; fin_cases a <;> simp <;> norm_num

/-- C10-15: N² = N + 2·C(N,2); Σ_{r,s} ln(2/7) = N² ln(2/7); Π_{r,s}(2/7) = (2/7)^{N²}. -/
theorem ordered_incidence (N : ℕ) :
    N ^ 2 = N + 2 * Nat.choose N 2 ∧
      ∑ _r : Fin N, ∑ _s : Fin N, Real.log (2/7) = (N:ℝ) ^ 2 * Real.log (2/7) ∧
      ∏ _r : Fin N, ∏ _s : Fin N, ((2:ℝ)/7) = (2/7) ^ (N ^ 2) := by
  refine ⟨?_, by simp [Finset.sum_const]; ring, ?_⟩
  · induction N with
    | zero => simp
    | succ n ih => rw [Nat.choose_succ_succ, Nat.choose_one_right]; nlinarith [ih]
  · rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, sq]

/-! ### ln(2/7) and the ladder (C10-16, C10-19, C10-20) -/

theorem log_seven_bounds : 1.945910 < Real.log 7 ∧ Real.log 7 < 1.945911 := by
  -- log 7 = 3 log 2 + log(1 − 1/8)
  have h87 : Real.log 7 = 3 * Real.log 2 + Real.log (1 - 1/8) := by
    rw [show (1:ℝ) - 1/8 = 7 / 2 ^ 3 by norm_num, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  have hs := Real.abs_log_sub_add_sum_range_le (show |(1/8 : ℝ)| < 1 by norm_num) 9
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs h87
  have l1 := Real.log_two_gt_d9; have l2 := Real.log_two_lt_d9
  rw [abs_le] at hs
  constructor <;> nlinarith [hs.1, hs.2]

/-- C10-16: A₀ = ln(2/7) = −1.25276…. -/
theorem A0_value : -1.252764 < Real.log (2/7) ∧ Real.log (2/7) < -1.252762 := by
  rw [Real.log_div (by norm_num) (by norm_num)]
  have l1 := Real.log_two_gt_d9; have l2 := Real.log_two_lt_d9
  obtain ⟨a, b⟩ := log_seven_bounds
  constructor <;> linarith

/-- C10-19: f(N) = 720^N (2/7)^{N²} has ln(f(N)/f(N−1)) = ln 720 + (2N−1) ln(2/7), and Σ_{k≤N}(2k−1) = N². -/
theorem ladder_recurrence (N : ℕ) (hN : 1 ≤ N) :
    Real.log ((720:ℝ) ^ N * (2/7) ^ (N ^ 2) / ((720:ℝ) ^ (N - 1) * (2/7) ^ ((N - 1) ^ 2))) =
      Real.log 720 + (2 * N - 1 : ℝ) * Real.log (2/7) ∧
      ∑ k ∈ Finset.Icc 1 N, (2 * k - 1) = N ^ 2 := by
  constructor
  · rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; push_cast; ring
  · induction N with
    | zero => omega
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; decide
      · rw [Finset.sum_Icc_succ_top (by omega), ih hpos]
        rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]; ring

/-- C10-20: g(N) = B₀N + A₀N² has second difference 2A₀; 2 ln(2/7) = −2.50553…. -/
theorem second_difference (A B : ℝ) (N : ℝ) :
    (B * (N + 1) + A * (N + 1) ^ 2) - 2 * (B * N + A * N ^ 2) + (B * (N - 1) + A * (N - 1) ^ 2) = 2 * A ∧
      (-2.505528 < 2 * Real.log (2/7) ∧ 2 * Real.log (2/7) < -2.505524) := by
  refine ⟨by ring, ?_⟩
  obtain ⟨a, b⟩ := A0_value
  constructor <;> linarith

/-! ### Gaussian characteristic function (C10-18) -/

/-- C10-18: for X ~ N(0, v), E[e^{iNX}] = e^{−N²v/2} = q^{N²} when v = −2 ln q; with variance Nv
(the law of a sum of N independent copies), E[e^{iX}] = q^N. -/
theorem gaussian_ladder {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (N : ℕ) :
    let v : NNReal := ⟨-2 * Real.log q, by nlinarith [Real.log_neg hq0 hq1]⟩
    MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 v) N = ((q ^ (N ^ 2) : ℝ) : ℂ) ∧
      MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 (N * v)) 1 = ((q ^ N : ℝ) : ℂ) := by
  intro v
  have hv : (v : ℝ) = -2 * Real.log q := rfl
  rw [ProbabilityTheory.charFun_gaussianReal, ProbabilityTheory.charFun_gaussianReal]
  constructor
  · rw [show ((q ^ (N ^ 2) : ℝ) : ℂ) = Complex.exp (((N ^ 2 : ℕ) : ℂ) * Real.log q) by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Real.rpow_natCast,
        Real.rpow_def_of_pos hq0, mul_comm]]
    congr 1; push_cast [hv]; ring
  · rw [show ((q ^ N : ℝ) : ℂ) = Complex.exp ((N : ℂ) * Real.log q) by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Real.rpow_natCast,
        Real.rpow_def_of_pos hq0, mul_comm]]
    congr 1; push_cast [NNReal.coe_mul, NNReal.coe_natCast, hv]; ring

end Entropic.AppIJ
