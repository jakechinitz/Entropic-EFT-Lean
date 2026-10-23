import Entropic.AppP.Records
import Entropic.AppP.Numbers
import Entropic.AppIJ.Shells
import Entropic.ClosureRoot
import Entropic.Spine
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-! Main text Parts I–III remainder (ledger C01): shell-integer ratios (C01-03), the Farey count (C01-05a),
the abundance relation (C01-14), SU(2) fusion dimensions (C01-21), marked carrier orthonormality
(C01-23), the closure evidence derivative and the maximum-entropy property (C01-24), ln 1680 and the
sharing-entropy ceiling (C01-27), time dilation (C01-31a), decoherent-history normalization (C01-32),
the dilation coherence factor (C01-34), the Schwarzschild radial scalar (C01-52), the Gaussian
representation of the closure amplitude (C01-56) and the one-bit horizon area (C01-60). -/

noncomputable section
namespace Entropic.Main.Core
open Real Matrix

/-- C01-03: 720·(2/7) = 1440/7 ∈ (205.71, 205.72) and 720²(2/7)⁴ = 8294400/2401 ∈ (3454.5, 3454.6); they lie
0.51% below m_μ/m_e = 206.7682827 and 0.65% below m_τ/m_e = 3477.23. -/
theorem shell_ratios :
    (720:ℝ) * (2/7) = 1440/7 ∧ 205.71 < (1440:ℝ)/7 ∧ (1440:ℝ)/7 < 205.72 ∧
      (720:ℝ) ^ 2 * (2/7) ^ 4 = 8294400/2401 ∧ 3454.5 < (8294400:ℝ)/2401 ∧ (8294400:ℝ)/2401 < 3454.6 ∧
      0.0050 < 1 - (1440:ℝ)/7 / 206.7682827 ∧ 1 - (1440:ℝ)/7 / 206.7682827 < 0.0052 ∧
      0.0064 < 1 - (8294400:ℝ)/2401 / 3477.23 ∧ 1 - (8294400:ℝ)/2401 / 3477.23 < 0.0066 := by
  norm_num

/-- C01-05 (a): the distinct rationals p/q ∈ [0,1] with 1 ≤ q ≤ 11 number 43. -/
theorem farey_count :
    (((Finset.range 12).filter (1 ≤ ·)).biUnion
      (fun q : ℕ => (Finset.range (q + 1)).image (fun p : ℕ => ((p : ℚ) / (q : ℚ))))).card = 43 := by decide +kernel

/-- C01-14: 1/ε = 4π²/g ∈ (5.319, 5.322) at the closure root, and a₀(Ω_c/Ω_b) = cH₀ when
a₀ = εcH₀, Ω_c/Ω_b = 1/ε. -/
theorem abundance {η : ℝ} (h : Entropic.FiniteModel.ClosureStationary η) :
    5.319 < 4 * π ^ 2 / Entropic.ClosureRoot.gshare η ∧ 4 * π ^ 2 / Entropic.ClosureRoot.gshare η < 5.322 ∧
      ∀ ε c H : ℝ, ε ≠ 0 → ε * c * H * (1 / ε) = c * H := by
  obtain ⟨e1, e2⟩ := Entropic.Spine.epsilon_bracket h
  have hg : 0 < Entropic.ClosureRoot.gshare η := by
    have := (Entropic.ClosureRoot.gshare_bracket h).1; unfold Entropic.ClosureRoot.gLo at this; linarith
  have hp : 0 < 4 * π ^ 2 := by positivity
  have r : 4 * π ^ 2 / Entropic.ClosureRoot.gshare η = 1 / (Entropic.ClosureRoot.gshare η / (4 * π ^ 2)) := by
    field_simp
  refine ⟨?_, ?_, fun ε c H he => by field_simp⟩
  · rw [r, lt_div_iff₀ (by linarith)]; nlinarith
  · rw [r, div_lt_iff₀ (by linarith)]; nlinarith

/-- C01-21 (dimensions, n = 2j): (n+1)² = Σ_{J=0}^{n}(2J+1); |M| = dim V_{2j} = 2n+1 = 4j+1; and
dim Q(j) = (n+1)² − (2n+1) = n² = 4j². -/
theorem fusion_dimensions (n : ℕ) :
    (n + 1) ^ 2 = ∑ J ∈ Finset.range (n + 1), (2 * J + 1) ∧ (n + 1) ^ 2 - (2 * n + 1) = n ^ 2 := by
  constructor
  · induction n with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ← ih]; ring
  · have : (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) := by ring
    omega

/-- C01-23: dim H_mark = 3·3 = 1 + 3 + 5 = 9, and products of two orthonormal triples are orthonormal. -/
theorem marked_carrier (a b : Fin 3 → Fin 3 → ℝ) (ha : ∀ i k, a i ⬝ᵥ a k = if i = k then 1 else 0)
    (hb : ∀ j l, b j ⬝ᵥ b l = if j = l then 1 else 0) (i j k l : Fin 3) :
    3 * 3 = 1 + 3 + 5 ∧
      (∑ p : Fin 3 × Fin 3, (a i p.1 * b j p.2) * (a k p.1 * b l p.2)) =
        (if i = k then 1 else 0) * (if j = l then 1 else 0) := by
  refine ⟨rfl, ?_⟩
  rw [Fintype.sum_prod_type, ← ha i k, ← hb j l, dotProduct, dotProduct, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))

/-- C01-24: 𝓕(η) = ln Z(η) + (3/2) ln η has 𝓕′(η) = −⟨K²⟩_η + 3/(2η). -/
theorem evidence_derivative {η : ℝ} (he : 0 < η) :
    HasDerivAt Entropic.ClosureRoot.evidence (-Entropic.FiniteModel.meanK2 η + 3 / (2 * η)) η := by
  have h := Entropic.ClosureRoot.evidence_hasDerivAt he
  convert h using 1
  rw [Entropic.ClosureRoot.meanK2_eq]
  have hZ := Entropic.ClosureRoot.Z_pos η
  unfold Entropic.ClosureRoot.N Entropic.ClosureRoot.S1 Entropic.ClosureRoot.Z at *
  have e : ∀ L : List (ℝ × ℝ), (L.map fun p => p.2 * (Real.exp (-η * p.1) * (η * p.1 - 3/2))).sum =
      η * (L.map fun p => p.2 * p.1 * Real.exp (-η * p.1)).sum - 3/2 * (L.map fun p => p.2 * Real.exp (-η * p.1)).sum := by
    intro L; induction L with
    | nil => simp
    | cons p L ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [e]
  set S := (Entropic.ClosureRoot.specR.map fun p => p.2 * p.1 * Real.exp (-η * p.1)).sum
  set Zv := (Entropic.ClosureRoot.specR.map fun p => p.2 * Real.exp (-η * p.1)).sum
  field_simp; ring

/-- C01-24 (maximum entropy): for a Gibbs law P = e^{−ηK}/Z and any law Q with the same mean of K,
H(Q) ≤ H(P). -/
theorem gibbs_max_entropy {B : Type*} [Fintype B] [DecidableEq B] [Nonempty B] (K : B → ℝ) (η : ℝ)
    (Q : B → ℝ) (hQ : ∑ b, Q b = 1) (hQ0 : ∀ b, 0 ≤ Q b)
    (hmean : ∑ b, Q b * K b = ∑ b, Real.exp (-η * K b) / (∑ c, Real.exp (-η * K c)) * K b) :
    ∑ b, negMulLog (Q b) ≤ ∑ b, negMulLog (Real.exp (-η * K b) / (∑ c, Real.exp (-η * K c))) := by
  have hdec := Entropic.AppP.entropy_decomposition K η Q hQ hQ0
  simp only at hdec
  set Z := ∑ c, Real.exp (-η * K c)
  have hZ : 0 < Z := Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  have hKL : 0 ≤ Entropic.AppP.KL Q (fun b => Real.exp (-η * K b) / Z) := by
    have L := Entropic.AppP.log_sum Finset.univ Q (fun b => Real.exp (-η * K b) / Z) (fun b _ => hQ0 b)
      (fun b _ => div_pos (Real.exp_pos _) hZ) Finset.univ_nonempty
    have h1 : ∑ b, Real.exp (-η * K b) / Z = 1 := by rw [← Finset.sum_div]; exact div_self hZ.ne'
    rw [hQ, h1, div_one, Real.log_one, mul_zero] at L
    exact L
  rw [hmean] at hdec
  linarith

/-- C01-27: ln 1680 = 4 ln 2 + ln 3 + ln 5 + ln 7 ∈ (7.426549067, 7.426549078), and g_share,eff < ln 1680. -/
theorem sharing_ceiling {η : ℝ} (h : Entropic.FiniteModel.ClosureStationary η) :
    7.426549067 < Real.log 1680 ∧ Real.log 1680 < 7.426549078 ∧ Entropic.ClosureRoot.gshare η < Real.log 1680 := by
  have e : Real.log 1680 = 4 * Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 := by
    rw [show (1680:ℝ) = 2 ^ 4 * 3 * 5 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  have h87 : Real.log 7 = 3 * Real.log 2 + Real.log (1 - 1/8) := by
    rw [show (1:ℝ) - 1/8 = 7 / 2 ^ 3 by norm_num, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  have hs := Real.abs_log_sub_add_sum_range_le (show |(1/8 : ℝ)| < 1 by norm_num) 12
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs
  rw [abs_le] at hs
  have l1 := Real.log_two_gt_d9; have l2 := Real.log_two_lt_d9
  have l3 := Real.log_three_gt_d9; have l4 := Real.log_three_lt_d9
  have l5 := Real.log_five_gt_d9; have l6 := Real.log_five_lt_d9
  have g2 := (Entropic.ClosureRoot.gshare_bracket h).2; unfold Entropic.ClosureRoot.gHi at g2
  rw [e, h87]
  refine ⟨by nlinarith [hs.1, hs.2], by nlinarith [hs.1, hs.2], by nlinarith [hs.1, hs.2]⟩

/-- C01-31 (a): c²dτ² = c²dt² − v²dt² with dτ, dt > 0 and |v| < c gives dτ/dt = √(1 − v²/c²). -/
theorem time_dilation {c v dt dτ : ℝ} (hc : 0 < c) (hv : v ^ 2 < c ^ 2) (hdt : 0 < dt) (hdτ : 0 < dτ)
    (h : c ^ 2 * dτ ^ 2 = c ^ 2 * dt ^ 2 - v ^ 2 * dt ^ 2) : dτ / dt = Real.sqrt (1 - v ^ 2 / c ^ 2) := by
  have hc2 : 0 < c ^ 2 := by positivity
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
  field_simp
  nlinarith [h]

/-- C01-32: if Σ_h C_h = W with W†W = I and Tr ρ = 1, then Σ_{h,h'} Tr(C_hρC_{h'}†) = 1; when the
off-diagonal decoherence functional vanishes, the diagonal probabilities sum to 1. -/
theorem decoherent_histories {H n : Type*} [Fintype H] [DecidableEq H] [Fintype n] [DecidableEq n]
    (C : H → Matrix n n ℂ) (W : Matrix n n ℂ) (hW : Wᴴ * W = 1) (hsum : ∑ h, C h = W) (ρ : Matrix n n ℂ)
    (hρ : ρ.trace = 1) (hdec : ∀ h h', h ≠ h' → (C h * ρ * (C h')ᴴ).trace = 0) :
    ∑ h, (C h * ρ * (C h)ᴴ).trace = 1 := by
  have htot : ∑ h, ∑ h', (C h * ρ * (C h')ᴴ).trace = 1 := by
    have : ∑ h, ∑ h', C h * ρ * (C h')ᴴ = W * ρ * Wᴴ := by
      rw [← hsum, Matrix.conjTranspose_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun h _ => ?_)
      rw [Matrix.mul_sum]
    rw [show (∑ h, ∑ h', (C h * ρ * (C h')ᴴ).trace) = (∑ h, ∑ h', C h * ρ * (C h')ᴴ).trace by
      simp [Matrix.trace_sum]]
    rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hW, Matrix.one_mul, hρ]
  rw [← htot]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [Finset.sum_eq_single h (fun h' _ hne => hdec h h' (Ne.symm hne)) (by simp)]

/-- C01-34: tracing the record after |x⟩|e₀⟩ ↦ |x⟩|e_x⟩ multiplies ρ_xy by ⟨e_y|e_x⟩. -/
theorem dilation_coherence {X E : Type*} [Fintype E] (ρ : X → X → ℂ) (e : X → E → ℂ) (x y : X) :
    ∑ k, ρ x y * e x k * star (e y k) = ρ x y * ∑ k, star (e y k) * e x k := by
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)

/-- C01-52: for h_RR = (1 − 2GM/(c²R))⁻¹ the scalar h^{RR}(∂_R R)² = 1 − 2GM/(c²R) = N² = −g_tt. -/
theorem schwarzschild_scalar {G M c R : ℝ} (h : 1 - 2 * G * M / (c ^ 2 * R) ≠ 0) :
    (1 / (1 - 2 * G * M / (c ^ 2 * R)))⁻¹ * 1 ^ 2 = 1 - 2 * G * M / (c ^ 2 * R) := by
  rw [one_div, inv_inv, one_pow, mul_one]

/-- C01-56 (one dimension): ∫ (2π)^{−1/2} e^{−x²/2} e^{isx} dx = e^{−s²/2}. -/
theorem gaussian_representation_1d (s : ℝ) :
    ∫ x : ℝ, ((2 * π) ^ (-(1:ℝ)/2) : ℝ) * (Complex.exp (Complex.I * s * x) * Complex.exp (-(1/2 : ℂ) * x ^ 2)) =
      Complex.exp (-(s : ℂ) ^ 2 / 2) := by
  rw [MeasureTheory.integral_const_mul, fourierIntegral_gaussian (by norm_num : (0:ℝ) < (1/2 : ℂ).re) (s : ℂ)]
  have h1 : ((π : ℂ) / (1/2)) ^ (1/2 : ℂ) = (((2 * π) ^ ((1:ℝ)/2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]; push_cast; ring_nf
  rw [h1, show -(s : ℂ) ^ 2 / (4 * (1/2)) = -(s:ℂ) ^ 2 / 2 by ring, ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.rpow_add (by positivity)]
  norm_num

/-- C01-60: S = A/(4L_P²) = ln 2 ⇔ A = 4 ln 2 L_P². -/
theorem one_bit_area {A L : ℝ} (hL : L ≠ 0) : A / (4 * L ^ 2) = Real.log 2 ↔ A = 4 * Real.log 2 * L ^ 2 := by
  constructor <;> intro h
  · field_simp at h; linarith
  · rw [h]; field_simp

end Entropic.Main.Core
