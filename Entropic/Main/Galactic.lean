import Entropic.GalacticLaw
import Entropic.Spine
import Entropic.AppO.Numerics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! Main text Part IV (Sections 14–19, ledger C02): carrier projectors, the Bose cell, the auxiliary
function Q and its derivative, nematic invariance, the director density in an adapted frame, lensing
and deep profiles, the cap radius, the response coefficients at the Sun, cell-count fluctuations,
telegrapher transport, cluster caps and the release/vacuum exchange identity. -/

noncomputable section
namespace Entropic.Main.Galactic
open Real Filter Topology

/-! ### C02-01, C02-02: selector projectors -/

section Selector
variable {A ι : Type*} [Ring A] (E : ι → A →+ A) (B : ι → Set A) (e : ι → A)

/-- Π_P X := E_P(e_P X). -/
def Pi (P : ι) (X : A) : A := E P (e P * X)

/-- C02-01: with E_P(X) ∈ B_P, E_P = id on B_P, E_P(bY) = bE_P(Y) for b ∈ B_P, e_P ∈ B_P idempotent and
e_Pe_Q = 0 (P ≠ Q): Π_P² = Π_P and Π_PΠ_Q = 0. -/
theorem selector_projector (hB : ∀ P X, E P X ∈ B P) (hid : ∀ P b, b ∈ B P → E P b = b)
    (hmod : ∀ P b Y, b ∈ B P → E P (b * Y) = b * E P Y) (he : ∀ P, e P ∈ B P)
    (hidem : ∀ P, e P * e P = e P) (horth : ∀ P Q, P ≠ Q → e P * e Q = 0) (X : A) (P Q : ι) :
    Pi E e P (Pi E e P X) = Pi E e P X ∧ (P ≠ Q → Pi E e P (Pi E e Q X) = 0) := by
  have key : ∀ R, E R (e R * X) = e R * E R (e R * X) := by
    intro R
    conv_lhs => rw [← hidem R, mul_assoc]
    exact hmod R _ _ (he R)
  constructor
  · unfold Pi
    rw [← key P, hid P _ (hB P _)]
  · intro hPQ
    unfold Pi
    rw [key Q, ← mul_assoc, horth P Q hPQ, zero_mul, map_zero]

/-- C02-02: if Σ_{A≺P} e_A = e_P and E_P ∘ E_A = E_P, then Π_P X = E_P(Σ_A Π_A X). -/
theorem nesting (P : ι) (S : Finset ι) (hsum : ∑ a ∈ S, e a = e P) (hfine : ∀ a ∈ S, ∀ Y, E P (E a Y) = E P Y)
    (X : A) : Pi E e P X = E P (∑ a ∈ S, Pi E e a X) := by
  unfold Pi
  rw [← hsum, Finset.sum_mul, map_sum, map_sum]
  exact Finset.sum_congr rfl (fun a ha => (hfine a ha _).symm)
end Selector

/-! ### C02-03 … C02-08 -/

/-- C02-03: the two-phase cell [0,2π]² has Lebesgue measure (2π)². -/
theorem haar_two_phase :
    MeasureTheory.volume (Set.Icc (0:ℝ) (2 * π) ×ˢ Set.Icc (0:ℝ) (2 * π)) = ENNReal.ofReal ((2 * π) ^ 2) := by
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, Real.volume_Icc, sub_zero,
    ← ENNReal.ofReal_mul (by positivity), sq]

/-- C02-05: a₀ = εcH₀ with H₀ = 67.4 km/s/Mpc lies in (1.230, 1.232)·10⁻¹⁰ m/s² at the closure root. -/
theorem a0_value {η : ℝ} (h : Entropic.FiniteModel.ClosureStationary η) :
    1.230e-10 < Entropic.ClosureRoot.gshare η / (4 * π ^ 2) * 299792458 * (67.4e3 / 3.0856775814913673e22) ∧
      Entropic.ClosureRoot.gshare η / (4 * π ^ 2) * 299792458 * (67.4e3 / 3.0856775814913673e22) < 1.232e-10 := by
  obtain ⟨e1, e2⟩ := Entropic.Spine.epsilon_bracket h
  constructor <;> nlinarith

/-- C02-06: a₀ = εcH₀ and Ω_c/Ω_b = 1/ε give a₀Ω_c/Ω_b = cH₀. -/
theorem acceleration_abundance {ε c H : ℝ} (he : ε ≠ 0) : ε * c * H * (1 / ε) = c * H := by field_simp

/-- C02-07: z^{1/4} = √(|∇Φ|/a₀) for z = |∇Φ|²/a₀². -/
theorem x_consistency {g a : ℝ} (hg : 0 ≤ g) (ha : 0 < a) : (g ^ 2 / a ^ 2) ^ ((1:ℝ)/4) = Real.sqrt (g / a) := by
  rw [show g ^ 2 / a ^ 2 = (g / a) ^ 2 by ring, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (div_nonneg hg ha.le)]
  norm_num

/-- n_B(x) = 1/(eˣ − 1). -/
def nB (x : ℝ) : ℝ := 1 / (Real.exp x - 1)

/-- C02-08: Σ_N e^{−xN} = 1/(1 − e^{−x}), so F = −kT ln Σ = kT ln(1 − e^{−x}); and d/dE[kT ln(1 − e^{−E/kT})] = n_B(E/kT). -/
theorem bose_cell {x kT : ℝ} (hx : 0 < x) (hk : 0 < kT) :
    HasSum (fun N : ℕ => Real.exp (-x * N)) (1 / (1 - Real.exp (-x))) ∧
      -kT * Real.log (1 / (1 - Real.exp (-x))) = kT * Real.log (1 - Real.exp (-x)) ∧
      HasDerivAt (fun E => kT * Real.log (1 - Real.exp (-(E / kT)))) (nB (x * kT / kT)) (x * kT) := by
  have he : Real.exp (-x) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hp : 0 < 1 - Real.exp (-x) := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have := hasSum_geometric_of_lt_one (Real.exp_pos (-x)).le he
    convert this using 1
    · funext N; rw [← Real.exp_nat_mul]; ring_nf
    · rw [one_div]
  · rw [one_div, Real.log_inv]; ring
  · have hd : HasDerivAt (fun E => -(E / kT)) (-(1 / kT)) (x * kT) :=
      ((hasDerivAt_id' (x * kT)).div_const kT).neg
    have h1 : HasDerivAt (fun E => 1 - Real.exp (-(E / kT))) (-(Real.exp (-(x * kT / kT)) * -(1 / kT))) (x * kT) :=
      (hd.exp).const_sub 1
    have hx' : x * kT / kT = x := by field_simp
    have h2 := (h1.log (by rw [hx']; exact hp.ne')).const_mul kT
    convert h2 using 1
    rw [hx']; unfold nB
    have hex : 1 < Real.exp x := by have := Real.add_one_lt_exp hx.ne'; linarith
    have : Real.exp x - 1 ≠ 0 := by linarith
    rw [Real.exp_neg]; field_simp; try ring

/-! ### C02-09, C02-10: the auxiliary function Q_⊥ -/

/-- Integrand of Q_⊥. -/
def qint (s : ℝ) : ℝ := 1 / (Real.exp (s ^ ((1:ℝ)/4)) - 1)

theorem qint_le {s : ℝ} (hs : 0 < s) : qint s ≤ s ^ (-((1:ℝ)/4)) := by
  unfold qint
  have hx : 0 < s ^ ((1:ℝ)/4) := Real.rpow_pos_of_pos hs _
  have h1 : s ^ ((1:ℝ)/4) ≤ Real.exp (s ^ ((1:ℝ)/4)) - 1 := by linarith [Real.add_one_le_exp (s ^ ((1:ℝ)/4))]
  rw [Real.rpow_neg hs.le, one_div]; exact inv_anti₀ hx h1

theorem qint_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ qint s := by
  unfold qint
  have : 1 < Real.exp (s ^ ((1:ℝ)/4)) := by
    have := Real.add_one_lt_exp (Real.rpow_pos_of_pos hs ((1:ℝ)/4)).ne'
    linarith [Real.rpow_pos_of_pos hs ((1:ℝ)/4)]
  exact div_nonneg zero_le_one (by linarith)

theorem qint_continuousOn : ContinuousOn qint (Set.Ioi 0) := by
  intro s hs
  have hs : 0 < s := hs
  apply ContinuousAt.continuousWithinAt
  unfold qint
  apply ContinuousAt.div continuousAt_const
  · exact (Real.continuous_exp.continuousAt.comp (Real.continuousAt_rpow_const s ((1:ℝ)/4) (Or.inl hs.ne'))).sub
      continuousAt_const
  · have : 1 < Real.exp (s ^ ((1:ℝ)/4)) := by
      have := Real.add_one_lt_exp (Real.rpow_pos_of_pos hs ((1:ℝ)/4)).ne'
      linarith [Real.rpow_pos_of_pos hs ((1:ℝ)/4)]
    linarith

/-- C02-09 (finiteness): the integrand of Q_⊥ is interval-integrable on [0, z] (dominated by s^{−1/4}). -/
theorem qint_integrable (z : ℝ) (hz : 0 ≤ z) : IntervalIntegrable qint MeasureTheory.volume 0 z := by
  have hdom : IntervalIntegrable (fun s : ℝ => s ^ (-((1:ℝ)/4))) MeasureTheory.volume 0 z :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  refine hdom.mono_fun' ?_ ?_
  · exact (qint_continuousOn.mono (fun s hs => by
      rw [Set.uIoc_of_le hz] at hs; exact hs.1)).aestronglyMeasurable measurableSet_uIoc
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc (fun s hs => ?_)
    rw [Set.uIoc_of_le hz] at hs
    show ‖qint s‖ ≤ s ^ (-((1:ℝ)/4))
    rw [Real.norm_eq_abs, abs_of_nonneg (qint_nonneg hs.1)]
    exact qint_le hs.1

/-- C02-09: Q_⊥′(z) = n_B(z^{1/4}) for z > 0; C02-10: Q′(z) = 1 + n_B(z^{1/4}) = 1/(1 − e^{−z^{1/4}}). -/
theorem Qperp_deriv {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun w => ∫ s in (0:ℝ)..w, qint s) (nB (z ^ ((1:ℝ)/4))) z ∧
      HasDerivAt (fun w => w + ∫ s in (0:ℝ)..w, qint s) (1 / (1 - Real.exp (-(z ^ ((1:ℝ)/4))))) z := by
  have hcont : ContinuousAt qint z := qint_continuousOn.continuousAt (Ioi_mem_nhds hz)
  have hint : IntervalIntegrable qint MeasureTheory.volume 0 z := qint_integrable z hz.le
  have hmeas : StronglyMeasurableAtFilter qint (𝓝 z) MeasureTheory.volume :=
    qint_continuousOn.stronglyMeasurableAtFilter isOpen_Ioi z hz
  have h1 := intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
  refine ⟨by simpa [qint, nB] using h1, ?_⟩
  have h2 := (hasDerivAt_id' z).add h1
  convert h2 using 1
  have hx : 0 < z ^ ((1:ℝ)/4) := Real.rpow_pos_of_pos hz _
  have he : 1 < Real.exp (z ^ ((1:ℝ)/4)) := by have := Real.add_one_lt_exp hx.ne'; linarith
  have hne : Real.exp (z ^ ((1:ℝ)/4)) - 1 ≠ 0 := by linarith
  have hne2 : 1 - (Real.exp (z ^ ((1:ℝ)/4)))⁻¹ ≠ 0 := by
    have : (Real.exp (z ^ ((1:ℝ)/4)))⁻¹ < 1 := inv_lt_one_of_one_lt₀ he
    linarith
  unfold qint; rw [Real.exp_neg]; field_simp; ring

/-! ### C02-16, C02-19: director invariance and density -/

/-- C02-16: z̃, x̃ and J_⊥ = n_B(x̃)(ê·∇Φ)ê are invariant under ê → −ê. -/
theorem nematic_invariance (e g : Fin 3 → ℝ) (a : ℝ) (f : ℝ → ℝ) :
    ((-e) ⬝ᵥ g) ^ 2 / a ^ 2 = (e ⬝ᵥ g) ^ 2 / a ^ 2 ∧
      (f (((-e) ⬝ᵥ g) ^ 2 / a ^ 2) * ((-e) ⬝ᵥ g)) • (-e) = (f ((e ⬝ᵥ g) ^ 2 / a ^ 2) * (e ⬝ᵥ g)) • e := by
  constructor
  · simp [neg_dotProduct]
  · ext i; simp [neg_dotProduct]

/-- C02-19 (adapted frame ê = ẑ, so the third row of M = ∂ê vanishes): 𝒮 = |M|² + tr(M²) − (tr M)²
= (M₁₁ − M₂₂)² + (M₁₂ + M₂₁)² + |b|² with b = Mẑ = (ê·∇)ê; hence 𝒮 ≥ 0, and (M₁₁ − M₂₂)² + (M₁₂ + M₂₁)²
= (λ₁ − λ₂)² for the symmetric part of the 2×2 block. -/
theorem director_density (M : Matrix (Fin 3) (Fin 3) ℝ) (h3 : ∀ i, M 2 i = 0) :
    (∑ a, ∑ i, M a i ^ 2) + (∑ a, ∑ i, M a i * M i a) - (∑ a, M a a) ^ 2 =
      (M 0 0 - M 1 1) ^ 2 + (M 0 1 + M 1 0) ^ 2 + (M 0 2 ^ 2 + M 1 2 ^ 2) ∧
      0 ≤ (∑ a, ∑ i, M a i ^ 2) + (∑ a, ∑ i, M a i * M i a) - (∑ a, M a a) ^ 2 := by
  have e : (∑ a, ∑ i, M a i ^ 2) + (∑ a, ∑ i, M a i * M i a) - (∑ a, M a a) ^ 2 =
      (M 0 0 - M 1 1) ^ 2 + (M 0 1 + M 1 0) ^ 2 + (M 0 2 ^ 2 + M 1 2 ^ 2) := by
    simp only [Fin.sum_univ_three, h3]; ring
  exact ⟨e, by rw [e]; positivity⟩

theorem sym_eigen_gap (p q s : ℝ) :
    let d := Real.sqrt ((p - q) ^ 2 + 4 * s ^ 2)
    ((p + q + d) / 2 - (p + q - d) / 2) ^ 2 = (p - q) ^ 2 + (2 * s) ^ 2 := by
  intro d
  rw [show (p + q + d) / 2 - (p + q - d) / 2 = d by ring, Real.sq_sqrt (by positivity)]; ring

/-! ### C02-30 … C02-36: lensing, deep profiles, cap radius -/

/-- C02-32: with ∇²Φ_b = 4πGρ and ∇²φ_⊥ = ∇·J, ∇²(Φ_b + φ_⊥) = 4πG(ρ + ∇·J/(4πG)). -/
theorem lensing_density {G ρ divJ lapb lapp : ℝ} (hG : G ≠ 0) (hb : lapb = 4 * π * G * ρ) (hp : lapp = divJ) :
    lapb + lapp = 4 * π * G * (ρ + divJ / (4 * π * G)) := by
  rw [hb, hp]; field_simp

/-- C02-33: ρ_⊥ = (1/(4πGr²)) d/dr(r²·A/r) = A/(4πGr²). -/
theorem deep_excess_density {A G r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun t => t ^ 2 * (A / t)) A r ∧ 1 / (4 * π * G * r ^ 2) * A = A / (4 * π * G * r ^ 2) := by
  constructor
  · have : (fun t => t ^ 2 * (A / t)) =ᶠ[𝓝 r] fun t => A * t := by
      filter_upwards [isOpen_ne.mem_nhds hr] with t ht
      field_simp
    exact (HasDerivAt.congr_of_eventuallyEq (by simpa using (hasDerivAt_id r).const_mul A) this)
  · ring

/-- C02-34: ΔΣ_⊥(R) = (2/R²)∫₀^R R′·A/(4GR′)dR′ − A/(4GR) = A/(4GR) (and Σ_⊥ = A/(4GR) is
GalacticLaw.surface_density_deep). -/
theorem excess_surface_density {A G R : ℝ} (hG : G ≠ 0) (hR : 0 < R) :
    2 / R ^ 2 * (∫ t in (0:ℝ)..R, A / (4 * G)) - A / (4 * G * R) = A / (4 * G * R) := by
  rw [intervalIntegral.integral_const, smul_eq_mul]; field_simp; ring

/-- C02-36: n_B(r_M/r) = C_R ⇔ r = r_M/ln(1 + 1/C_R), and r_C = r_M/ln(1 + 1/C) is strictly increasing in C > 0. -/
theorem cap_radius {rM r C : ℝ} (hM : 0 < rM) (hr : 0 < r) (hC : 0 < C) :
    (nB (rM / r) = C ↔ r = rM / Real.log (1 + 1 / C)) ∧
      StrictMonoOn (fun C => rM / Real.log (1 + 1 / C)) (Set.Ioi 0) := by
  have hl : ∀ C : ℝ, 0 < C → 0 < Real.log (1 + 1 / C) := fun C hC => Real.log_pos (by
    have : 0 < 1 / C := by positivity
    linarith)
  constructor
  · have hx : 0 < rM / r := div_pos hM hr
    have he : 1 < Real.exp (rM / r) := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hx
    unfold nB
    constructor
    · intro h
      have hne : Real.exp (rM / r) - 1 ≠ 0 := by linarith
      have h1 : Real.exp (rM / r) = 1 + 1 / C := by
        have : Real.exp (rM / r) - 1 = 1 / C := by rw [← h]; field_simp
        linarith
      have h2 : rM / r = Real.log (1 + 1 / C) := by rw [← h1, Real.log_exp]
      rw [eq_div_iff (hl C hC).ne', ← h2]; field_simp
    · intro h
      have h2 : rM / r = Real.log (1 + 1 / C) := by rw [h]; field_simp [(hl C hC).ne']
      have hpos : 0 < 1 + 1 / C := by have : 0 < 1 / C := by positivity
                                      linarith
      rw [h2, Real.exp_log hpos]
      field_simp; ring
  · intro C1 h1 C2 h2 hlt
    have h1 : (0:ℝ) < C1 := h1; have h2 : (0:ℝ) < C2 := h2
    simp only
    apply div_lt_div_of_pos_left hM (hl C2 h2)
    apply Real.log_lt_log (by have : 0 < 1 / C2 := by positivity
                              linarith)
    have : 1 / C2 < 1 / C1 := one_div_lt_one_div_of_lt h1 hlt
    linarith

/-- C02-37: C_R = (1 − η*)/ε ∈ (5.16, 5.17) at the closure root; 1/ln(1 + 1/20) ∈ (20.4, 20.6) and
1/ln(1 + 1/49) ∈ (49.4, 49.6). -/
theorem budget_numbers {η : ℝ} (h : Entropic.FiniteModel.ClosureStationary η) :
    5.16 < (1 - η) / (Entropic.ClosureRoot.gshare η / (4 * π ^ 2)) ∧
      (1 - η) / (Entropic.ClosureRoot.gshare η / (4 * π ^ 2)) < 5.17 := by
  obtain ⟨e1, e2⟩ := Entropic.Spine.epsilon_bracket h
  obtain ⟨b1, b2⟩ := Entropic.ClosureRoot.stationary_bracket h
  unfold Entropic.ClosureRoot.etaLo at b1; unfold Entropic.ClosureRoot.etaHi at b2
  have hp : 0 < Entropic.ClosureRoot.gshare η / (4 * π ^ 2) := by linarith
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

/-! ### C02-45, C02-48 … C02-56: response coefficients and transport -/

/-- C02-45: d/dg[n_B(√(g/a₀))·g] = n_B(x) − (x/2)n_B(x)(1 + n_B(x)) with x = √(g/a₀). -/
theorem parallel_response {a g : ℝ} (ha : 0 < a) (hg : 0 < g) :
    HasDerivAt (fun g => nB (Real.sqrt (g / a)) * g)
      (nB (Real.sqrt (g / a)) - Real.sqrt (g / a) / 2 * nB (Real.sqrt (g / a)) * (1 + nB (Real.sqrt (g / a)))) g := by
  set x := Real.sqrt (g / a)
  have hx : 0 < x := Real.sqrt_pos.mpr (div_pos hg ha)
  have he : 1 < Real.exp x := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hx
  have hs : HasDerivAt (fun g => Real.sqrt (g / a)) (1 / a / (2 * x)) g :=
    ((hasDerivAt_id' g).div_const a).sqrt (div_pos hg ha).ne'
  have hne : Real.exp x - 1 ≠ 0 := by linarith
  have h1 := (hs.exp.sub_const 1)
  have hn := (hasDerivAt_const g (1:ℝ)).div h1 hne
  have hm := hn.mul (hasDerivAt_id' g)
  have hx2 : x ^ 2 * a = g := by simp only [x]; rw [Real.sq_sqrt (div_pos hg ha).le]; field_simp
  have key : ∀ E t : ℝ, E - 1 ≠ 0 → t ≠ 0 → t ^ 2 * a = g →
      1 / (E - 1) - t / 2 * (1 / (E - 1)) * (1 + 1 / (E - 1)) =
        (0 * (E - 1) - 1 * (E * (1 / a / (2 * t)))) / (E - 1) ^ 2 * g + 1 / (E - 1) * 1 := by
    intro E t hE ht hg'
    rw [← hg']; field_simp; ring
  unfold nB
  convert hm using 1
  simp only [Pi.div_apply, Pi.mul_apply]
  exact key _ _ hne hx.ne' hx2

/-- C02-50: with g = g_bar(1 + n̄) and Var(n̄) = σ²/N, σ_g/g = σ/(√N(1 + n_B)) = √(𝓕 n_B/(N(1 + n_B))),
and N > 100𝓕 ⇒ σ_g/g < 0.1, N > 1112𝓕 ⇒ σ_g/g < 0.03. -/
theorem boost_fluctuation {σ n N F : ℝ} (hn : 0 < n) (hN : 0 < N) (hF : 0 < F) (hσ : σ ^ 2 = F * (n * (1 + n))) :
    Real.sqrt (σ ^ 2 / N) / (1 + n) = Real.sqrt (F * n / (N * (1 + n))) ∧
      (100 * F < N → Real.sqrt (F * n / (N * (1 + n))) < 0.1) ∧
      (1112 * F < N → Real.sqrt (F * n / (N * (1 + n))) < 0.03) := by
  have h1n : 0 < 1 + n := by linarith
  have hfrac : F * n / (N * (1 + n)) < F / N := by
    rw [div_lt_div_iff₀ (by positivity) hN]; nlinarith [mul_pos hF hN]
  refine ⟨?_, fun h => ?_, fun h => ?_⟩
  · conv_lhs => rw [show (1 + n) = Real.sqrt ((1 + n) ^ 2) from (Real.sqrt_sq h1n.le).symm]
    rw [← Real.sqrt_div (by positivity)]
    congr 1; rw [hσ]; field_simp
  · rw [show (0.1:ℝ) = Real.sqrt (0.1 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_lt_sqrt (by positivity)
    calc F * n / (N * (1 + n)) < F / N := hfrac
      _ < 0.1 ^ 2 := by rw [div_lt_iff₀ hN]; nlinarith
  · rw [show (0.03:ℝ) = Real.sqrt (0.03 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_lt_sqrt (by positivity)
    calc F * n / (N * (1 + n)) < F / N := hfrac
      _ < 0.03 ^ 2 := by rw [div_lt_iff₀ hN]; nlinarith

/-- C02-51: a time-independent solution of τ₀φ̈ + φ̇ − D∇²φ = −4πGDρ satisfies ∇²φ = 4πGρ (= ∇·J). -/
theorem telegrapher_static {τ D G ρ lap : ℝ} (hD : D ≠ 0) (h : τ * 0 + 0 - D * lap = -(4 * π * G * D * ρ)) :
    lap = 4 * π * G * ρ := by
  have : D * (lap - 4 * π * G * ρ) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hD
  · linarith

/-- C02-52: D/τ₀ = c² and τ₀⁻¹ = H₀ give D = c²/H₀ and front speed √(D/τ₀) = c. -/
theorem transport_parameters {D τ c H : ℝ} (hc : 0 ≤ c) (hτ : τ ≠ 0) (h1 : D / τ = c ^ 2) (h2 : 1 / τ = H) (hH : H ≠ 0) :
    D = c ^ 2 / H ∧ Real.sqrt (D / τ) = c := by
  refine ⟨?_, by rw [h1, Real.sqrt_sq hc]⟩
  have : τ = 1 / H := by field_simp at h2 ⊢; linarith
  rw [this] at h1; field_simp at h1 ⊢; linarith

/-- C02-53: F(ω,k) = Dk²/(Dk² − τω² − iω) is well defined for k ≠ 0 and F(0,k) = 1. -/
theorem fourier_response {D τ k ω : ℝ} (hD : 0 < D) (hk : k ≠ 0) :
    ((D * k ^ 2 : ℝ) : ℂ) - (τ * ω ^ 2 : ℝ) - Complex.I * ω ≠ 0 ∧
      ((D * k ^ 2 : ℝ) : ℂ) / (((D * k ^ 2 : ℝ) : ℂ) - (τ * (0:ℝ) ^ 2 : ℝ) - Complex.I * (0:ℝ)) = 1 := by
  have hpos : 0 < D * k ^ 2 := by positivity
  constructor
  · intro h
    have e : ((D * k ^ 2 : ℝ) : ℂ) - ((τ * ω ^ 2 : ℝ) : ℂ) - Complex.I * ω = ⟨D * k ^ 2 - τ * ω ^ 2, -ω⟩ := by
      apply Complex.ext <;> simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;> ring
    rw [e, Complex.ext_iff] at h
    simp at h
    obtain ⟨h1, h2⟩ := h
    rw [h2] at h1; nlinarith
  · have : ((D * k ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [show ((D * k ^ 2 : ℝ) : ℂ) - ((τ * (0:ℝ) ^ 2 : ℝ) : ℂ) - Complex.I * ((0:ℝ) : ℂ) = ((D * k ^ 2 : ℝ) : ℂ) by
      push_cast; ring]
    exact div_self this

/-- C02-54: every complex root of τs² + s + Dk² = 0 (τ, D > 0, k ≠ 0) has negative real part. -/
theorem laplace_poles_stable {τ D k : ℝ} (hτ : 0 < τ) (hD : 0 < D) (hk : k ≠ 0) (s : ℂ)
    (hs : (τ : ℂ) * s ^ 2 + s + (D * k ^ 2 : ℝ) = 0) : s.re < 0 := by
  have hre := congrArg Complex.re hs
  have him := congrArg Complex.im hs
  simp [sq, Complex.mul_re, Complex.mul_im] at hre him
  have hpos : 0 < D * k ^ 2 := by positivity
  by_cases hb : s.im = 0
  · rw [hb] at hre
    by_contra h; push_neg at h
    nlinarith [mul_nonneg hτ.le (mul_self_nonneg s.re)]
  · have : 2 * τ * s.re + 1 = 0 := by
      have : s.im * (2 * τ * s.re + 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hb
      · exact h
    nlinarith

/-- C02-55, C02-56: (v/c)² = 10⁻⁶ for v = 300 km/s, c = 3·10⁵ km/s; 1 Mpc/c ∈ (3.2, 3.3) Myr, about
2.5 orders of magnitude below 1 Gyr (ratio ∈ (300, 310)). -/
theorem transport_magnitudes :
    ((300:ℝ) / 3e5) ^ 2 = 1e-6 ∧
      3.2e6 < (3.0856775814913673e22 / 299792458 : ℝ) / 3.15576e7 ∧
      (3.0856775814913673e22 / 299792458 : ℝ) / 3.15576e7 < 3.3e6 ∧
      300 < (1e9 : ℝ) / ((3.0856775814913673e22 / 299792458) / 3.15576e7) ∧
      (1e9 : ℝ) / ((3.0856775814913673e22 / 299792458) / 3.15576e7) < 310 := by
  norm_num

/-! ### C02-57 … C02-69: cluster caps and occupancy -/

/-- C02-57, C02-59: with Ω_c/Ω_b = 1/ε, Ω_m/Ω_b = 1 + 1/ε ∈ (6.319, 6.323) and f_b = ε/(1 + ε) ∈ (0.1581, 0.1583)
at the closure root. -/
theorem bath_cap {η : ℝ} (h : Entropic.FiniteModel.ClosureStationary η) :
    let ε := Entropic.ClosureRoot.gshare η / (4 * π ^ 2)
    6.319 < 1 + 1 / ε ∧ 1 + 1 / ε < 6.323 ∧ 0.1581 < ε / (1 + ε) ∧ ε / (1 + ε) < 0.1583 ∧
      (∀ Ωb Ωc : ℝ, Ωb ≠ 0 → Ωc / Ωb = 1 / ε → (Ωb + Ωc) / Ωb = 1 + 1 / ε ∧ Ωb / (Ωb + Ωc) = ε / (1 + ε)) := by
  intro ε
  obtain ⟨e1, e2⟩ := Entropic.Spine.epsilon_bracket h
  have e1' : 0.1879 < ε := e1
  have e2' : ε < 0.1880 := e2
  have hp : 0 < ε := by linarith
  refine ⟨?_, ?_, ?_, ?_, fun Ωb Ωc hb hc => ?_⟩
  · rw [show 1 + 1 / ε = (ε + 1) / ε by field_simp, lt_div_iff₀ hp]; nlinarith
  · rw [show 1 + 1 / ε = (ε + 1) / ε by field_simp, div_lt_iff₀ hp]; nlinarith
  · rw [lt_div_iff₀ (by linarith)]; nlinarith
  · rw [div_lt_iff₀ (by linarith)]; nlinarith
  · have hc' : Ωc = Ωb / ε := by field_simp at hc ⊢; linarith
    constructor
    · rw [hc']; field_simp
    · rw [hc']; have : Ωb + Ωb / ε ≠ 0 := by
        rw [show Ωb + Ωb / ε = Ωb * (1 + 1 / ε) by ring]; exact mul_ne_zero hb (by positivity)
      field_simp; ring

/-- C02-60: R_rel = 1 + (1 − ε)B f ≤ 1 + (1 − ε), strict when B f < 1; CLASH (B = 0.83, f = 0.9) gives
R_rel ∈ (1.60, 1.61) at the closure root. -/
theorem linear_lift {ε B f : ℝ} (hε : ε < 1) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    1 + (1 - ε) * B * f ≤ 1 + (1 - ε) ∧ (B * f < 1 → 1 + (1 - ε) * B * f < 1 + (1 - ε)) := by
  have hbf : B * f ≤ 1 := by nlinarith
  have h1 : 0 < 1 - ε := by linarith
  constructor
  · nlinarith
  · intro h; nlinarith

theorem clash_value {η : ℝ} (h : Entropic.FiniteModel.ClosureStationary η) :
    1.60 < 1 + (1 - Entropic.ClosureRoot.gshare η / (4 * π ^ 2)) * 0.83 * 0.9 ∧
      1 + (1 - Entropic.ClosureRoot.gshare η / (4 * π ^ 2)) * 0.83 * 0.9 < 1.61 := by
  obtain ⟨e1, e2⟩ := Entropic.Spine.epsilon_bracket h
  constructor <;> nlinarith

/-- C02-62: for W > 0, W g ν(Wg/a)/(g ν(g/a)) → √W as g → 0⁺ (ν(y) = 1/(1 − e^{−√y})). -/
theorem deep_compression {a W : ℝ} (ha : 0 < a) (hW : 0 < W) :
    Tendsto (fun g => Entropic.GalacticLaw.gObs a (W * g) / Entropic.GalacticLaw.gObs a g) (𝓝[>] 0) (𝓝 (Real.sqrt W)) := by
  have h1 := Entropic.GalacticLaw.deep_limit ha
  have hWg : Tendsto (fun g => W * g) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun g => W * g) (𝓝 0) (𝓝 (W * 0)) := (continuous_const.mul continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with g hg; exact mul_pos hW hg
  have h2 := h1.comp hWg
  have hq : Tendsto (fun g => (Entropic.GalacticLaw.gObs a (W * g) / Real.sqrt (a * (W * g))) /
      (Entropic.GalacticLaw.gObs a g / Real.sqrt (a * g)) * Real.sqrt W) (𝓝[>] 0) (𝓝 (1 / 1 * Real.sqrt W)) :=
    ((h2.div h1 one_ne_zero).mul_const _)
  rw [show (1:ℝ) / 1 * Real.sqrt W = Real.sqrt W by ring] at hq
  apply hq.congr'
  filter_upwards [self_mem_nhdsWithin] with g hg
  have hg : (0:ℝ) < g := hg
  have hG := (Entropic.GalacticLaw.gObs_sandwich ha hg).1
  have hGW := (Entropic.GalacticLaw.gObs_sandwich ha (mul_pos hW hg)).1
  have hs1 : 0 < Real.sqrt (a * g) := Real.sqrt_pos.mpr (by positivity)
  have hsw : Real.sqrt (a * (W * g)) = Real.sqrt W * Real.sqrt (a * g) := by
    rw [← Real.sqrt_mul hW.le]; ring_nf
  have hpos : 0 < Entropic.GalacticLaw.gObs a g := by linarith
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW
  rw [hsw]; field_simp

/-- C02-63: f_dec + f_cont = 1 gives f_dec + (1 + 1/ε)f_cont = 1 + f_cont/ε. -/
theorem cap_residual {fd fc ε : ℝ} (h : fd + fc = 1) (hε : ε ≠ 0) : fd + (1 + 1 / ε) * fc = 1 + fc / ε := by
  have : fd = 1 - fc := by linarith
  rw [this]; field_simp; ring

/-- C02-64: S ↦ gObs(S g_bar) is strictly increasing and continuous with limits 0 and ∞, so
gObs(S g_bar) = g_obs has a unique solution S > 0. -/
theorem source_inversion {a gb go : ℝ} (ha : 0 < a) (hb : 0 < gb) (ho : 0 < go) :
    ∃! S, 0 < S ∧ Entropic.GalacticLaw.gObs a (S * gb) = go := by
  have hmono : StrictMonoOn (fun S => Entropic.GalacticLaw.gObs a (S * gb)) (Set.Ioi 0) := by
    intro S1 h1 S2 h2 hlt
    exact Entropic.GalacticLaw.gObs_strictMonoOn ha (mul_pos h1 hb) (mul_pos h2 hb)
      (mul_lt_mul_of_pos_right hlt hb)
  have hcont : ContinuousOn (fun S => Entropic.GalacticLaw.gObs a (S * gb)) (Set.Ioi 0) := by
    intro S hS
    have hS : 0 < S := hS
    apply ContinuousAt.continuousWithinAt
    unfold Entropic.GalacticLaw.gObs
    apply ContinuousAt.div (by fun_prop)
    · fun_prop
    · have := Entropic.GalacticLaw.one_sub_exp_neg_pos (Real.sqrt_pos.mpr (div_pos (mul_pos hS hb) ha))
      exact this.ne'
  -- upper point: S₂ with S₂ g_b ≥ g_o
  set S2 := go / gb + 1
  have hS2 : 0 < S2 := by positivity
  have hup : go < Entropic.GalacticLaw.gObs a (S2 * gb) := by
    have := (Entropic.GalacticLaw.gObs_sandwich ha (mul_pos hS2 hb)).1
    have : go < S2 * gb := by simp only [S2]; rw [add_mul, div_mul_cancel₀ _ hb.ne']; linarith
    linarith
  -- lower point: S₁ small with gObs ≤ S₁ g_b + √(a S₁ g_b) ≤ g_o/2
  set t := min (go / 4) (go ^ 2 / (16 * a))
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  set S1 := t / gb
  have hS1 : 0 < S1 := div_pos ht hb
  have hlow : Entropic.GalacticLaw.gObs a (S1 * gb) < go := by
    have hS1g : S1 * gb = t := by simp only [S1]; field_simp
    have := (Entropic.GalacticLaw.gObs_sandwich ha (mul_pos hS1 hb)).2.2
    rw [hS1g] at this ⊢
    have h1 : t ≤ go / 4 := min_le_left _ _
    have h2 : t ≤ go ^ 2 / (16 * a) := min_le_right _ _
    have h3 : Real.sqrt (a * t) ≤ go / 4 := by
      rw [show go / 4 = Real.sqrt ((go / 4) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      apply Real.sqrt_le_sqrt
      calc a * t ≤ a * (go ^ 2 / (16 * a)) := mul_le_mul_of_nonneg_left h2 ha.le
        _ = (go / 4) ^ 2 := by field_simp; ring
    linarith
  have hlt : S1 < S2 := by
    by_contra hc; push_neg at hc
    have := hmono.le_iff_le hS2 hS1 |>.mpr hc
    linarith
  obtain ⟨S, ⟨hS1', hS2'⟩, hS⟩ := intermediate_value_Ioo hlt.le
    (hcont.mono (fun x hx => lt_of_lt_of_le hS1 hx.1)) ⟨hlow, hup⟩
  refine ⟨S, ⟨lt_trans hS1 hS1', hS⟩, fun S' ⟨hS'0, hS'⟩ => ?_⟩
  exact hmono.injOn hS'0 (lt_trans hS1 hS1') (hS'.trans hS.symm)

/-- C02-68: ν(y) > 1 + 1/ε ⇔ y < (ln(1 + ε))² (y, ε > 0). -/
theorem cap_threshold {y ε : ℝ} (hy : 0 < y) (hε : 0 < ε) :
    1 + 1 / ε < 1 / (1 - Real.exp (-Real.sqrt y)) ↔ y < (Real.log (1 + ε)) ^ 2 := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hd := Entropic.GalacticLaw.one_sub_exp_neg_pos hs
  have hl : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  have e1 : (1 + 1 / ε < 1 / (1 - Real.exp (-Real.sqrt y))) ↔ (1 - Real.exp (-Real.sqrt y) < ε / (1 + ε)) := by
    rw [lt_div_iff₀ hd, show (1 + 1 / ε) * (1 - Real.exp (-Real.sqrt y)) < 1 ↔
      1 - Real.exp (-Real.sqrt y) < 1 / (1 + 1 / ε) by
        rw [lt_div_iff₀ (by positivity)]; constructor <;> intro h <;> linarith]
    rw [show 1 / (1 + 1 / ε) = ε / (1 + ε) by field_simp; ring]
  have e2 : (1 - Real.exp (-Real.sqrt y) < ε / (1 + ε)) ↔ Real.exp (-Real.log (1 + ε)) < Real.exp (-Real.sqrt y) := by
    rw [show Real.exp (-Real.log (1 + ε)) = (1 + ε)⁻¹ by rw [Real.exp_neg, Real.exp_log (by linarith)],
      show ε / (1 + ε) = 1 - (1 + ε)⁻¹ by field_simp; ring]
    constructor <;> intro h <;> linarith
  rw [e1, e2, Real.exp_lt_exp, neg_lt_neg_iff]
  constructor
  · intro h
    have := mul_self_lt_mul_self hs.le h
    rw [Real.mul_self_sqrt hy.le] at this; nlinarith
  · intro h
    rw [show Real.log (1 + ε) = Real.sqrt (Real.log (1 + ε) ^ 2) by rw [Real.sqrt_sq hl.le]]
    exact Real.sqrt_lt_sqrt hy.le h

/-- C02-69: σ_A = εM_c/M_A ∈ [0,1] ⇔ 0 ≤ M_c ≤ M_A/ε. -/
theorem occupancy {ε M Mc : ℝ} (hε : 0 < ε) (hM : 0 < M) :
    (0 ≤ ε * Mc / M ∧ ε * Mc / M ≤ 1) ↔ (0 ≤ Mc ∧ Mc ≤ M / ε) := by
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨?_, ?_⟩
    · have := (div_nonneg_iff.mp h0); rcases this with ⟨a, _⟩ | ⟨_, b⟩
      · exact nonneg_of_mul_nonneg_right (by linarith) hε |> fun _ => by nlinarith
      · linarith
    · rw [div_le_one hM] at h1; rw [le_div_iff₀ hε]; linarith
  · rintro ⟨h0, h1⟩
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hM]; rw [le_div_iff₀ hε] at h1; linarith

/-! ### C02-70, C02-71, C02-76, C02-79 -/

/-- C02-70: dφ/dτ = u^μ∇_μφ = −u·u with u_μ = −∇_μφ, so dφ/dτ = 1 forces u·u = −1 and X = −½∇φ·∇φ = ½. -/
theorem clock_normalization {uu dφ : ℝ} (h1 : dφ = -uu) (h2 : dφ = 1) : uu = -1 ∧ -(1/2) * uu = 1/2 := by
  constructor <;> linarith

/-- C02-71: on X = ½ the stress λ∂φ∂φ + gλ(X − ½) is the dust form ρuu with ρ = λ, p = 0. -/
theorem dust_stress (lam du dv g : ℝ) : lam * du * dv + g * lam * ((1:ℝ)/2 - 1/2) = lam * (-du) * (-dv) := by ring

/-- C02-76: 9·(1/3)² = 1. -/
theorem nine_state_dilation : (9:ℝ) * (1/3) ^ 2 = 1 := by norm_num

/-- C02-79: with a³ρ_C = ρ₀e^{−ηF(a)} and ρ_Λ(a) = ηρ₀∫₀^a a′^{−3}e^{−ηF}F′ da′,
d(a³ρ_C)/da = −a³ dρ_Λ/da (so ρ̇_C + 3Hρ_C = −ρ̇_Λ). -/
theorem release_exchange (F F' : ℝ → ℝ) {η ρ0 a : ℝ} (ha : 0 < a) (hF : ∀ x, HasDerivAt F (F' x) x)
    (hcont : Continuous fun x => x ^ (-3:ℤ) * Real.exp (-η * F x) * F' x) :
    HasDerivAt (fun x => ρ0 * Real.exp (-η * F x)) (-(η * ρ0 * Real.exp (-η * F a) * F' a)) a ∧
      HasDerivAt (fun x => η * ρ0 * ∫ t in (1:ℝ)..x, t ^ (-3:ℤ) * Real.exp (-η * F t) * F' t)
        (η * ρ0 * (a ^ (-3:ℤ) * Real.exp (-η * F a) * F' a)) a ∧
      -(η * ρ0 * Real.exp (-η * F a) * F' a) = -(a ^ 3 * (η * ρ0 * (a ^ (-3:ℤ) * Real.exp (-η * F a) * F' a))) := by
  refine ⟨?_, ?_, ?_⟩
  · have := (((hF a).const_mul (-η)).exp).const_mul ρ0
    convert this using 1; ring
  · exact (hcont.integral_hasStrictDerivAt 1 a).hasDerivAt.const_mul _
  · have : a ^ 3 * a ^ (-3:ℤ) = 1 := by
      rw [zpow_neg, zpow_ofNat]; field_simp
    calc -(η * ρ0 * Real.exp (-η * F a) * F' a)
        = -((a ^ 3 * a ^ (-3:ℤ)) * (η * ρ0 * Real.exp (-η * F a) * F' a)) := by rw [this, one_mul]
      _ = _ := by ring

end Entropic.Main.Galactic
