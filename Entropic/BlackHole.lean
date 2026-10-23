import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Tactic

/-! Strong-field spherical sector (main manuscript Sec. 21, App. F.1, F.4, F.5).

F.1: the capacity-to-lapse map is fixed by its axioms. A continuous, positive,
multiplicative map on (0,1] is a power q^α (this is the step the manuscript
states as "with continuity"); vanishing at q → 0⁺ forces α > 0; weak-field
matching f'(1) = 1/2 forces α = 1/2, so N = √q and N² = q.

F.4/N.5: constancy of the Misner–Sharp mass is equivalent to the Schwarzschild
form q(r) = 1 − r_s/r on any exterior interval, with the marginal surface at r_s.

F.5: Schwarzschild horizon thermodynamics with the matched length L*² = ħG/c³.
The physical identifications (capacity ↔ q_geo, the domain postulate q ≥ 0,
L_P = L*) are INPUT, exactly as the manuscript states them. -/

noncomputable section
namespace Entropic.BlackHole
open Real Set Filter Topology

/-! ## F.1  Uniqueness of the lapse map -/

section Lapse
variable {f : ℝ → ℝ}

/-- g(t) = log f(e^{-t}) turns the multiplicative law on (0,1] into Cauchy's
additive law on [0,∞). -/
def gOf (f : ℝ → ℝ) (t : ℝ) : ℝ := Real.log (f (Real.exp (-t)))

theorem exp_neg_mem {t : ℝ} (ht : 0 ≤ t) : Real.exp (-t) ∈ Ioc (0:ℝ) 1 :=
  ⟨Real.exp_pos _, by rw [Real.exp_le_one_iff]; linarith⟩

variable (hpos : ∀ q ∈ Ioc (0:ℝ) 1, 0 < f q)
  (hmul : ∀ x ∈ Ioc (0:ℝ) 1, ∀ y ∈ Ioc (0:ℝ) 1, f (x * y) = f x * f y)
include hpos hmul

theorem f_one : f 1 = 1 := by
  have h := hmul 1 ⟨one_pos, le_rfl⟩ 1 ⟨one_pos, le_rfl⟩
  have hp := hpos 1 ⟨one_pos, le_rfl⟩
  rw [mul_one] at h
  have : f 1 * (f 1 - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h0 | h1
  · linarith
  · linarith

theorem g_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : gOf f (s + t) = gOf f s + gOf f t := by
  unfold gOf
  rw [neg_add, Real.exp_add, hmul _ (exp_neg_mem hs) _ (exp_neg_mem ht),
    Real.log_mul (hpos _ (exp_neg_mem hs)).ne' (hpos _ (exp_neg_mem ht)).ne']

theorem g_zero : gOf f 0 = 0 := by
  unfold gOf; rw [neg_zero, Real.exp_zero, f_one hpos hmul, Real.log_one]

/-- Odd extension of g to all of ℝ. -/
def G (f : ℝ → ℝ) (t : ℝ) : ℝ := if 0 ≤ t then gOf f t else -gOf f (-t)

theorem G_add (s t : ℝ) : G f (s + t) = G f s + G f t := by
  have key := fun {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) => g_add hpos hmul (s := a) (t := b) ha hb
  unfold G
  by_cases hs : 0 ≤ s <;> by_cases ht : 0 ≤ t <;> by_cases hst : 0 ≤ s + t <;>
    simp only [hs, ht, hst, if_true, if_false]
  · exact key hs ht
  · linarith
  · -- s ≥ 0, t < 0, s + t ≥ 0:  g(s) = g(s+t) + g(-t)
    have := key hst (by linarith : 0 ≤ -t); rw [show s + t + -t = s by ring] at this; linarith
  · -- s ≥ 0, t < 0, s + t < 0:  g(-t) = g(s) + g(-(s+t))
    have := key hs (by linarith : 0 ≤ -(s + t)); rw [show s + -(s + t) = -t by ring] at this; linarith
  · have := key hst (by linarith : 0 ≤ -s); rw [show s + t + -s = t by ring] at this; linarith
  · have := key ht (by linarith : 0 ≤ -(s + t)); rw [show t + -(s + t) = -s by ring] at this; linarith
  · linarith
  · have := key (by linarith : 0 ≤ -s) (by linarith : 0 ≤ -t)
    rw [show -s + -t = -(s + t) by ring] at this; linarith

variable (hcont : ContinuousOn f (Ioc (0:ℝ) 1))
include hcont

omit hmul in
theorem g_continuousOn : ContinuousOn (gOf f) (Ici 0) := by
  unfold gOf
  have h1 : ContinuousOn (fun t : ℝ => Real.exp (-t)) (Ici 0) := (continuous_neg.rexp).continuousOn
  have h2 : ContinuousOn (fun t => f (Real.exp (-t))) (Ici 0) :=
    hcont.comp h1 (fun t ht => exp_neg_mem ht)
  exact h2.log (fun t ht => (hpos _ (exp_neg_mem ht)).ne')

theorem G_continuous : Continuous (G f) := by
  have hc := g_continuousOn hpos hcont
  unfold G
  refine continuous_if_le continuous_const continuous_id ?_ ?_ ?_
  · exact hc.mono (fun t ht => ht)
  · have : ContinuousOn (fun t => gOf f (-t)) {x : ℝ | id x ≤ 0} :=
      hc.comp continuous_neg.continuousOn (fun t (ht : id t ≤ 0) => show (0:ℝ) ≤ -t by simp only [id] at ht; linarith)
    exact this.neg
  · intro t ht
    have h0 : t = 0 := (show (0:ℝ) = t from ht).symm
    subst h0; simp [g_zero hpos hmul]

/-- The lapse map is a power law: ∃ α, f(q) = q^α on (0,1]. -/
theorem lapse_is_power : ∃ α : ℝ, ∀ q ∈ Ioc (0:ℝ) 1, f q = q ^ α := by
  let Gh : ℝ →+ ℝ := { toFun := G f, map_zero' := by simp [G, g_zero hpos hmul],
                        map_add' := G_add hpos hmul }
  have hlin : ∀ t, G f t = t * G f 1 := by
    intro t
    have := map_real_smul Gh (G_continuous hpos hmul hcont) t 1
    simpa [Gh] using this
  refine ⟨-G f 1, fun q hq => ?_⟩
  have hq0 : 0 < q := hq.1
  have ht : 0 ≤ -Real.log q := by
    have := Real.log_nonpos hq0.le hq.2; linarith
  have hG : G f (-Real.log q) = gOf f (-Real.log q) := by simp [G, ht]
  have hf : f q = Real.exp (gOf f (-Real.log q)) := by
    unfold gOf; rw [neg_neg, Real.exp_log hq0, Real.exp_log (hpos q hq)]
  rw [hf, ← hG, hlin, Real.rpow_def_of_pos hq0]
  congr 1; ring

/-- Vanishing lapse at exhausted capacity forces α > 0. -/
theorem lapse_exponent_pos (hzero : Tendsto f (𝓝[>] 0) (𝓝 0)) :
    ∃ α : ℝ, 0 < α ∧ ∀ q ∈ Ioc (0:ℝ) 1, f q = q ^ α := by
  obtain ⟨α, hα⟩ := lapse_is_power hpos hmul hcont
  refine ⟨α, ?_, hα⟩
  by_contra hle; push_neg at hle
  -- for q ∈ (0,1], q^α ≥ 1 when α ≤ 0, contradicting f → 0
  have hev : ∀ᶠ q in 𝓝[>] (0:ℝ), 1 ≤ f q := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with q hq
    rw [hα q ⟨hq.1, hq.2.le⟩]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hq.1 hq.2.le hle
  have := ge_of_tendsto hzero hev
  linarith

/-- Weak-field matching N = 1 − δ/2 at q = 1 − δ (i.e. f'(1) = 1/2 from inside)
forces α = 1/2, so the lapse is N = √q and N² = q. -/
theorem lapse_is_sqrt (hderiv : HasDerivWithinAt f (1/2) (Ioc (0:ℝ) 1) 1) :
    ∀ q ∈ Ioc (0:ℝ) 1, f q = Real.sqrt q := by
  obtain ⟨α, hα⟩ := lapse_is_power hpos hmul hcont
  have hpow : HasDerivWithinAt (fun q : ℝ => q ^ α) α (Ioc (0:ℝ) 1) 1 := by
    have := (Real.hasDerivAt_rpow_const (p := α) (x := 1) (Or.inl one_ne_zero)).hasDerivWithinAt
      (s := Ioc (0:ℝ) 1)
    simpa using this
  have hcongr : HasDerivWithinAt (fun q : ℝ => q ^ α) (1/2) (Ioc (0:ℝ) 1) 1 :=
    hderiv.congr (fun q hq => (hα q hq).symm) (by simp [hα 1 ⟨one_pos, le_rfl⟩])
  have huniq : UniqueDiffWithinAt ℝ (Ioc (0:ℝ) 1) 1 :=
    uniqueDiffOn_Ioc 0 1 1 ⟨one_pos, le_rfl⟩
  have hαv : α = 1/2 := huniq.eq_deriv _ hpow hcongr
  intro q hq
  rw [hα q hq, hαv, Real.sqrt_eq_rpow]

/-- The axioms are consistent: √q satisfies every hypothesis above. -/
theorem sqrt_satisfies_axioms :
    ContinuousOn Real.sqrt (Ioc (0:ℝ) 1) ∧ (∀ q ∈ Ioc (0:ℝ) 1, 0 < Real.sqrt q) ∧
    (∀ x ∈ Ioc (0:ℝ) 1, ∀ y ∈ Ioc (0:ℝ) 1, Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y) ∧
    Tendsto Real.sqrt (𝓝[>] 0) (𝓝 0) ∧
    HasDerivWithinAt Real.sqrt (1/2) (Ioc (0:ℝ) 1) 1 := by
  refine ⟨Real.continuous_sqrt.continuousOn, fun q hq => Real.sqrt_pos.mpr hq.1,
    fun x hx y _ => Real.sqrt_mul hx.1.le y, ?_, ?_⟩
  · have := Real.continuous_sqrt.tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  · have := (Real.hasDerivAt_sqrt (x := 1) one_ne_zero).hasDerivWithinAt (s := Ioc (0:ℝ) 1)
    simpa using this

end Lapse

/-! ## F.4 / N.5  Misner–Sharp constancy ⇔ Schwarzschild exterior -/

section Exterior

/-- Misner–Sharp mass of the radial invariant q_geo = |∇R|² at areal radius r. -/
def msMass (G c : ℝ) (q : ℝ → ℝ) (r : ℝ) : ℝ := c ^ 2 * r * (1 - q r) / (2 * G)

/-- Static spherical vacuum: (r q)' = 1 on an exterior interval (r₀, ∞), which is
the statement d M_MS/dr = 0. Its solutions are exactly q = 1 − 2GM/(c²r). -/
theorem vacuum_iff_schwarzschild {G c r₀ : ℝ} (hG : G ≠ 0) (hc : c ≠ 0) (hr₀ : 0 ≤ r₀)
    {q dq : ℝ → ℝ} (hd : ∀ r ∈ Ioi r₀, HasDerivAt q (dq r) r)
    (hvac : ∀ r ∈ Ioi r₀, r * dq r + q r = 1) :
    ∃ M : ℝ, ∀ r ∈ Ioi r₀, q r = 1 - 2 * G * M / (c ^ 2 * r) := by
  -- M_MS has zero derivative on (r₀, ∞), hence is constant
  have hM : ∀ r ∈ Ioi r₀, HasDerivAt (msMass G c q) 0 r := by
    intro r hr
    have := (((hasDerivAt_id r).const_mul (c ^ 2)).fun_mul ((hd r hr).const_sub 1)).div_const (2 * G)
    unfold msMass
    convert this using 1
    · funext x; simp [id]
    · rw [show c ^ 2 * 1 * (1 - q r) + c ^ 2 * id r * -dq r = c ^ 2 * (1 - (r * dq r + q r)) by
        simp only [id]; ring, hvac r hr]
      simp
  have hconst : ∀ a ∈ Ioi r₀, ∀ b ∈ Ioi r₀, msMass G c q a = msMass G c q b := by
    intro a ha b hb
    have hdiff : DifferentiableOn ℝ (msMass G c q) (Ioi r₀) :=
      fun x hx => (hM x hx).differentiableAt.differentiableWithinAt
    exact (convex_Ioi r₀).is_const_of_fderivWithin_eq_zero hdiff
      (fun x hx => by
        rw [fderivWithin_eq_fderiv (isOpen_Ioi.uniqueDiffWithinAt hx) (hM x hx).differentiableAt]
        exact (hM x hx).hasFDerivAt.fderiv.trans (by ext; simp)) ha hb
  obtain ⟨r₁, hr₁⟩ : ∃ r₁, r₁ ∈ Ioi r₀ := ⟨r₀ + 1, by simp⟩
  refine ⟨msMass G c q r₁, fun r hr => ?_⟩
  rw [← hconst r hr r₁ hr₁]
  have hr0 : 0 < r := lt_of_le_of_lt hr₀ hr
  unfold msMass; field_simp; ring

/-- Conversely the Schwarzschild profile satisfies the vacuum relation. -/
theorem schwarzschild_vacuum {rs r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun x => 1 - rs / x) (rs / r ^ 2) r ∧ r * (rs / r ^ 2) + (1 - rs / r) = 1 := by
  constructor
  · have := ((hasDerivAt_inv hr).const_mul rs).const_sub 1
    simp only [div_eq_mul_inv]
    convert this using 1
    ring
  · field_simp <;> ring

def qS (rs r : ℝ) : ℝ := 1 - rs / r

/-- Sign of q_geo labels untrapped (r > r_s), marginal (r = r_s), trapped (0 < r < r_s). -/
theorem qS_sign {rs r : ℝ} (hrs : 0 < rs) (hr : 0 < r) :
    (0 < qS rs r ↔ rs < r) ∧ (qS rs r = 0 ↔ r = rs) ∧ (qS rs r < 0 ↔ r < rs) := by
  unfold qS
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_pos, div_lt_one hr]
  · rw [sub_eq_zero, eq_comm, div_eq_one_iff_eq hr.ne', eq_comm]
  · rw [sub_neg, one_lt_div hr]

/-- With N = √q (F.1) the lapse squared equals the radial invariant on the exterior. -/
theorem lapse_sq_eq_qgeo {rs r : ℝ} (hrs : 0 ≤ rs) (hr : rs < r) :
    Real.sqrt (qS rs r) ^ 2 = qS rs r := by
  have hr0 : 0 < r := lt_of_le_of_lt hrs hr
  have hq : 0 ≤ qS rs r := by unfold qS; rw [sub_nonneg, div_le_one hr0]; exact hr.le
  exact Real.sq_sqrt hq

end Exterior

/-! ## F.5  Horizon thermodynamics of the exterior saddle -/

section Thermo
variable {G c hbar kB : ℝ}

def rS (G c M : ℝ) : ℝ := 2 * G * M / c ^ 2
/-- Surface gravity κ = (c²/2) dq/dr at r_s. -/
def kappa (G c M : ℝ) : ℝ := c ^ 2 / 2 * (1 / rS G c M)
def hawkingT (G c hbar kB M : ℝ) : ℝ := hbar * kappa G c M / (2 * π * kB * c)
/-- Matched cell length L*² = hbarG/c³ (L_P(G*) = L*). -/
def Lsq (G c hbar : ℝ) : ℝ := hbar * G / c ^ 3
def area (G c M : ℝ) : ℝ := 4 * π * rS G c M ^ 2
def entropyBH (G c hbar kB M : ℝ) : ℝ := kB * area G c M / (4 * Lsq G c hbar)

variable (hG : 0 < G) (hc : 0 < c) (hhbar : 0 < hbar) (hk : 0 < kB)
include hG hc hhbar hk

theorem surface_gravity_from_q {M : ℝ} (hM : 0 < M) :
    HasDerivAt (qS (rS G c M)) (1 / rS G c M) (rS G c M) ∧
      kappa G c M = c ^ 4 / (4 * G * M) := by
  have hr : rS G c M ≠ 0 := by unfold rS; positivity
  constructor
  · have := (schwarzschild_vacuum (rs := rS G c M) hr).1
    convert this using 1
    · funext x; simp [qS, div_eq_mul_inv]
    · field_simp
  · unfold kappa rS; field_simp <;> ring

theorem hawking_temperature {M : ℝ} (hM : 0 < M) :
    hawkingT G c hbar kB M = hbar * c ^ 3 / (8 * π * G * M * kB) := by
  unfold hawkingT kappa rS; field_simp <;> ring

theorem entropy_eq {M : ℝ} (hM : 0 < M) :
    entropyBH G c hbar kB M = 4 * π * kB * G * M ^ 2 / (hbar * c) := by
  unfold entropyBH area rS Lsq; field_simp <;> ring

/-- First law: d(Mc²) = T dS, i.e. T · dS/dM = c². -/
theorem first_law {M : ℝ} (hM : 0 < M) :
    HasDerivAt (entropyBH G c hbar kB) (8 * π * kB * G * M / (hbar * c)) M ∧
      hawkingT G c hbar kB M * (8 * π * kB * G * M / (hbar * c)) = c ^ 2 := by
  constructor
  · have : entropyBH G c hbar kB = fun M => (4 * π * kB * G / (hbar * c)) * M ^ 2 := by
      funext M; unfold entropyBH area rS Lsq; field_simp <;> ring
    rw [this]
    convert (hasDerivAt_pow 2 M).const_mul (4 * π * kB * G / (hbar * c)) using 1
    field_simp <;> ring
  · rw [hawking_temperature hG hc hhbar hk hM]; field_simp <;> ring

/-- Smarr relation for the Schwarzschild exterior: M c² = 2 T S. -/
theorem smarr {M : ℝ} (hM : 0 < M) :
    M * c ^ 2 = 2 * hawkingT G c hbar kB M * entropyBH G c hbar kB M := by
  rw [hawking_temperature hG hc hhbar hk hM, entropy_eq hG hc hhbar hk hM]; field_simp <;> ring

/-- Negative heat capacity: T strictly decreases with M. -/
theorem temperature_antitone : StrictAntiOn (hawkingT G c hbar kB) (Ioi 0) := by
  intro M₁ h₁ M₂ h₂ hlt
  have h1 : (0:ℝ) < M₁ := h₁; have h2 : (0:ℝ) < M₂ := h₂
  rw [hawking_temperature hG hc hhbar hk h1, hawking_temperature hG hc hhbar hk h2]
  apply div_lt_div_of_pos_left (by positivity) (by positivity)
  have : 0 < 8 * π * G * kB := by positivity
  nlinarith

/-- One capacity bit per channel area a_ch = 4 ln2 · L*²: S/(k_B ln 2) = A / a_ch. -/
theorem bits_per_channel_area {M : ℝ} (hM : 0 < M) :
    entropyBH G c hbar kB M / (kB * Real.log 2) = area G c M / (4 * Real.log 2 * Lsq G c hbar) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 < Lsq G c hbar := by unfold Lsq; positivity
  unfold entropyBH; field_simp <;> ring

/-- Projected-area form of the quarter for the spherical horizon:
S/k_B = (mean projected area)/L*², and the sphere's projection is π r_s² = A/4. -/
theorem quarter_as_projection {M : ℝ} (hM : 0 < M) :
    entropyBH G c hbar kB M / kB = π * rS G c M ^ 2 / Lsq G c hbar ∧
      π * rS G c M ^ 2 = area G c M / 4 := by
  have hL : 0 < Lsq G c hbar := by unfold Lsq; positivity
  constructor
  · unfold entropyBH area; field_simp <;> ring
  · unfold area; ring

end Thermo

/-! ## Sec. 14  PPN: the exterior in isotropic coordinates has β = γ = 1 -/

section PPN

/-- r = ρ(1 + m/(2ρ))² maps the isotropic radius to the areal radius, and the lapse
and spatial factor take the isotropic form (exact identities, ρ > m/2 > 0). -/
theorem isotropic_form {m ρ : ℝ} (hρ : 0 < ρ) (hm : 0 < m) (hext : m < 2 * ρ) :
    let r := ρ * (1 + m / (2 * ρ)) ^ 2
    1 - 2 * m / r = ((1 - m / (2 * ρ)) / (1 + m / (2 * ρ))) ^ 2 ∧
    HasDerivAt (fun x => x * (1 + m / (2 * x)) ^ 2) ((1 + m / (2 * ρ)) * (1 - m / (2 * ρ))) ρ ∧
    ((1 + m / (2 * ρ)) * (1 - m / (2 * ρ))) ^ 2 / (1 - 2 * m / r) = (1 + m / (2 * ρ)) ^ 4 ∧
    r ^ 2 = ρ ^ 2 * (1 + m / (2 * ρ)) ^ 4 := by
  intro r
  have h1 : 2 * ρ + m ≠ 0 := by linarith
  have h2 : 2 * ρ - m ≠ 0 := by linarith
  have hr : r = (2 * ρ + m) ^ 2 / (4 * ρ) := by simp only [r]; field_simp <;> ring
  have hq : 1 - 2 * m / r = ((2 * ρ - m) / (2 * ρ + m)) ^ 2 := by
    rw [hr]; field_simp <;> ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hq]; field_simp
  · have h := (hasDerivAt_id ρ).fun_mul (((((hasDerivAt_inv hρ.ne').const_mul (m / 2))).const_add 1).fun_pow 2)
    have hfun : (fun x : ℝ => x * (1 + m / (2 * x)) ^ 2) = (fun x => id x * (1 + m / 2 * x⁻¹) ^ 2) := by
      funext x; simp only [id]; ring
    have hρ0 : ρ ≠ 0 := hρ.ne'
    rw [hfun]; convert h using 1; simp only [id]; norm_num; field_simp; ring
  · rw [hq]; field_simp <;> ring
  · simp only [r]; ring

/-- Lapse² in isotropic coordinates with U = m/ρ:
    ((1 − U/2)/(1 + U/2))² = ((2 − U)/(2 + U))² = 1 − 2U + 2U² − 2U³(3+U)/(2+U)², exactly. -/
theorem lapse_isotropic_expansion (U : ℝ) (hU : 2 + U ≠ 0) :
    ((1 - U / 2) / (1 + U / 2)) ^ 2 = 1 - 2 * U + 2 * U ^ 2 - 2 * U ^ 3 * (3 + U) / (2 + U) ^ 2 := by
  have h : (1 - U / 2) / (1 + U / 2) = (2 - U) / (2 + U) := by
    have : 1 + U / 2 ≠ 0 := by intro h; apply hU; linarith
    field_simp
  rw [h]
  field_simp <;> ring

/-- Spatial factor (1 + U/2)⁴ = 1 + 2U + (3/2)U² + U³/2 + U⁴/16 exactly. -/
theorem spatial_isotropic_expansion (U : ℝ) :
    (1 + U / 2) ^ 4 = 1 + 2 * U + 3/2 * U ^ 2 + U ^ 3 / 2 + U ^ 4 / 16 := by ring

/-- PPN β: −g₀₀ = 1 − 2U + 2βU² + O(U³) with β = 1. -/
theorem ppn_beta :
    Tendsto (fun U : ℝ => (((1 - U / 2) / (1 + U / 2)) ^ 2 - (1 - 2 * U)) / (2 * U ^ 2))
      (𝓝[≠] 0) (𝓝 1) := by
  have hloc : ∀ᶠ U in 𝓝 (0:ℝ), 2 + U ≠ 0 :=
    (continuous_const.add continuous_id).continuousAt.eventually_ne (by norm_num)
  have h : ∀ᶠ U in 𝓝[≠] (0:ℝ),
      (((1 - U / 2) / (1 + U / 2)) ^ 2 - (1 - 2 * U)) / (2 * U ^ 2) = 1 - U * (3 + U) / (2 + U) ^ 2 := by
    filter_upwards [self_mem_nhdsWithin, hloc.filter_mono nhdsWithin_le_nhds] with U hU hU2
    have hU0 : U ≠ 0 := hU
    rw [lapse_isotropic_expansion U hU2]; field_simp <;> ring
  rw [tendsto_congr' h]
  have hc : ContinuousAt (fun U : ℝ => 1 - U * (3 + U) / (2 + U) ^ 2) 0 := by
    apply ContinuousAt.sub continuousAt_const
    apply ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
  have := hc.tendsto
  simp at this
  exact this.mono_left nhdsWithin_le_nhds

/-- PPN γ: g_ij = (1 + 2γU + O(U²)) δ_ij with γ = 1. -/
theorem ppn_gamma :
    Tendsto (fun U : ℝ => ((1 + U / 2) ^ 4 - 1) / (2 * U)) (𝓝[≠] 0) (𝓝 1) := by
  have h : ∀ᶠ U in 𝓝[≠] (0:ℝ), ((1 + U / 2) ^ 4 - 1) / (2 * U) = 1 + 3/4 * U + U ^ 2 / 4 + U ^ 3 / 32 := by
    filter_upwards [self_mem_nhdsWithin] with U hU
    have : U ≠ 0 := hU
    field_simp <;> ring
  rw [tendsto_congr' h]
  have hc : Continuous (fun U : ℝ => 1 + 3/4 * U + U ^ 2 / 4 + U ^ 3 / 32) := by fun_prop
  have := hc.tendsto 0
  simp at this
  exact this.mono_left nhdsWithin_le_nhds

end PPN

end Entropic.BlackHole
