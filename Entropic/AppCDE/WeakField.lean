import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Appendix C/D/E weak-field bridge, electron anchor, transport (ledger C05-35, -37, -46,
-47, -48, -49, -51, -52, -56, -57, -59, -61, -66, -73, -74 … -79, -81). -/

noncomputable section
namespace Entropic.AppCDE
open Real

/-! ### Event volume and tetrahedral conversion (C05-35, -37) -/

/-- C05-35: N = m₄(V/v)^{1/4}, N L = cT and V = π(cT)⁴/24 give v = (π/24) m₄⁴ L⁴. -/
theorem event_volume {m4 L cT v : ℝ} (hm : 0 < m4) (hL : 0 < L) (hT : 0 < cT) (hv : 0 < v)
    (hN : cT / L = m4 * (Real.pi * cT ^ 4 / 24 / v) ^ (1/4 : ℝ)) :
    v = Real.pi / 24 * m4 ^ 4 * L ^ 4 := by
  have hx : 0 < Real.pi * cT ^ 4 / 24 / v := by positivity
  have h4 : ((Real.pi * cT ^ 4 / 24 / v) ^ (1/4 : ℝ)) ^ 4 = Real.pi * cT ^ 4 / 24 / v := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have := congrArg (· ^ 4) hN
  simp only [mul_pow, h4] at this
  field_simp at this
  nlinarith [this, pow_pos hL 4, pow_pos hT 4]

/-- C05-37: the regular tetrahedron with vertices s·(1,1,1), s·(1,−1,−1), s·(−1,1,−1),
s·(−1,−1,1) has edge a = 2√2 s; its edge-vector determinant is −16 so its volume
16s³/6 equals a³/(6√2), and its face area |(4,4,−4)s²|/2 equals (√3/4)a². -/
theorem tet_det : Matrix.det !![(0:ℝ), -2, -2; -2, 0, -2; -2, -2, 0] = -16 := by
  simp [Matrix.det_fin_three]; norm_num

theorem regular_tetrahedron (s : ℝ) (hs : 0 < s) :
    |(-16) * s ^ 3| / 6 = (2 * Real.sqrt 2 * s) ^ 3 / (6 * Real.sqrt 2) ∧
      Real.sqrt ((4 * s ^ 2) ^ 2 + (4 * s ^ 2) ^ 2 + (-4 * s ^ 2) ^ 2) / 2 =
        Real.sqrt 3 / 4 * (2 * Real.sqrt 2 * s) ^ 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2p : 0 < Real.sqrt 2 := by positivity
  constructor
  · rw [abs_of_neg (by nlinarith [pow_pos hs 3]),
      show (2 * Real.sqrt 2 * s) ^ 3 = 8 * s ^ 3 * Real.sqrt 2 ^ 2 * Real.sqrt 2 by ring, h2]
    field_simp; ring
  · rw [show (4 * s ^ 2) ^ 2 + (4 * s ^ 2) ^ 2 + (-4 * s ^ 2) ^ 2 = (4 * s ^ 2) ^ 2 * 3 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [mul_pow, mul_pow, h2]; ring

/-- C05-37 inverse: a_reg = (6√2 V)^{1/3} has a_reg³/(6√2) = V. -/
theorem areg_volume {V : ℝ} (hV : 0 < V) :
    ((6 * Real.sqrt 2 * V) ^ (1/3 : ℝ)) ^ 3 / (6 * Real.sqrt 2) = V := by
  have hx : 0 < 6 * Real.sqrt 2 * V := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num

/-! ### Weak-field bridge (C05-46, -47, -48, -49, -51, -52) -/

/-- C05-46: δS = αΦ maps the capacity action −(γ/2)X + κρδS onto Z·(−X/(8πG) − ρΦ)
(X = |∇Φ|²) for all X, ρ, Φ iff α = −2S_∞/c² and Z = 2κS_∞/c², given the bridge
G = c²κ/(8πγS_∞). -/
theorem bridge_unique {c κ γ S α Z : ℝ} (hc : c ≠ 0) (hκ : κ ≠ 0) (hγ : γ ≠ 0) (hS : S ≠ 0)
    (hα : α ≠ 0) :
    (∀ X ρ Φ : ℝ, -(γ/2) * (α ^ 2 * X) + κ * ρ * (α * Φ) =
        Z * (-X / (8 * Real.pi * (c ^ 2 * κ / (8 * Real.pi * γ * S))) - ρ * Φ)) ↔
      (α = -2 * S / c ^ 2 ∧ Z = 2 * κ * S / c ^ 2) := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  constructor
  · intro h
    have hρ := h 0 1 1
    have hX := h 1 0 0
    have hZ : Z = -κ * α := by simp at hρ; linarith
    rw [hZ] at hX
    field_simp at hX
    have h3 : γ * (α * c ^ 2 + 2 * S) = 0 := by linear_combination (-1:ℝ) * hX
    have h4 : α * c ^ 2 + 2 * S = 0 := (mul_eq_zero.mp h3).resolve_left hγ
    have hα' : α = -2 * S / c ^ 2 := by field_simp; linarith
    refine ⟨hα', ?_⟩
    rw [hZ, hα']; ring
  · rintro ⟨rfl, rfl⟩ X ρ Φ
    field_simp; ring

/-- C05-47: the bounded lapse q = 1 + 2Φ/c² matches e^{2Φ/c²} in value and slope at Φ = 0,
vanishes at Φ = −c²/2 (δS = S_∞), while the exponential never vanishes. -/
theorem bounded_lapse {c : ℝ} (hc : c ≠ 0) :
    (1 + 2 * 0 / c ^ 2 = Real.exp (2 * 0 / c ^ 2)) ∧
      HasDerivAt (fun Φ => 1 + 2 * Φ / c ^ 2) (2 / c ^ 2) 0 ∧
      HasDerivAt (fun Φ => Real.exp (2 * Φ / c ^ 2)) (2 / c ^ 2) 0 ∧
      1 + 2 * (-c ^ 2 / 2) / c ^ 2 = 0 ∧ ∀ Φ, Real.exp (2 * Φ / c ^ 2) ≠ 0 := by
  refine ⟨by simp, ?_, ?_, by field_simp; ring, fun Φ => (Real.exp_pos _).ne'⟩
  · have := ((hasDerivAt_id (0:ℝ)).const_mul 2).div_const (c ^ 2) |>.const_add 1
    simpa using this
  · have h := (((hasDerivAt_id (0:ℝ)).const_mul 2).div_const (c ^ 2)).exp
    simpa using h

/-- C05-48: δS = k/r is radially harmonic for r > 0 ((r²δS′)′ = 0), and its flux through
every sphere is −4πr²δS′(r) = 4πk; with k = κM/(4πγ) the flux is κM/γ (Gauss form of
∇²δS = −(κ/γ)Mδ³). -/
theorem point_source {k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun r => k / r) (-k / r ^ 2) r ∧
      HasDerivAt (fun r => r ^ 2 * (-k / r ^ 2)) 0 r ∧
      -(4 * Real.pi * r ^ 2 * (-k / r ^ 2)) = 4 * Real.pi * k := by
  have hr0 : r ≠ 0 := hr.ne'
  refine ⟨?_, ?_, by field_simp⟩
  · have := (hasDerivAt_inv hr0).const_mul k
    convert this using 1
    · funext x; rw [div_eq_mul_inv]
    · field_simp
  · have hc : (fun r : ℝ => r ^ 2 * (-k / r ^ 2)) =ᶠ[nhds r] fun _ => -k := by
      filter_upwards [eventually_ne_nhds hr0] with x hx
      field_simp
    exact (hasDerivAt_const r (-k)).congr_of_eventuallyEq hc

/-- C05-49: Φ = −c²δS/(2S_∞) with δS = κM/(4πγr) and G = c²κ/(8πγS_∞) is Φ = −GM/r,
whose inward acceleration is −dΦ/dr = −GM/r²·(−1)… i.e. magnitude GM/r². -/
theorem newton_acceleration {c κ γ S M r : ℝ} (hc : c ≠ 0) (hγ : γ ≠ 0) (hS : S ≠ 0)
    (hr : 0 < r) :
    let G := c ^ 2 * κ / (8 * Real.pi * γ * S)
    (∀ x, -c ^ 2 * (κ * M / (4 * Real.pi * γ * x)) / (2 * S) = -(G * M) / x) ∧
      HasDerivAt (fun x => -(G * M) / x) (G * M / r ^ 2) r := by
  intro G
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  refine ⟨fun x => ?_, ?_⟩
  · by_cases hx : x = 0
    · subst hx; simp
    · simp only [G]; field_simp; ring
  · have := (hasDerivAt_inv hr.ne').const_mul (-(G * M))
    convert this using 1
    · funext x; rw [div_eq_mul_inv]
    · field_simp

/-- C05-51: halo density. If F(s) = s²Δg(s) has continuous derivative F′ on [0, r] and
ρ_halo = F′/(4πG s²), then M_halo(r) = ∫₀ʳ 4πs²ρ_halo ds = F(r)/G, so G M_halo/r² = Δg(r). -/
theorem halo_density {G r : ℝ} (hG : G ≠ 0) (hr : 0 < r) (Δg F' : ℝ → ℝ)
    (hF : ∀ s, HasDerivAt (fun s => s ^ 2 * Δg s) (F' s) s) (hc : Continuous F') :
    G * (∫ s in (0:ℝ)..r, F' s / G) / r ^ 2 = Δg r := by
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hF s) (hc.intervalIntegrable _ _)]
  have : r ^ 2 ≠ 0 := by positivity
  field_simp; ring

/-- The local density form: 4πs²·F′/(4πGs²) = F′/G for s ≠ 0. -/
theorem halo_integrand {G s F' : ℝ} (hs : s ≠ 0) :
    4 * Real.pi * s ^ 2 * (F' / (4 * Real.pi * G * s ^ 2)) = F' / G := by
  by_cases hG : G = 0
  · subst hG; simp
  · have hp : Real.pi ≠ 0 := Real.pi_ne_zero; field_simp

/-- C05-52: κ_m(ℓ) = κ_UV(L/ℓ) with κ_UV = ħ/(cL ln 2) is independent of L and equals
m_e/ln 2 at the reduced Compton length ℓ = ħ/(m_e c). -/
theorem mass_entropy_anchor {ħ c L me : ℝ} (hħ : 0 < ħ) (hc : 0 < c) (hL : 0 < L) (hm : 0 < me) :
    ħ / (c * L * Real.log 2) * (L / (ħ / (me * c))) = me / Real.log 2 := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp

/-! ### Electron anchor (C05-56, -57, -59, -61, -73) -/

/-- C05-56: E_e = −(3ħZ/(2τ_*))ln(1−p) = m_e c² = ħ/τ_e solves to τ_* = −(3/2)Zτ_e ln(1−p),
and L_* = cτ_*, λ_e = cτ_e give L_* = −(3/2)Zλ_e ln(1−p). -/
theorem electron_tick {ħ Z τ τe p c : ℝ} (hħ : ħ ≠ 0) (hτ : τ ≠ 0) (hτe : τe ≠ 0)
    (h : -(3 * ħ * Z / (2 * τ)) * Real.log (1 - p) = ħ / τe) :
    τ = -(3/2) * Z * τe * Real.log (1 - p) ∧
      c * τ = -(3/2) * Z * (c * τe) * Real.log (1 - p) := by
  have : τ = -(3/2) * Z * τe * Real.log (1 - p) := by
    field_simp at h; linarith
  exact ⟨this, by rw [this]; ring⟩

/-- First-order log enclosure: r ≤ −ln(1−r) ≤ r/(1−r) for 0 ≤ r < 1. -/
theorem neglog_bounds {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    r ≤ -Real.log (1 - r) ∧ -Real.log (1 - r) ≤ r / (1 - r) := by
  have hp : 0 < 1 - r := by linarith
  constructor
  · have := Real.log_le_sub_one_of_pos hp; linarith
  · have := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
    rw [Real.log_inv] at this
    have e : (1 - r)⁻¹ - 1 = r / (1 - r) := by field_simp; ring
    linarith

/-- Second-order: |−ln(1−r) − r − r²/2| ≤ 2r³ for 0 ≤ r ≤ 1/2. -/
theorem neglog_second {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1/2) :
    |-Real.log (1 - r) - r - r ^ 2 / 2| ≤ 2 * r ^ 3 := by
  have hr : |r| < 1 := by rw [abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hr 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_of_nonneg h0] at h
  norm_num at h
  have e : |-Real.log (1 - r) - r - r ^ 2 / 2| = |r + r ^ 2 / 2 + Real.log (1 - r)| := by
    rw [← abs_neg]; ring_nf
  rw [e]
  refine le_trans h ?_
  rw [div_le_iff₀ (by linarith)]; nlinarith [pow_nonneg h0 3]

/-- C05-57, -59, -73: with u = −ln(1−r), L_* = (3/2)Zλ_e u = (3/2)Zλ_e r(1+O(r)):
0 ≤ u/r − 1 ≤ 2r, and r/u = 1 − r/2 + O(r²) with |r/u − 1 + r/2| ≤ 3r² (0 < r ≤ 1/2). -/
theorem anchor_expansion {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1/2) :
    0 ≤ -Real.log (1 - r) / r - 1 ∧ -Real.log (1 - r) / r - 1 ≤ 2 * r ∧
      |r / (-Real.log (1 - r)) - 1 + r / 2| ≤ 3 * r ^ 2 := by
  obtain ⟨a, b⟩ := neglog_bounds h0.le (by linarith)
  have hu : 0 < -Real.log (1 - r) := lt_of_lt_of_le h0 a
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_nonneg, le_div_iff₀ h0]; linarith
  · rw [sub_le_iff_le_add, div_le_iff₀ h0]
    have : r / (1 - r) ≤ r + 2 * r ^ 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    nlinarith
  · have h2 := neglog_second h0.le h1
    set u := -Real.log (1 - r)
    obtain ⟨e1, e2⟩ := abs_le.mp h2
    have : r / u - 1 + r / 2 = (r - u + r * u / 2) / u := by field_simp
    rw [this, abs_div, abs_of_pos hu, div_le_iff₀ hu, abs_le]
    constructor <;> nlinarith [pow_pos h0 3, pow_pos h0 2, mul_pos h0 hu]

/-- C05-59, -73: λ_e/L_* = 2/(3Z u) = N_eff · r/u with N_eff = (2/(3Z))/r, and
= (1/Z)·dim_eff,⊥·r/u with dim_eff,⊥ = (2/3)/r. -/
theorem support_scale {Z lam r u : ℝ} (hZ : Z ≠ 0) (hl : lam ≠ 0) (hr : r ≠ 0) (hu : u ≠ 0) :
    lam / ((3/2) * Z * lam * u) = 2 / (3 * Z * u) ∧
      2 / (3 * Z * u) = (2 / (3 * Z) / r) * (r / u) ∧
      2 / (3 * Z * u) = (1 / Z) * ((2/3) / r) * (r / u) := by
  refine ⟨by field_simp, by field_simp, by field_simp⟩

/-- C05-61: ln(λ_e/L_*) = 7g − ln(3/2) − ln Z_e − ln(u/r) with r = e^{−7g}, and the remainder
ln(u/r) lies in [0, 2r]. -/
theorem log_ratio {g Z : ℝ} (hZ : 0 < Z) (hg : 0 < g) (hr : Real.exp (-7 * g) ≤ 1/2) :
    let r := Real.exp (-7 * g)
    let u := -Real.log (1 - r)
    Real.log (2 / (3 * Z * u)) = 7 * g - Real.log (3/2) - Real.log Z - Real.log (u / r) ∧
      0 ≤ Real.log (u / r) ∧ Real.log (u / r) ≤ 2 * r := by
  intro r u
  have hr0 : 0 < r := Real.exp_pos _
  obtain ⟨a1, a2, -⟩ := anchor_expansion hr0 hr
  have hu : 0 < u := lt_of_lt_of_le hr0 (neglog_bounds hr0.le (by linarith)).1
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.log_div (by norm_num) (by positivity), Real.log_mul (by positivity) hu.ne',
      Real.log_mul (by norm_num) hZ.ne', Real.log_div hu.ne' hr0.ne']
    have : Real.log r = -7 * g := Real.log_exp _
    rw [this, Real.log_div (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
    ring
  · apply Real.log_nonneg; rw [le_div_iff₀ hr0]; linarith [(neglog_bounds hr0.le (by linarith)).1]
  · have hpos : 0 < u / r := by positivity
    have := Real.log_le_sub_one_of_pos hpos
    linarith

/-! ### Closure saturation (C05-66) -/

theorem closure_saturation {η m : ℝ} (hη : 0 < η) (h : m = 3 / (2 * η)) :
    η * m = 3/2 ∧ (η * m)⁻¹ = 2/3 := by
  subst h; constructor <;> field_simp <;> norm_num

/-! ### Telegrapher transport (C05-74 … -79, -81) -/

/-- C05-74: the plane wave e^{−iωt}·e^{ik·x} solves τ∂ₜ²δs + ∂ₜδs − D∇²δs = 0 iff
τω² + iω − D|k|² = 0. The time factor satisfies ∂ₜ = −iω, ∂ₜ² = −ω²; the spatial factor
∇² = −|k|². -/
theorem plane_wave_dispersion (τ D k2 : ℝ) (ω : ℂ) (E : ℂ) (hE : E ≠ 0) :
    (τ * ((-Complex.I * ω) ^ 2 * E) + (-Complex.I * ω) * E - D * (-(k2 : ℂ) * E) = 0) ↔
      (τ * ω ^ 2 + Complex.I * ω - D * k2 = 0) := by
  constructor
  · intro h
    have : (-(τ * ω ^ 2 + Complex.I * ω - D * k2)) * E = 0 := by
      rw [← h]; ring_nf; rw [Complex.I_sq]; ring
    rcases mul_eq_zero.mp this with h1 | h1
    · exact neg_eq_zero.mp h1
    · exact absurd h1 hE
  · intro h
    have : τ * ((-Complex.I * ω) ^ 2 * E) + (-Complex.I * ω) * E - D * (-(k2 : ℂ) * E) =
        -(τ * ω ^ 2 + Complex.I * ω - D * k2) * E := by ring_nf; rw [Complex.I_sq]; ring
    rw [this, h]; simp

theorem time_factor_deriv (ω : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (-Complex.I * ω * t)) (-Complex.I * ω * Complex.exp (-Complex.I * ω * t)) t := by
  have h := ((hasDerivAt_id (t : ℂ)).const_mul (-Complex.I * ω)).cexp
  have := h.comp_ofReal (z := t)
  simpa [mul_comm] using this

/-- C05-75: every root ω of τω² + iω − D|k|² = 0 (τ, D > 0) has Im ω ≤ 0, with Im ω = 0
only for k = 0 and ω = 0; hence |e^{−iωt}| = e^{t Im ω} is non-increasing. -/
theorem telegrapher_stable {τ D k2 : ℝ} (hτ : 0 < τ) (hD : 0 < D) (hk : 0 ≤ k2) {ω : ℂ}
    (h : τ * ω ^ 2 + Complex.I * ω - D * k2 = 0) :
    ω.im ≤ 0 ∧ (ω.im = 0 → k2 = 0 ∧ ω = 0) := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [sq, Complex.mul_re, Complex.mul_im] at hre him
  -- him: τ(2 a b) + a = 0 ; hre: τ(a² − b²) − b − D k2 = 0
  set a := ω.re; set b := ω.im
  have hab : a * (2 * τ * b + 1) = 0 := by linarith
  rcases mul_eq_zero.mp hab with ha | hb
  · rw [ha] at hre
    have hq : b * (τ * b + 1) = -(D * k2) := by nlinarith
    have hDk : 0 ≤ D * k2 := by positivity
    refine ⟨?_, fun hb0 => ?_⟩
    · by_contra hpos; push_neg at hpos
      have : 0 < b * (τ * b + 1) := by have := mul_pos hτ hpos; positivity
      linarith
    · rw [hb0] at hq
      have : k2 = 0 := by
        have : D * k2 = 0 := by linarith
        rcases mul_eq_zero.mp this with h1 | h1
        · exact absurd h1 hD.ne'
        · exact h1
      exact ⟨this, Complex.ext ha hb0⟩
  · have : b = -1 / (2 * τ) := by field_simp; linarith
    refine ⟨by rw [this]; apply div_nonpos_of_nonpos_of_nonneg <;> linarith, fun hb0 => ?_⟩
    rw [this] at hb0; field_simp at hb0; norm_num at hb0

theorem decay_modulus (ω : ℂ) (t : ℝ) : ‖Complex.exp (-Complex.I * ω * t)‖ = Real.exp (ω.im * t) := by
  rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]

/-- C05-76: the principal symbol τ∂ₜ² − D∇² has speed √(D/τ); it equals c > 0 iff D/τ = c²,
and with τ = 1/H₀ this is D = c²/H₀. -/
theorem characteristic_speed {τ D c H0 : ℝ} (hτ : 0 < τ) (hD : 0 < D) (hc : 0 < c) (hH : 0 < H0) :
    (Real.sqrt (D / τ) = c ↔ D / τ = c ^ 2) ∧ (τ = 1 / H0 → D / τ = c ^ 2 → D = c ^ 2 / H0) := by
  constructor
  · constructor
    · intro h; rw [← h, Real.sq_sqrt (by positivity)]
    · intro h; rw [h, Real.sqrt_sq hc.le]
  · intro h1 h2; rw [h1] at h2; field_simp at h2 ⊢; linarith

/-- C05-78: for 4τDk² > 1 the roots of τs² + s + Dk² are −1/(2τ) ± iω_k with
ω_k = √(4τDk² − 1)/(2τ). -/
theorem underdamped_roots {τ D k2 : ℝ} (hτ : 0 < τ) (h : 1 < 4 * τ * D * k2) (sgn : ℝ)
    (hs : sgn = 1 ∨ sgn = -1) :
    let ωk := Real.sqrt (4 * τ * D * k2 - 1) / (2 * τ)
    let s : ℂ := -1 / (2 * τ) + sgn * Complex.I * ωk
    (τ : ℂ) * s ^ 2 + s + D * k2 = 0 := by
  intro ωk s
  have hsq : Real.sqrt (4 * τ * D * k2 - 1) ^ 2 = 4 * τ * D * k2 - 1 := Real.sq_sqrt (by linarith)
  have hsg : sgn ^ 2 = 1 := by rcases hs with h | h <;> simp [h]
  have hτ0 : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hω2 : ωk ^ 2 = (4 * τ * D * k2 - 1) / (4 * τ ^ 2) := by
    simp only [ωk]; rw [div_pow, hsq]; ring
  have hωC : ((ωk : ℝ) : ℂ) ^ 2 = (((4 * τ * D * k2 - 1) / (4 * τ ^ 2) : ℝ) : ℂ) := by
    rw [← hω2]; push_cast; ring
  have hsgC : ((sgn : ℝ) : ℂ) ^ 2 = 1 := by exact_mod_cast hsg
  set ε : ℂ := (sgn : ℂ) * Complex.I * (ωk : ℂ) with hε_def
  have hε : ε ^ 2 = -((ωk : ℂ) ^ 2) := by
    rw [hε_def, mul_pow, mul_pow, Complex.I_sq, hsgC]; ring
  have hs' : s = -1 / (2 * (τ : ℂ)) + ε := by simp only [s, hε_def]
  rw [hs']
  have : (τ : ℂ) * (-1 / (2 * τ) + ε) ^ 2 + (-1 / (2 * τ) + ε) + D * k2 =
      (τ : ℂ) * ε ^ 2 - 1 / (4 * τ) + D * k2 := by field_simp; ring
  rw [this, hε, hωC]; push_cast; field_simp; ring

/-- ω_k = ck√(1 − 1/(4τDk²)) when D/τ = c², so ω_k/(ck) → 1 as k → ∞. -/
theorem omega_over_ck {τ D c : ℝ} (hτ : 0 < τ) (hD : 0 < D) (hc : 0 < c) (hDc : D / τ = c ^ 2) :
    Filter.Tendsto (fun k : ℝ => Real.sqrt (4 * τ * D * k ^ 2 - 1) / (2 * τ) / (c * k))
      Filter.atTop (nhds 1) := by
  have hD' : D = c ^ 2 * τ := by field_simp at hDc; linarith
  have key : ∀ k > 0, Real.sqrt (4 * τ * D * k ^ 2 - 1) / (2 * τ) / (c * k) =
      Real.sqrt (1 - 1 / (4 * τ * D * k ^ 2)) := by
    intro k hk
    have hB : 0 < 2 * τ * c * k := by positivity
    rw [div_div, show 2 * τ * (c * k) = Real.sqrt ((2 * τ * c * k) ^ 2) by
      rw [Real.sqrt_sq hB.le]; ring, ← Real.sqrt_div' _ (by positivity)]
    congr 1; rw [hD']; field_simp; ring
  have h1 : Filter.Tendsto (fun k : ℝ => 4 * τ * D * k ^ 2) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop two_ne_zero).const_mul_atTop (by positivity)
  have h2 : Filter.Tendsto (fun k : ℝ => 1 / (4 * τ * D * k ^ 2)) Filter.atTop (nhds 0) := by
    refine (tendsto_inv_atTop_zero.comp h1).congr ?_
    intro k; simp [one_div]
  have h3 : Filter.Tendsto (fun k : ℝ => Real.sqrt (1 - 1 / (4 * τ * D * k ^ 2))) Filter.atTop
      (nhds 1) := by
    have h3' := (Real.continuous_sqrt.tendsto (1 - 0)).comp ((tendsto_const_nhds (x := (1:ℝ))).sub h2)
    rw [sub_zero, Real.sqrt_one] at h3'
    exact h3'
  refine h3.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with k hk
  exact (key k hk).symm

/-- C05-79: 4τDk_c² = 1 with τ = 1/H₀, D = c²/H₀ gives k_c = H₀/(2c) and
λ_c = 2π/k_c = 4πc/H₀; for H₀ = 67.4 km/s/Mpc, λ_c ∈ (55.8, 56.0) Gpc. -/
theorem critical_wavelength {c H0 : ℝ} (hc : 0 < c) (hH : 0 < H0) :
    4 * (1 / H0) * (c ^ 2 / H0) * (H0 / (2 * c)) ^ 2 = 1 ∧
      2 * Real.pi / (H0 / (2 * c)) = 4 * Real.pi * c / H0 := by
  constructor <;> field_simp <;> ring

theorem lambda_c_numeric :
    55.8 < 4 * Real.pi * (299792.458 / 67.4) / 1000 ∧ 4 * Real.pi * (299792.458 / 67.4) / 1000 < 56.0 := by
  have := Real.pi_gt_d4; have := Real.pi_lt_d4; constructor <;> nlinarith

/-- C05-77: a time-independent solution of τ∂ₜ²δS + ∂ₜδS = D∇²δS + Aχ with A/D = κ/γ obeys
∇²δS = −(κ/γ)χ. -/
theorem static_limit {D A kg lap χ : ℝ} (hD : D ≠ 0) (hA : A / D = kg)
    (h : (0:ℝ) + 0 = D * lap + A * χ) : lap = -(kg * χ) := by
  rw [← hA]; field_simp; linarith

/-- C05-81: the trace source −ρc² + 3p vanishes for radiation p = ρc²/3. -/
theorem radiation_trace (ρ c : ℝ) : -ρ * c ^ 2 + 3 * (ρ * c ^ 2 / 3) = 0 := by ring

end Entropic.AppCDE
