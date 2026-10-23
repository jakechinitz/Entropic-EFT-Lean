import Entropic.AppCDE.Frame
import Entropic.ClosureRoot
import Entropic.EFT.Edge.Kernel
import Entropic.EFT.Edge.SourceProjection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Appendix C: edge kernel numbers, continuum matching and the source/stiffness ratio
(ledger C05-03, -04, -08, -12, -13, -14, -19, -25, -27, -28, -29, -30, -82). -/

noncomputable section
namespace Entropic.AppCDE
open Entropic.FiniteModel Entropic.ClosureRoot Entropic.EFT.Edge

/-! ### Kernel numbers at the closure root (C05-03, -04, -08, -14) -/

theorem eta_bracket {η : ℝ} (h : ClosureStationary η) :
    (298668443934 / 10 ^ 13 : ℝ) < η ∧ η < 298668443936 / 10 ^ 13 := by
  have := stationary_bracket h; unfold etaLo etaHi at this; exact this

/-- J_bare = (2/3)η* = 0.0199112296 (10 significant digits). -/
theorem Jbare_value {η : ℝ} (h : ClosureStationary η) :
    0.01991122955 < Jbare η ∧ Jbare η < 0.01991122965 := by
  obtain ⟨a, b⟩ := eta_bracket h; unfold Jbare; constructor <;> linarith

/-- J_tree = J_bare/(z−1) = 2η*/9 = 0.0066370765. -/
theorem Jtree_value {η : ℝ} (h : ClosureStationary η) :
    0.00663707645 < Jtree η ∧ Jtree η < 0.00663707655 := by
  obtain ⟨a, b⟩ := eta_bracket h; rw [Jtree_closed]; constructor <;> linarith

/-- Dyson dressing: c_loop = 1/(1 + J_tree Σ_ret) = 0.95426, J_ren = 0.00633348. -/
theorem loop_values {η : ℝ} (h : ClosureStationary η) :
    0.954255 < loopFactor η ∧ loopFactor η < 0.954265 ∧
      0.006333475 < Jren η ∧ Jren η < 0.006333485 := by
  obtain ⟨a, b⟩ := eta_bracket h
  have hS := SigmaReturn_closed
  have hJ := Jtree_closed η
  have hpos : 0 < 1 + Jtree η * SigmaReturn := by rw [hS, hJ]; nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold loopFactor; rw [lt_div_iff₀ hpos, hS, hJ]; nlinarith
  · unfold loopFactor; rw [div_lt_iff₀ hpos, hS, hJ]; nlinarith
  · unfold Jren; rw [lt_div_iff₀ hpos, hS, hJ]; nlinarith
  · unfold Jren; rw [div_lt_iff₀ hpos, hS, hJ]; nlinarith

theorem Jren_pos {η : ℝ} (hη : 0 < η) : 0 < Jren η := by
  unfold Jren; rw [Jtree_closed, SigmaReturn_closed]; positivity

/-- 4J_ren/(3π²) = 8.556e-4, so γ ≈ 8.556·10⁻⁴ c⁴/G_*. -/
theorem gamma_coefficient {η : ℝ} (h : ClosureStationary η) :
    8.5555e-4 < 4 * Jren η / (3 * Real.pi ^ 2) ∧ 4 * Jren η / (3 * Real.pi ^ 2) < 8.5570e-4 := by
  obtain ⟨-, -, j1, j2⟩ := loop_values h
  have p1 := Real.pi_gt_d6; have p2 := Real.pi_lt_d6
  have q1 : (3.141592:ℝ) ^ 2 < Real.pi ^ 2 := pow_lt_pow_left₀ p1 (by norm_num) (by norm_num)
  have q2 : Real.pi ^ 2 < (3.141593:ℝ) ^ 2 := pow_lt_pow_left₀ p2 (by positivity) (by norm_num)
  have hp : 0 < 3 * Real.pi ^ 2 := by positivity
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

/-! ### Continuum matching (C05-12, -13, -14, -82) -/

/-- C05-12: per primitive cell the four bonds give Σ_i (L d_i·v)² = (4/3)L²|v|², and dividing
by ΔV₄ = L⁴/c gives ħ(J/2)Σ(...)/ΔV₄ = (γ_Q/2)|v|² with γ_Q = 4ħcJ/(3L²). -/
theorem gammaQ_from_lattice (ħ c J L : ℝ) (hL : L ≠ 0) (hc : c ≠ 0) (v : Fin 3 → ℝ) :
    ħ * (J / 2) * (∑ i, (∑ a, (L * d i a) * v a) ^ 2) / (L ^ 4 / c) =
      (4 * ħ * c * J / (3 * L ^ 2)) / 2 * ∑ a, v a ^ 2 := by
  have : ∑ i, (∑ a, (L * d i a) * v a) ^ 2 = L ^ 2 * ∑ i, (∑ a, d i a * v a) ^ 2 := by
    rw [Finset.mul_sum]; congr 1; ext i
    rw [show ∑ a, L * d i a * v a = L * ∑ a, d i a * v a by rw [Finset.mul_sum]; congr 1; ext; ring]
    ring
  rw [this, frame_quadratic]; field_simp

/-- C05-13: with S = πQ, (γ/2)(∇S)² = (γ_Q/2)(∇Q)² for all gradients iff γ = γ_Q/π²; this is
the library's `gammaStiffness`. -/
theorem gamma_from_gammaQ (ħ c L η : ℝ) :
    gammaStiffness ħ c L η = (4 * ħ * c * Jren η / (3 * L ^ 2)) / Real.pi ^ 2 ∧
      ∀ γ γQ : ℝ, (∀ X : ℝ, γ / 2 * (Real.pi * X) ^ 2 = γQ / 2 * X ^ 2) ↔ γ = γQ / Real.pi ^ 2 := by
  refine ⟨by unfold gammaStiffness; field_simp, fun γ γQ => ⟨fun h => ?_, fun h X => ?_⟩⟩
  · have := h 1; have hp : Real.pi ^ 2 ≠ 0 := by positivity
    field_simp; nlinarith [this]
  · rw [h]; have hp : Real.pi ≠ 0 := Real.pi_ne_zero; field_simp

/-- C05-14: ħc/L² = c⁴/G_* with G_* = c³L²/ħ. -/
theorem hbar_c_over_L2 (ħ c L : ℝ) (hħ : ħ ≠ 0) (hc : c ≠ 0) (hL : L ≠ 0) :
    ħ * c / L ^ 2 = c ^ 4 / (c ^ 3 * L ^ 2 / ħ) := by field_simp

/-- C05-82: γ > 0. -/
theorem gamma_pos {ħ c L η : ℝ} (hħ : 0 < ħ) (hc : 0 < c) (hL : 0 < L) (hη : 0 < η) :
    0 < gammaStiffness ħ c L η := by
  unfold gammaStiffness; have := Jren_pos hη; positivity

/-! ### Dihedral angle (C05-19) -/

theorem cos_two_pi_div_five : Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
  have h := Real.cos_pi_div_five
  rw [show 2 * Real.pi / 5 = 2 * (Real.pi / 5) by ring, Real.cos_two_mul, h]
  have : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  ring_nf; rw [this]; ring

/-- θ = arccos(1/3) satisfies 5θ < 2π < 6θ, so no integer number of regular tetrahedra
closes around an edge. -/
theorem dihedral_not_divisor :
    5 * Real.arccos (1/3) < 2 * Real.pi ∧ 2 * Real.pi < 6 * Real.arccos (1/3) ∧
      ∀ k : ℕ, (k : ℝ) * Real.arccos (1/3) ≠ 2 * Real.pi := by
  have hs : Real.sqrt 5 < 2.237 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  -- cos(2π/5) < 1/3 < 1/2 = cos(π/3), and arccos is antitone
  have h1 : Real.arccos (1/3) < 2 * Real.pi / 5 := by
    have hc : Real.cos (2 * Real.pi / 5) < 1/3 := by rw [cos_two_pi_div_five]; linarith
    have hpos : 0 ≤ 2 * Real.pi / 5 := by positivity
    have hle : 2 * Real.pi / 5 ≤ Real.pi := by linarith [Real.pi_pos]
    have hm : -1 ≤ Real.cos (2 * Real.pi / 5) := Real.neg_one_le_cos _
    calc Real.arccos (1/3) < Real.arccos (Real.cos (2 * Real.pi / 5)) :=
          Real.arccos_lt_arccos hm hc (by norm_num)
      _ = 2 * Real.pi / 5 := Real.arccos_cos hpos hle
  have h2 : Real.pi / 3 < Real.arccos (1/3) := by
    have : Real.arccos (1/2) = Real.pi / 3 := by
      rw [show (1:ℝ)/2 = Real.cos (Real.pi / 3) by rw [Real.cos_pi_div_three]]
      exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
    rw [← this]; exact Real.arccos_lt_arccos (by norm_num) (by norm_num) (by norm_num)
  refine ⟨by linarith, by linarith, fun k hk => ?_⟩
  have hθ : 0 < Real.arccos (1/3) := by linarith [Real.pi_pos]
  have k5 : (5:ℝ) < k := by
    by_contra hc; push_neg at hc
    have : (k:ℝ) * Real.arccos (1/3) ≤ 5 * Real.arccos (1/3) := mul_le_mul_of_nonneg_right hc hθ.le
    linarith
  have k6 : (k:ℝ) < 6 := by
    by_contra hc; push_neg at hc
    have : 6 * Real.arccos (1/3) ≤ (k:ℝ) * Real.arccos (1/3) := mul_le_mul_of_nonneg_right hc hθ.le
    linarith
  have : 5 < k := by exact_mod_cast k5
  have : k < 6 := by exact_mod_cast k6
  omega

/-! ### Source/stiffness matching and Newton constant (C05-25, -27, -28, -29, -30) -/

/-- C05-25: δQ_def = ln(7/6)/π and s_def = J_ren δQ/G give s_def/J_ren = ln(7/6)/(π G). -/
theorem source_amplitude (J G : ℝ) (hJ : J ≠ 0) (hG : G ≠ 0) :
    (J * (Real.log (7/6) / Real.pi) / G) / J = Real.log (7/6) / (Real.pi * G) := by
  field_simp

/-- C05-27: if ∇²δS = −(κ/γ)ρ and ∇²δS = −(3L/(4G κ_m))ρ for all ρ, then
κ/γ = 3L/(4 G κ_m), independent of J_ren. -/
theorem kappa_over_gamma (kg L G km : ℝ)
    (h : ∀ ρ : ℝ, -(kg * ρ) = -(3 * L / (4 * G * km) * ρ)) : kg = kappaOverGamma L G km := by
  have := h 1; unfold kappaOverGamma; linarith

/-- C05-28: G = c²(κ/γ)/(8πS_∞) with κ/γ = 3L/(4Gκ_m) and κ_m = ħ/(cL ln 2) gives
G = (c³L²/ħ)·3 ln 2/(32π G_tet S_∞). -/
theorem newton_from_bridge (c ħ L Gt S : ℝ) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hL : L ≠ 0)
    (hG : Gt ≠ 0) (hS : S ≠ 0) :
    c ^ 2 * kappaOverGamma L Gt (ħ / (c * L * Real.log 2)) / (8 * Real.pi * S) =
      (c ^ 3 * L ^ 2 / ħ) * (3 * Real.log 2 / (32 * Real.pi * Gt * S)) := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold kappaOverGamma; field_simp; ring

/-- C05-29: G/G_* = S₀/S_∞ with S₀ = SInfCell G_tet, so G = G_* iff S_∞ = S₀. -/
theorem G_over_Gstar (Gs Gt S : ℝ) (hGs : Gs ≠ 0) (hS : S ≠ 0) (hGt : Gt ≠ 0) :
    (Gs * (3 * Real.log 2 / (32 * Real.pi * Gt * S))) / Gs = SInfCell Gt / S ∧
      (Gs * (3 * Real.log 2 / (32 * Real.pi * Gt * S)) = Gs ↔ S = SInfCell Gt) := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hS0 : SInfCell Gt ≠ 0 := by unfold SInfCell; positivity
  constructor
  · unfold SInfCell; field_simp
  · unfold SInfCell; constructor
    · intro h; field_simp at h ⊢; linarith
    · intro h; rw [h]; field_simp

/-- C05-30: entropy-unit change γ′ = γ/b², κ′ = κ/b, S′ = bS leaves κ/(γS) fixed, and
S_∞ = βS₀ gives G = G_*/β. -/
theorem entropy_unit (b κ γ S Gs β : ℝ) (hb : b ≠ 0) (hγ : γ ≠ 0) (hS : S ≠ 0) (hβ : β ≠ 0) :
    (κ / b) / ((γ / b ^ 2) * (b * S)) = κ / (γ * S) ∧ Gs * (1 / β) = Gs / β := by
  constructor
  · field_simp
  · ring

end Entropic.AppCDE
