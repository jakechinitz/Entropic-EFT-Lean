import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.Sym.Card
import Mathlib.Tactic

/-! Appendix J (CDT part): centering constant, origin invariance, coupling displacements, volume tilt,
graph budget, conservation, simplex volumes and Newton benchmark
(ledger C10-55 … -57, -59 … -61, -64, -65, -67, -76, -77, -79 … -81, -84, -86, -95, -99, -100, -102). -/

noncomputable section
namespace Entropic.AppIJ
open Real Filter Topology

/-! ### Thermodynamic integration (C10-55, C10-67) -/

section Thermo
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] (E : Ω → ℝ) (N : ℝ)

def Zt (s : ℝ) : ℝ := (∑ ω, Real.exp (-s * N * E ω)) / Fintype.card Ω
def gmean (s : ℝ) : ℝ := (∑ ω, E ω * Real.exp (-s * N * E ω)) / ∑ ω, Real.exp (-s * N * E ω)

theorem Zsum_pos (s : ℝ) : 0 < ∑ ω, Real.exp (-s * N * E ω) :=
  Finset.sum_pos (fun ω _ => Real.exp_pos _) Finset.univ_nonempty

theorem hasDerivAt_logZt (s : ℝ) :
    HasDerivAt (fun x => Real.log (Zt E N x)) (-N * gmean E N s) s := by
  have hc : (0:ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hsum : HasDerivAt (fun x => ∑ ω, Real.exp (-x * N * E ω))
      (∑ ω, -(N * E ω) * Real.exp (-s * N * E ω)) s := by
    apply HasDerivAt.fun_sum; intro ω _
    have := ((hasDerivAt_id' s).mul_const (-(N * E ω))).exp
    convert this using 1
    · funext x; ring_nf
    · ring_nf
  have hZ := (hsum.div_const (Fintype.card Ω : ℝ)).log (div_pos (Zsum_pos E N s) hc).ne'
  unfold Zt gmean
  convert hZ using 1
  have hp := Zsum_pos E N s
  rw [show (∑ ω, -(N * E ω) * Real.exp (-s * N * E ω)) = -N * ∑ ω, E ω * Real.exp (-s * N * E ω) by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ω _ => by ring)]
  generalize (∑ ω, E ω * Real.exp (-s * N * E ω)) = A at *
  generalize (∑ ω, Real.exp (-s * N * E ω)) = Z at *
  field_simp

theorem gmean_continuous : Continuous (gmean E N) := by
  unfold gmean
  exact Continuous.div (by fun_prop) (by fun_prop) (fun s => (Zsum_pos E N s).ne')

/-- C10-55: −(1/(βN)) ln Z(β) = (1/β)∫₀^β ⟨Ē⟩_s ds. -/
theorem thermodynamic_integration (β : ℝ) (hβ : 0 < β) (hN : N ≠ 0) :
    -(1 / (β * N)) * Real.log (Zt E N β) = (1 / β) * ∫ s in (0:ℝ)..β, gmean E N s := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := β)
    (f := fun x => Real.log (Zt E N x)) (f' := fun s => -N * gmean E N s)
    (fun s _ => hasDerivAt_logZt E N s)
    ((continuous_const.mul (gmean_continuous E N)).intervalIntegrable _ _)
  have hZ0 : Zt E N 0 = 1 := by
    unfold Zt; simp
  rw [hZ0, Real.log_one, sub_zero, intervalIntegral.integral_const_mul] at hftc
  rw [← hftc]; field_simp

/-- C10-67: d⟨Ē⟩_β/dβ = −N Var_β(Ē) ≤ 0 (so β ↦ βμ(β) = ∫₀^β⟨Ē⟩ is concave). -/
theorem gmean_deriv (β : ℝ) :
    HasDerivAt (gmean E N) (-N * (((∑ ω, E ω ^ 2 * Real.exp (-β * N * E ω)) / ∑ ω, Real.exp (-β * N * E ω)) -
      gmean E N β ^ 2)) β := by
  have hnum : HasDerivAt (fun x => ∑ ω, E ω * Real.exp (-x * N * E ω))
      (∑ ω, -(N * E ω ^ 2) * Real.exp (-β * N * E ω)) β := by
    apply HasDerivAt.fun_sum; intro ω _
    have := (((hasDerivAt_id' β).mul_const (-(N * E ω))).exp).const_mul (E ω)
    convert this using 1
    · funext x; ring_nf
    · ring_nf
  have hden : HasDerivAt (fun x => ∑ ω, Real.exp (-x * N * E ω))
      (∑ ω, -(N * E ω) * Real.exp (-β * N * E ω)) β := by
    apply HasDerivAt.fun_sum; intro ω _
    have := ((hasDerivAt_id' β).mul_const (-(N * E ω))).exp
    convert this using 1
    · funext x; ring_nf
    · ring_nf
  have h := hnum.div hden (Zsum_pos E N β).ne'
  unfold gmean
  convert h using 1
  have hp := Zsum_pos E N β
  simp only [neg_mul, Finset.sum_neg_distrib]
  rw [show ∑ ω, N * E ω ^ 2 * Real.exp (-(β * N * E ω)) = N * ∑ ω, E ω ^ 2 * Real.exp (-(β * N * E ω)) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ω _ => by ring),
    show ∑ ω, N * E ω * Real.exp (-(β * N * E ω)) = N * ∑ ω, E ω * Real.exp (-(β * N * E ω)) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ω _ => by ring)]
  generalize (∑ ω, E ω ^ 2 * Real.exp (-(β * N * E ω))) = A2 at *
  generalize (∑ ω, E ω * Real.exp (-(β * N * E ω))) = A at *
  simp only [neg_mul] at hp ⊢
  generalize (∑ ω, Real.exp (-(β * N * E ω))) = Z at *
  field_simp; ring

theorem variance_nonneg (β : ℝ) :
    0 ≤ ((∑ ω, E ω ^ 2 * Real.exp (-β * N * E ω)) / ∑ ω, Real.exp (-β * N * E ω)) - gmean E N β ^ 2 := by
  have hp := Zsum_pos E N β
  set Z := ∑ ω, Real.exp (-β * N * E ω)
  set m := gmean E N β
  have : ((∑ ω, E ω ^ 2 * Real.exp (-β * N * E ω)) / Z) - m ^ 2 =
      (∑ ω, (E ω - m) ^ 2 * Real.exp (-β * N * E ω)) / Z := by
    have hm : m * Z = ∑ ω, E ω * Real.exp (-β * N * E ω) := by
      simp only [m, gmean, Z]
      generalize (∑ ω, E ω * Real.exp (-β * N * E ω)) = A at *
      field_simp
    have e : ∑ ω, (E ω - m) ^ 2 * Real.exp (-β * N * E ω) =
        ∑ ω, E ω ^ 2 * Real.exp (-β * N * E ω) - 2 * m * ∑ ω, E ω * Real.exp (-β * N * E ω) + m ^ 2 * Z := by
      simp only [Z, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun ω _ => by ring)
    rw [e, ← hm]
    generalize (∑ ω, E ω ^ 2 * Real.exp (-β * N * E ω)) = A2 at *
    field_simp; ring
  rw [this]
  exact div_nonneg (Finset.sum_nonneg (fun ω _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)) hp.le

end Thermo

/-! ### Origin invariance, coupling displacement, orientation, counts (C10-56, -57, -59, -60, -61, -95) -/

/-- C10-56: E_c ↦ E_c + C, μ ↦ μ + C leaves Ẑ = e^{βμN} Σ e^{−βΣ_c E_c} unchanged. -/
theorem origin_invariance {ι : Type*} (S : Finset ι) (E : ι → ℝ) (β μ C N : ℝ) :
    Real.exp (β * (μ + C) * N) * ∑ x ∈ S, Real.exp (-β * (E x + N * C)) =
      Real.exp (β * μ * N) * ∑ x ∈ S, Real.exp (-β * E x) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← Real.exp_add, ← Real.exp_add]; ring_nf

/-- C10-57, C10-95: the action basis rewriting, and the N₄₁ source (βμ/2)N₄₁ is the displacement
δκ₄ = −βμ/2, δΔ = +βμ/2, δκ₀ = −6δΔ. -/
theorem cdt_displacement (κ0 κ4 Δ βμ N0 N41 N32 : ℝ) :
    -(κ0 + 6 * Δ) * N0 + κ4 * (N41 + N32) + Δ * (2 * N41 + N32) =
      -(κ0 + 6 * Δ) * N0 + (κ4 + 2 * Δ) * N41 + (κ4 + Δ) * N32 ∧
    -((κ0 - 6 * (βμ / 2)) + 6 * (Δ + βμ / 2)) * N0 + ((κ4 - βμ / 2) + 2 * (Δ + βμ / 2)) * N41 +
        ((κ4 - βμ / 2) + (Δ + βμ / 2)) * N32 =
      -(κ0 + 6 * Δ) * N0 + (κ4 + 2 * Δ) * N41 + (κ4 + Δ) * N32 + βμ / 2 * N41 := by
  constructor <;> ring

/-- C10-59: a geometry-independent two-fold orientation adds exactly ln 2 to the log partition function. -/
theorem orientation_ln2 {ι : Type*} (S : Finset ι) (w : ι → ℝ) (hw : 0 < ∑ x ∈ S, w x) :
    Real.log (∑ x ∈ S, (w x + w x)) = Real.log 2 + Real.log (∑ x ∈ S, w x) := by
  rw [Finset.sum_add_distrib, ← two_mul, Real.log_mul (by norm_num) hw.ne']

/-- C10-60: the sorted-label orbits (multisets of size 4 from 7 labels) number C(10,4) = 210. -/
theorem sorted_orbits : Fintype.card (Sym (Fin 7) 4) = 210 := by
  rw [Sym.card_sym_eq_choose]; decide

/-- C10-61: P(m not injective) = 1 − 840/2401 = 1561/2401 ∈ (0.65014, 0.65015). -/
theorem collision_benchmark : 7 * 6 * 5 * 4 = 840 ∧ 7 ^ 4 = 2401 ∧
    (0.65014 : ℝ) < 1 - 840 / 2401 ∧ (1 : ℝ) - 840 / 2401 < 0.65015 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ### Volume tilt (C10-64, C10-65) -/

/-- C10-64: ε(N − N̄)² + (βμ/2)N is minimized at N − N̄ = −βμ/(4ε). -/
theorem volume_tilt {ε βμ Nb : ℝ} (hε : 0 < ε) (N : ℝ) :
    ε * ((Nb - βμ / (4 * ε)) - Nb) ^ 2 + βμ / 2 * (Nb - βμ / (4 * ε)) ≤ ε * (N - Nb) ^ 2 + βμ / 2 * N := by
  have : ε * (N - Nb) ^ 2 + βμ / 2 * N - (ε * ((Nb - βμ / (4 * ε)) - Nb) ^ 2 + βμ / 2 * (Nb - βμ / (4 * ε))) =
      ε * (N - Nb + βμ / (4 * ε)) ^ 2 := by field_simp; ring
  nlinarith [mul_nonneg hε.le (sq_nonneg (N - Nb + βμ / (4 * ε)))]

theorem demonstration_point : -(1 * 2.488) / (4 * 0.01) = (-62.2 : ℝ) := by norm_num

/-! ### Budget operator (C10-76) and conservation (C10-77) -/

/-- C10-76: on a 4-regular graph xᵀLx ≤ 8|x|², so 2zI − L with z = 4 is positive semidefinite
(eigenvalues 8 − λ ≥ 0): no small-momentum pole. -/
theorem budget_operator {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 4) (x : V → ℝ) :
    Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) x x ≤ 8 * ∑ i, x i ^ 2 := by
  rw [SimpleGraph.lapMatrix_toLinearMap₂']
  have hb : ∀ i j, (if G.Adj i j then (x i - x j) ^ 2 else 0) ≤
      2 * (if G.Adj i j then x i ^ 2 else 0) + 2 * (if G.Adj i j then x j ^ 2 else 0) := by
    intro i j; split_ifs <;> nlinarith [sq_nonneg (x i + x j)]
  have hdeg : ∀ i, ∑ j, (if G.Adj i j then x i ^ 2 else 0) = 4 * x i ^ 2 := by
    intro i
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have : (Finset.univ.filter (G.Adj i)).card = 4 := by
      rw [← hreg i, ← SimpleGraph.card_neighborFinset_eq_degree]; congr 1; ext j; simp
    rw [this]; norm_num
  have hdeg' : ∀ j, ∑ i, (if G.Adj i j then x j ^ 2 else 0) = 4 * x j ^ 2 := by
    intro j
    rw [show (fun i => if G.Adj i j then x j ^ 2 else 0) = fun i => if G.Adj j i then x j ^ 2 else 0 by
      funext i; simp [G.adj_comm]]
    exact hdeg j
  have hsum : ∑ i, ∑ j, (if G.Adj i j then (x i - x j) ^ 2 else 0) ≤ 16 * ∑ i, x i ^ 2 := by
    calc ∑ i, ∑ j, (if G.Adj i j then (x i - x j) ^ 2 else 0)
        ≤ ∑ i, ∑ j, (2 * (if G.Adj i j then x i ^ 2 else 0) + 2 * (if G.Adj i j then x j ^ 2 else 0)) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hb i j))
      _ = 2 * ∑ i, ∑ j, (if G.Adj i j then x i ^ 2 else 0) + 2 * ∑ j, ∑ i, (if G.Adj i j then x j ^ 2 else 0) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]; rw [Finset.sum_comm (f := fun i j => if G.Adj i j then x j ^ 2 else 0)]
      _ = 16 * ∑ i, x i ^ 2 := by
          simp only [hdeg, hdeg', ← Finset.mul_sum]; ring
  linarith

/-- C10-77: f_x ↦ f_x − Σ_{y∼x}J_xy − Q_x + Q̄ with antisymmetric J and Q̄ the mean conserves Σ_x f_x. -/
theorem transport_conservation {X : Type*} [Fintype X] [Nonempty X] (J : X → X → ℝ) (Q f : X → ℝ)
    (hJ : ∀ x y, J x y = -J y x) :
    ∑ x, (f x - ∑ y, J x y - Q x + (∑ z, Q z) / Fintype.card X) = ∑ x, f x := by
  have hc : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hJ0 : ∑ x, ∑ y, J x y = 0 := by
    have h1 : ∑ x, ∑ y, J x y = -∑ x, ∑ y, J x y := by
      calc ∑ x, ∑ y, J x y = ∑ x, ∑ y, -J y x :=
            Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hJ x y))
        _ = -∑ x, ∑ y, J y x := by simp only [Finset.sum_neg_distrib]
        _ = -∑ y, ∑ x, J y x := by rw [Finset.sum_comm]
    linarith
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hJ0, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp; ring

/-- C10-79: e^{−S_eff} = e^{−S_host} Z_label gives S_eff = S_host − ln Z_label. -/
theorem effective_action (Sh Z : ℝ) (hZ : 0 < Z) : -Real.log (Real.exp (-Sh) * Z) = Sh - Real.log Z := by
  rw [Real.log_mul (Real.exp_pos _).ne' hZ.ne', Real.log_exp]; ring

/-! ### Simplex volumes and apex height (C10-80, -81, -84, -86) -/

/-- C10-80: base volume a³/(6√2) times apex height a√(α + 3/8), over 4, is a⁴√(8α + 3)/96. -/
theorem simplex41_volume (a α : ℝ) (hα : 0 ≤ 8 * α + 3) :
    (1/4) * (a ^ 3 / (6 * Real.sqrt 2)) * (a * Real.sqrt (α + 3/8)) = a ^ 4 * Real.sqrt (8 * α + 3) / 96 := by
  have h8 : Real.sqrt (α + 3/8) = Real.sqrt (8 * α + 3) / (2 * Real.sqrt 2) := by
    rw [show α + 3/8 = (8 * α + 3) / 8 by ring, Real.sqrt_div' _ (by norm_num),
      show (8:ℝ) = (2 * Real.sqrt 2) ^ 2 by rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num,
      Real.sqrt_sq (by positivity)]
  rw [h8]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 2 := by positivity
  field_simp; rw [show Real.sqrt 2 ^ 2 = 2 by rw [sq, h2]]; ring

/-- C10-81: t₄₁/v₄₁ = t₃₂/v₃₂ = ρ gives R_V = 1 and (t₄₁ + ξt₃₂)/(1+ξ) = ρ(v₄₁ + ξv₃₂)/(1+ξ). -/
theorem two_source_volume {t41 t32 v41 v32 ρ ξ : ℝ} (hv41 : v41 ≠ 0) (hv32 : v32 ≠ 0) (hρ : ρ ≠ 0)
    (h41 : t41 = ρ * v41) (h32 : t32 = ρ * v32) :
    t41 * v32 / (t32 * v41) = 1 ∧ (t41 + ξ * t32) / (1 + ξ) = ρ * ((v41 + ξ * v32) / (1 + ξ)) := by
  subst h41 h32
  constructor
  · field_simp
  · ring

/-- C10-84: the bare cosmological contribution λ[√(8α̃−3) − √(12α̃−7)]/96 vanishes at α̃ = 1. -/
theorem cosmological_delta (lam : ℝ) : lam * (Real.sqrt (8 * 1 - 3) - Real.sqrt (12 * 1 - 7)) / 96 = 0 := by
  norm_num

/-- C10-86: with circumradius R = a√(3/8) and timelike edge² = −αa², the apex height is
h = a√(α + 3/8); at a = 2.530: R = 1.549…, and at α = 7/12, h = 2.476…. -/
theorem apex_height {a α : ℝ} (ha : 0 ≤ a) (hα : 0 ≤ α) :
    Real.sqrt (α * a ^ 2 + (a * Real.sqrt (3/8)) ^ 2) = a * Real.sqrt (α + 3/8) := by
  rw [mul_pow, Real.sq_sqrt (by norm_num), show α * a ^ 2 + a ^ 2 * (3/8) = a ^ 2 * (α + 3/8) by ring,
    Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]

theorem apex_numbers :
    1.549 < 2.530 * Real.sqrt (3/8) ∧ 2.530 * Real.sqrt (3/8) < 1.550 ∧
      2.476 < 2.530 * Real.sqrt (7/12 + 3/8) ∧ 2.530 * Real.sqrt (7/12 + 3/8) < 2.477 := by
  have s1 : (0.61237 : ℝ) < Real.sqrt (3/8) := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s2 : Real.sqrt (3/8) < 0.61238 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have t1 : (0.97894 : ℝ) < Real.sqrt (7/12 + 3/8) := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have t2 : Real.sqrt (7/12 + 3/8) < 0.97895 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ### Newton benchmark, held velocity, normalization (C10-99, -100, -102) -/

/-- C10-99: Q(r,T) = −(2G/(πr))[arctan(T/r) − (r/(2T)) ln(1 + T²/r²)] → −G/r as T → ∞. -/
theorem newton_benchmark (G r : ℝ) (hr : 0 < r) :
    Tendsto (fun T : ℝ => -(2 * G / (π * r)) * (Real.arctan (T / r) - r / (2 * T) * Real.log (1 + T ^ 2 / r ^ 2)))
      atTop (𝓝 (-G / r)) := by
  have h1 : Tendsto (fun T : ℝ => Real.arctan (T / r)) atTop (𝓝 (π / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      (tendsto_id.atTop_div_const hr)
  -- (r/(2T)) ln(1 + T²/r²) = (1/2)(ln(1 + u²)/u) with u = T/r → ∞
  have hlog : Tendsto (fun u : ℝ => Real.log (1 + u ^ 2) / u) atTop (𝓝 0) := by
    have hle : ∀ᶠ u in atTop, Real.log (1 + u ^ 2) / u ≤ 2 * Real.log (2 * u) / u := by
      filter_upwards [eventually_ge_atTop (1:ℝ)] with u hu
      apply div_le_div_of_nonneg_right _ (by linarith)
      rw [← Real.log_rpow (by positivity)]
      apply Real.log_le_log (by positivity)
      rw [show ((2 * u) ^ (2:ℝ)) = 4 * u ^ 2 by rw [Real.rpow_two]; ring]; nlinarith
    have hge : ∀ᶠ u in atTop, 0 ≤ Real.log (1 + u ^ 2) / u := by
      filter_upwards [eventually_ge_atTop (1:ℝ)] with u hu
      exact div_nonneg (Real.log_nonneg (by nlinarith)) (by linarith)
    have hup : Tendsto (fun u : ℝ => 2 * Real.log (2 * u) / u) atTop (𝓝 0) := by
      have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero)
      have h2 : Tendsto (fun u : ℝ => Real.log (2 * u) / (2 * u)) atTop (𝓝 0) := by
        have := h.comp (tendsto_id.const_mul_atTop (show (0:ℝ) < 2 by norm_num))
        simpa [Function.comp_def] using this
      have := h2.const_mul 4
      rw [mul_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
      field_simp; ring
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup hge hle
  have h2 : Tendsto (fun T : ℝ => r / (2 * T) * Real.log (1 + T ^ 2 / r ^ 2)) atTop (𝓝 0) := by
    have := (hlog.comp (tendsto_id.atTop_div_const hr)).const_mul (1/2)
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    simp only [Function.comp, id]
    rw [div_pow]; field_simp
  have := ((h1.sub h2).const_mul (-(2 * G / (π * r))))
  convert this using 2
  field_simp; ring

/-- C10-100: among v with A_D + e·v = 0 (|e| = 1), |v| ≥ |A_D|, with equality at v = −A_D e. -/
theorem min_norm_velocity (e v : Fin 3 → ℝ) (A : ℝ) (he : e ⬝ᵥ e = 1) (hv : A + e ⬝ᵥ v = 0) :
    A ^ 2 ≤ v ⬝ᵥ v ∧ (A + e ⬝ᵥ (-A • e) = 0) ∧ (-A • e) ⬝ᵥ (-A • e) = A ^ 2 := by
  refine ⟨?_, by rw [dotProduct_smul, he]; simp, by rw [dotProduct_smul, smul_dotProduct, he]; simp; ring⟩
  have hcs : (e ⬝ᵥ v) ^ 2 ≤ (e ⬝ᵥ e) * (v ⬝ᵥ v) := by
    simp only [dotProduct, Fin.sum_univ_three]
    nlinarith [sq_nonneg (e 0 * v 1 - e 1 * v 0), sq_nonneg (e 0 * v 2 - e 2 * v 0),
      sq_nonneg (e 1 * v 2 - e 2 * v 1)]
  rw [he, one_mul] at hcs
  have : e ⬝ᵥ v = -A := by linarith
  rw [this] at hcs; nlinarith

/-- C10-102: Z₀₀ = Σ_g P₀(g)·1 = 1. -/
theorem sourced_normalization {ι : Type*} (S : Finset ι) (P : ι → ℝ) (h : ∑ g ∈ S, P g = 1) :
    ∑ g ∈ S, P g * 1 = 1 := by simpa using h

end Entropic.AppIJ
