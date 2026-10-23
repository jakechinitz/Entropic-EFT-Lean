import Entropic.Main.Core
import Entropic.Main.Galactic
import Entropic.AppH11.Records
import Entropic.AppO.Numerics
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic

/-! Main text Parts V–VIII remainder (ledger C03): the maximum-path-entropy kernel (C03-21), fresh
amplitudes and determinants (C03-28 … C03-32), K₄ matchings (C03-29), the rare-event size (C03-38),
the joint Gibbs measure at β = 0 (C03-52), the defect configurations (C03-62), the rebalanced budget
(C03-64), Kirchhoff cancellation and the slice Laplacian kernel (C03-66 … C03-68), lattice/junction
algebra (C03-72, C03-77 … C03-80), the capacity free-energy centering (C03-85, C03-89, C03-92 … C03-98),
volume couplings (C03-101, C03-102, C03-105 … C03-113), Gaussian relative entropy (C03-115, C03-116),
no-signaling (C03-152), Hubble ratio and boosts (C03-162, C03-163) and horizon/bulk algebra
(C03-168, C03-169, C03-172). -/

noncomputable section
namespace Entropic.Main.Cosmo
open Real Matrix

/-! ### C03-21: maximum path entropy -/

section Path
open Entropic.AppFG.Info
variable {B : Type*} [Fintype B]

/-- C03-21: for a joint law P(b,b′) = p(b)K(b,b′) with second marginal q, H(B′|B) = H(P) − H(p) ≤ H(q),
with equality iff P = p ⊗ q (i.e. K(b,·) = q whenever p(b) > 0). -/
theorem max_path_entropy (P : B → B → ℝ) (hP : ∀ x y, 0 ≤ P x y) (h1 : ∑ x, ∑ y, P x y = 1) :
    Hjoint P - H (pX P) ≤ H (pY P) ∧ (Hjoint P - H (pX P) = H (pY P) ↔ ∀ x y, P x y = pX P x * pY P y) := by
  refine ⟨by linarith [subadditive P hP h1], ?_⟩
  rw [← subadditive_eq_iff P hP h1]; constructor <;> intro h <;> linarith
end Path

/-! ### C03-28 … C03-32, C03-38 -/

/-- C03-28: Σ_b (√p_b)² = 1 for a probability law. -/
theorem fresh_norm {B : Type*} [Fintype B] (p : B → ℝ) (hp : ∀ b, 0 ≤ p b) (h1 : ∑ b, p b = 1) :
    ∑ b, Real.sqrt (p b) ^ 2 = 1 := by
  simp only [Real.sq_sqrt (hp _)]; exact h1

/-- C03-29: K₄ has exactly three perfect matchings (fixed-point-free involutions of four vertices). -/
theorem k4_matchings :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 4) => σ * σ = 1 ∧ ∀ i, σ i ≠ i)).card = 3 := by decide

/-- C03-30, C03-31: exp(Σ p ln p) = e^{−g} and seven independent channels give e^{−7g}. -/
theorem channel_determinant (g : ℝ) : Real.exp (-g) ^ 7 = Real.exp (-7 * g) := by
  rw [← Real.exp_nat_mul]; ring_nf

/-- C03-32: r = e^{−7g} ∈ (0,1), T = 1 − r ∈ (0,1) and E_raw = −(ħ/τ) ln(1 − r) > 0. -/
theorem survival_gap {g ħτ : ℝ} (hg : 0 < g) (hh : 0 < ħτ) :
    0 < Real.exp (-7 * g) ∧ Real.exp (-7 * g) < 1 ∧ 0 < 1 - Real.exp (-7 * g) ∧ 1 - Real.exp (-7 * g) < 1 ∧
      0 < -(ħτ * Real.log (1 - Real.exp (-7 * g))) := by
  have h1 : Real.exp (-7 * g) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have h0 := Real.exp_pos (-7 * g)
  refine ⟨h0, h1, by linarith, by linarith, ?_⟩
  have := Real.log_neg (by linarith : (0:ℝ) < 1 - Real.exp (-7 * g)) (by linarith)
  nlinarith

/-- C03-38: r ≤ −ln(1 − r) ≤ r/(1 − r) (relative correction ≤ r/(1 − r)), and at the closure root
r = e^{−7g} ∈ (2.77, 2.78)·10⁻²³. -/
theorem rare_event (r : ℝ) (h0 : 0 < r) (h1 : r < 1) :
    r ≤ -Real.log (1 - r) ∧ -Real.log (1 - r) ≤ r / (1 - r) := by
  have hp : 0 < 1 - r := by linarith
  constructor
  · have := Real.log_le_sub_one_of_pos hp; linarith
  · have := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
    rw [Real.log_inv] at this
    have e : (1 - r)⁻¹ - 1 = r / (1 - r) := by field_simp; ring
    linarith

theorem rare_event_value {η : ℝ} (h : Entropic.FiniteModel.ClosureStationary η) :
    2.77e-23 < Real.exp (-7 * Entropic.ClosureRoot.gshare η) ∧ Real.exp (-7 * Entropic.ClosureRoot.gshare η) < 2.78e-23 := by
  obtain ⟨g1, g2⟩ := Entropic.ClosureRoot.gshare_bracket h
  unfold Entropic.ClosureRoot.gLo at g1; unfold Entropic.ClosureRoot.gHi at g2
  have hlo := Entropic.AppO.Num.exp_lower (a := 7 * (74198000220 / 10 ^ 10)) 52 (by norm_num [abs_le])
  have hhi := Entropic.AppO.Num.exp_upper (a := 7 * (74198000250 / 10 ^ 10)) 52 (by norm_num [abs_le])
  have n1 : (1 / 2.78e-23 : ℝ) < Real.exp (7 * (74198000220 / 10 ^ 10)) :=
    lt_of_lt_of_le (by norm_num [Entropic.AppO.Num.tay]) hlo
  have n2 : Real.exp (7 * (74198000250 / 10 ^ 10)) < (1 / 2.77e-23 : ℝ) :=
    lt_of_le_of_lt hhi (by norm_num [Entropic.AppO.Num.tay])
  have m1 : Real.exp (7 * (74198000220 / 10 ^ 10)) < Real.exp (7 * Entropic.ClosureRoot.gshare η) :=
    Real.exp_lt_exp.mpr (by linarith)
  have m2 : Real.exp (7 * Entropic.ClosureRoot.gshare η) < Real.exp (7 * (74198000250 / 10 ^ 10)) :=
    Real.exp_lt_exp.mpr (by linarith)
  have e : Real.exp (-7 * Entropic.ClosureRoot.gshare η) = 1 / Real.exp (7 * Entropic.ClosureRoot.gshare η) := by
    rw [show -7 * Entropic.ClosureRoot.gshare η = -(7 * Entropic.ClosureRoot.gshare η) by ring, Real.exp_neg, one_div]
  have hp := Real.exp_pos (7 * Entropic.ClosureRoot.gshare η)
  rw [e]
  constructor
  · rw [lt_div_iff₀ hp]; have := lt_trans m2 n2; rw [lt_div_iff₀ (by norm_num)] at this; linarith
  · rw [div_lt_iff₀ hp]; have := lt_trans n1 m1; rw [div_lt_iff₀ (by norm_num)] at this; linarith

/-! ### C03-52, C03-62, C03-64 -/

/-- C03-52: at β = 0 the label factor is the configuration count, so the g-marginal is ∝ e^{−S(g)}. -/
theorem beta_zero_marginal {M : Type*} [Fintype M] (w : ℝ) (E : M → ℝ) :
    ∑ m : M, w * Real.exp (-(0:ℝ) * E m) = w * Fintype.card M := by
  simp; ring

/-- C03-62: the all-zero configuration has C(4,2) = 6 collisions and K² = 48. -/
theorem defect_configs : Nat.choose 4 2 = 6 ∧ (48:ℝ) - ((0 + 0 + 0 + 0) ^ 2 - (0 + 0 + 0 + 0)) / 3 = 48 :=
  ⟨by decide, by norm_num⟩

/-- C03-64: if L1 = 0 then (2z − L)1 = 2z·1 ≠ 0 (no small-momentum pole). -/
theorem rebalanced_budget {n : Type*} [Fintype n] [DecidableEq n] (L : Matrix n n ℝ) (z : ℝ) (hz : 0 < z)
    (hL : L *ᵥ (fun _ => 1) = 0) : ((2 * z) • (1 : Matrix n n ℝ) - L) *ᵥ (fun _ => 1) = (2 * z) • (fun _ => 1) := by
  rw [Matrix.sub_mulVec, hL, sub_zero, Matrix.smul_mulVec, Matrix.one_mulVec]

/-! ### C03-66 … C03-68: graphs -/

section Graph
variable {V Ed : Type*} [Fintype V] [Fintype Ed] [DecidableEq V] (tl hd : Ed → V)

/-- Incidence B_ve = [v = tail e] − [v = head e]. -/
def inc (v : V) (e : Ed) : ℝ := (if v = tl e then 1 else 0) - (if v = hd e then 1 else 0)

/-- C03-66: summing local conservation over S, edges with both ends in S cancel. -/
theorem kirchhoff_cancellation (S : Finset V) (j : Ed → ℝ) :
    ∑ v ∈ S, ∑ e, inc tl hd v e * j e =
      ∑ e, ((if tl e ∈ S then 1 else 0) - (if hd e ∈ S then 1 else 0)) * j e := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [← Finset.sum_mul]; congr 1
  simp only [inc, Finset.sum_sub_distrib, Finset.sum_ite_eq']

/-- C03-67: L = BWBᵀ satisfies L1 = 0 (Bᵀ1 = 0). -/
theorem laplacian_constant (w : Ed → ℝ) (v : V) :
    ∑ u, (∑ e, inc tl hd v e * w e * inc tl hd u e) * 1 = 0 := by
  simp only [mul_one]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero; intro e _
  rw [← Finset.mul_sum]
  simp [inc, Finset.sum_sub_distrib]

/-- C03-68: the quadratic form xᵀ(BWBᵀ)x = Σ_e w_e (x_tail − x_head)², so with W > 0 it vanishes only
when x is constant along every edge (hence on each connected component). -/
theorem laplacian_form (w : Ed → ℝ) (x : V → ℝ) :
    ∑ v, ∑ u, x v * (∑ e, inc tl hd v e * w e * inc tl hd u e) * x u = ∑ e, w e * (x (tl e) - x (hd e)) ^ 2 := by
  have hB : ∀ e, ∑ v, x v * inc tl hd v e = x (tl e) - x (hd e) := by
    intro e; simp [inc, mul_sub, Finset.sum_sub_distrib]
  calc ∑ v, ∑ u, x v * (∑ e, inc tl hd v e * w e * inc tl hd u e) * x u
      = ∑ e, w e * (∑ v, x v * inc tl hd v e) * (∑ u, x u * inc tl hd u e) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
        simp_rw [Finset.sum_comm (γ := Ed)]
        refine Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl
          (fun u _ => by ring)))
    _ = _ := by simp only [hB]; exact Finset.sum_congr rfl (fun e _ => by ring)

theorem laplacian_kernel (w : Ed → ℝ) (hw : ∀ e, 0 < w e) (x : V → ℝ)
    (h0 : ∑ e, w e * (x (tl e) - x (hd e)) ^ 2 = 0) : ∀ e, x (tl e) = x (hd e) := by
  intro e
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => mul_nonneg (hw e).le (sq_nonneg _))).mp h0 e
    (Finset.mem_univ e)
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (hw e).ne'
  · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h; linarith
end Graph

/-! ### C03-72, C03-77 … C03-80: junction and native units -/

/-- C03-72: L_f ≈ wa²(−∇²) with node source αρa³ gives −∇²μ = (α/D)ρ with D = w/a. -/
theorem diffusion_constant {w a α ρ lap : ℝ} (ha : a ≠ 0) (hw : w ≠ 0) (h : w * a ^ 2 * (-lap) = α * (ρ * a ^ 3)) :
    -lap = α / (w / a) * ρ := by
  field_simp at h ⊢; linarith

/-- C03-77: ∇²q = (χα/D)ρ with q = 1 + 2Φ/c² and ∇²Φ = 4πGρ for all ρ gives χα/D = 8πG/c². -/
theorem junction_coefficient {k G c : ℝ} (hc : c ≠ 0) (h : ∀ ρ : ℝ, k * ρ = 2 / c ^ 2 * (4 * π * G * ρ)) :
    k = 8 * π * G / c ^ 2 := by
  have := h 1; field_simp at this ⊢; linarith

/-- C03-78, C03-79: 8πG*/c² ∈ (1.866394, 1.866395)·10⁻²⁶ m/kg and m* = √(ħc/G*) ∈ (2.17643, 2.17644)·10⁻⁸ kg
(G* = 6.6742890813·10⁻¹¹). -/
theorem native_si :
    1.866394e-26 < 8 * π * 6.6742890813e-11 / 299792458 ^ 2 ∧ 8 * π * 6.6742890813e-11 / 299792458 ^ 2 < 1.866395e-26 ∧
      2.17643e-8 < Real.sqrt (1.054571817e-34 * 299792458 / 6.6742890813e-11) ∧
      Real.sqrt (1.054571817e-34 * 299792458 / 6.6742890813e-11) < 2.17644e-8 := by
  have p1 := Real.pi_gt_d6; have p2 := Real.pi_lt_d6
  refine ⟨by nlinarith, by nlinarith, ?_, ?_⟩
  · rw [show (2.17643e-8 : ℝ) = Real.sqrt (2.17643e-8 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · rw [show (2.17644e-8 : ℝ) = Real.sqrt (2.17644e-8 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)

/-- C03-80: with x = L x̃, ρ = (m*/L³)ρ̃, G = c³L²/ħ, m* = ħ/(cL): L²·(8πG/c²)·(m*/L³) = 8π; and 8π ∈ (25.13274, 25.13275). -/
theorem native_junction {L c ħ : ℝ} (hL : L ≠ 0) (hc : c ≠ 0) (hh : ħ ≠ 0) :
    L ^ 2 * (8 * π * (c ^ 3 * L ^ 2 / ħ) / c ^ 2) * ((ħ / (c * L)) / L ^ 3) = 8 * π ∧
      25.13274 < 8 * π ∧ 8 * π < 25.13275 := by
  have p1 := Real.pi_gt_d20; have p2 := Real.pi_lt_d20
  refine ⟨by field_simp, by linarith, by linarith⟩

/-! ### C03-85, C03-89, C03-92 … C03-98: capacity factor and couplings -/

/-- C03-85: e^{−S}·Z_cap = e^{−(S − ln Z_cap)} for Z_cap > 0. -/
theorem effective_action {S Z : ℝ} (hZ : 0 < Z) : Real.exp (-S) * Z = Real.exp (-(S - Real.log Z)) := by
  rw [show -(S - Real.log Z) = -S + Real.log Z by ring, Real.exp_add, Real.exp_log hZ]

/-- C03-89, C03-109: with N₃₂ = ξN₄₁ and N₄ = N₄₁ + N₃₂, v₄₁N₄₁ + v₃₂N₃₂ = v̄₄N₄, v̄₄ = (v₄₁ + ξv₃₂)/(1 + ξ). -/
theorem fixed_ratio {v41 v32 ξ N41 : ℝ} (hξ : 1 + ξ ≠ 0) :
    v41 * N41 + v32 * (ξ * N41) = (v41 + ξ * v32) / (1 + ξ) * (N41 + ξ * N41) := by
  field_simp

/-- C03-92, C03-93: if −(1/(βN)) ln Z(N) → μ then for Ẑ = e^{βμN}Z, −(1/(βN)) ln Ẑ(N) → 0. -/
theorem centered_density (Z : ℕ → ℝ) (hZ : ∀ N, 0 < Z N) {β μ : ℝ} (hβ : 0 < β)
    (hlim : Filter.Tendsto (fun N : ℕ => -(1 / (β * N)) * Real.log (Z N)) Filter.atTop (nhds μ)) :
    Filter.Tendsto (fun N : ℕ => -(1 / (β * N)) * Real.log (Real.exp (β * μ * N) * Z N)) Filter.atTop (nhds 0) := by
  have e : ∀ N : ℕ, 0 < N → -(1 / (β * N)) * Real.log (Real.exp (β * μ * N) * Z N) =
      -μ + -(1 / (β * N)) * Real.log (Z N) := by
    intro N hN
    have hN' : (0:ℝ) < N := by exact_mod_cast hN
    rw [Real.log_mul (Real.exp_pos _).ne' (hZ N).ne', Real.log_exp]; field_simp; try ring
  have : Filter.Tendsto (fun N : ℕ => -μ + -(1 / (β * N)) * Real.log (Z N)) Filter.atTop (nhds (-μ + μ)) :=
    tendsto_const_nhds.add hlim
  rw [neg_add_cancel] at this
  apply this.congr'
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN
  exact (e N hN).symm

/-- C03-94: E ↦ E + C multiplies Z by e^{−βCN} and shifts μ by C, leaving Ẑ = e^{βμN}Z invariant. -/
theorem origin_invariance {β μ C N Z : ℝ} :
    Real.exp (β * (μ + C) * N) * (Real.exp (-β * C * N) * Z) = Real.exp (β * μ * N) * Z := by
  rw [← mul_assoc, ← Real.exp_add]; ring_nf

/-- C03-96: ε(N − N̄)² + bN is minimized at N = N̄ − b/(2ε); with b = βμ/2, ΔN = −βμ/(4ε). -/
theorem volume_displacement {ε b Nbar : ℝ} (hε : 0 < ε) (N : ℝ) :
    ε * (Nbar - b / (2 * ε) - Nbar) ^ 2 + b * (Nbar - b / (2 * ε)) ≤ ε * (N - Nbar) ^ 2 + b * N ∧
      (b / 2) / (2 * ε) = b / (4 * ε) := by
  constructor
  · have : ε * (N - Nbar) ^ 2 + b * N - (ε * (Nbar - b / (2 * ε) - Nbar) ^ 2 + b * (Nbar - b / (2 * ε))) =
        ε * (N - (Nbar - b / (2 * ε))) ^ 2 := by field_simp; ring
    nlinarith [mul_nonneg hε.le (sq_nonneg (N - (Nbar - b / (2 * ε))))]
  · field_simp; ring

/-- C03-98: δΔ = b, δκ₄ = −b, δκ₀ = −6b shift S_CDT by exactly bN₄₁. -/
theorem cdt_shift (κ0 Δ κ4 b N0 N41 N32 : ℝ) :
    let S := fun k0 D k4 => -(k0 + 6 * D) * N0 + k4 * (N41 + N32) + D * (2 * N41 + N32)
    S (κ0 - 6 * b) (Δ + b) (κ4 - b) - S κ0 Δ κ4 = b * N41 := by
  intro S; simp only [S]; ring

/-! ### C03-101 … C03-113: volume couplings -/

/-- C03-101: for α > 7/12, 8α − 3 > 0 and 12α − 7 > 0; C03-108: at α = 1 both volumes are √5/96. -/
theorem regge_nondegenerate {α : ℝ} (h : 7/12 < α) : 0 < 8 * α - 3 ∧ 0 < 12 * α - 7 := by
  constructor <;> linarith

theorem isotropic_point : Real.sqrt (8 * 1 - 3) / 96 = Real.sqrt 5 / 96 ∧ Real.sqrt (12 * 1 - 7) / 96 = Real.sqrt 5 / 96 := by
  norm_num

/-- C03-102, C03-111: (√3/4)a² = 4 ln 2 L² gives a ∈ (2.530, 2.531) L, and (2.530)³/(6√2) ∈ (1.908, 1.909). -/
theorem lock_edge :
    2.530 < Real.sqrt (16 * Real.log 2 / Real.sqrt 3) ∧ Real.sqrt (16 * Real.log 2 / Real.sqrt 3) < 2.531 ∧
      1.908 < (2.530 : ℝ) ^ 3 / (6 * Real.sqrt 2) ∧ (2.530 : ℝ) ^ 3 / (6 * Real.sqrt 2) < 1.909 := by
  have l1 := Real.log_two_gt_d9; have l2 := Real.log_two_lt_d9
  have s3a : (1.7320508 : ℝ) < Real.sqrt 3 := by
    rw [show (1.7320508:ℝ) = Real.sqrt (1.7320508 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have s3b : Real.sqrt 3 < (1.7320509 : ℝ) := by
    rw [show (1.7320509:ℝ) = Real.sqrt (1.7320509 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have s2a : (1.4142135 : ℝ) < Real.sqrt 2 := by
    rw [show (1.4142135:ℝ) = Real.sqrt (1.4142135 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have s2b : Real.sqrt 2 < (1.4142136 : ℝ) := by
    rw [show (1.4142136:ℝ) = Real.sqrt (1.4142136 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hq1 : (6.403 : ℝ) < 16 * Real.log 2 / Real.sqrt 3 := by rw [lt_div_iff₀ (by linarith)]; nlinarith
  have hq2 : 16 * Real.log 2 / Real.sqrt 3 < (6.4031 : ℝ) := by rw [div_lt_iff₀ (by linarith)]; nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (2.530:ℝ) = Real.sqrt (2.530 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by nlinarith)
  · rw [show (2.531:ℝ) = Real.sqrt (2.531 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by positivity) (by nlinarith)
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- C03-105, C03-112: ρ = c³Λ/(8πħG) = Λ/(8πL_G²) with L_G² = ħG/c³, and t* = ρL*⁴ = ΛL*²/(8π) when L_G = L*. -/
theorem volume_density {c Λ ħ G L : ℝ} (hc : c ≠ 0) (hh : ħ ≠ 0) (hG : G ≠ 0) :
    c ^ 3 * Λ / (8 * π * ħ * G) = Λ / (8 * π * (ħ * G / c ^ 3)) ∧
      (L ^ 2 = ħ * G / c ^ 3 → Λ / (8 * π * (ħ * G / c ^ 3)) * L ^ 4 = Λ * L ^ 2 / (8 * π)) := by
  have hp : π ≠ 0 := Real.pi_ne_zero
  refine ⟨by field_simp, fun hL => ?_⟩
  rw [← hL]
  by_cases hL0 : L = 0
  · simp [hL0]
  · field_simp

/-- C03-107: δκ₄ + 2δΔ = a⁴v₄₁ρ and δκ₄ + δΔ = a⁴v₃₂ρ have the unique solution
(δκ₄, δΔ) = a⁴ρ(2v₃₂ − v₄₁, v₄₁ − v₃₂). -/
theorem coupling_displacement {k D A41 A32 : ℝ} :
    (k + 2 * D = A41 ∧ k + D = A32) ↔ (k = 2 * A32 - A41 ∧ D = A41 - A32) := by
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- C03-113: if the normalized vacuum free energy has zero density, an extra extensive term ρ·v·N with
ρv ≠ 0 would give density ρv ≠ 0; hence ρ_cap^(eq) = 0. -/
theorem zero_cap_density {ρ v : ℝ} (f : ℕ → ℝ) (hf : Filter.Tendsto (fun N : ℕ => f N / N) Filter.atTop (nhds 0))
    (h : Filter.Tendsto (fun N : ℕ => (f N + ρ * v * N) / N) Filter.atTop (nhds 0)) : ρ * v = 0 := by
  have e : Filter.Tendsto (fun N : ℕ => (f N + ρ * v * N) / N - f N / N) Filter.atTop (nhds (0 - 0)) := h.sub hf
  rw [sub_zero] at e
  have e2 : Filter.Tendsto (fun N : ℕ => (f N + ρ * v * N) / N - f N / N) Filter.atTop (nhds (ρ * v)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_gt_atTop 0] with N hN
    have : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp; ring
  exact tendsto_nhds_unique e2 e

/-! ### C03-115, C03-116: Gaussian relative entropy -/

/-- C03-115: λ − 1 − ln λ ≥ 0 for λ > 0, with equality iff λ = 1; hence (1/2)Σ(λᵢ − 1 − ln λᵢ) ≥ 0 with
equality iff all λᵢ = 1 (G = I). -/
theorem gaussian_kl_nonneg {ι : Type*} [Fintype ι] (lam : ι → ℝ) (h : ∀ i, 0 < lam i) :
    0 ≤ (1/2) * ∑ i, (lam i - 1 - Real.log (lam i)) ∧
      ((1/2) * ∑ i, (lam i - 1 - Real.log (lam i)) = 0 ↔ ∀ i, lam i = 1) := by
  have hn : ∀ i, 0 ≤ lam i - 1 - Real.log (lam i) := fun i => by
    have := Real.log_le_sub_one_of_pos (h i); linarith
  refine ⟨by have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hn i); linarith, ⟨fun h0 => ?_, fun h1 => ?_⟩⟩
  · have hs : ∑ i, (lam i - 1 - Real.log (lam i)) = 0 := by linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp hs
    intro i
    by_contra hne
    have := Real.log_lt_sub_one_of_pos (h i) hne
    linarith [this, ‹∀ i ∈ Finset.univ, _› i (Finset.mem_univ i)]
  · simp [h1]

/-- C03-116: for |x| ≤ 1/2, |(x − ln(1 + x))/2 − x²/4| ≤ |x|³. -/
theorem gaussian_kl_quadratic {x : ℝ} (hx : |x| ≤ 1/2) : |(x - Real.log (1 + x)) / 2 - x ^ 2 / 4| ≤ |x| ^ 3 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -x) (by rw [abs_neg]; linarith) 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at h
  norm_num at h
  have e : (x - Real.log (1 + x)) / 2 - x ^ 2 / 4 = -(-x + x ^ 2 / 2 + Real.log (1 + x)) / 2 := by ring
  rw [e, abs_div, abs_neg, abs_two]
  have : |x| ^ 3 / (1 - |x|) ≤ 2 * |x| ^ 3 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [pow_nonneg (abs_nonneg x) 3]
  have h' : |-x + x ^ 2 / 2 + Real.log (1 + x)| ≤ 2 * |x| ^ 3 := le_trans h this
  linarith

/-! ### C03-152: no-signaling -/

section NoSignal
variable {s r : Type*} [Fintype s] [Fintype r] [DecidableEq s] [DecidableEq r]
open Entropic.AppH11

/-- C03-152: for remote instrument maps Iₖ whose sum is trace preserving, Σₖ Tr_B[(id ⊗ Iₖ)ρ] = Tr_B ρ. -/
theorem no_signaling {K : Type*} [Fintype K] (I : K → Matrix r r ℂ →ₗ[ℂ] Matrix r r ℂ)
    (hTP : ∀ Y, (∑ k, I k Y).trace = Y.trace) (ρ : Matrix (s × r) (s × r) ℂ) :
    ∑ k, ptrE (idTensor (I k) ρ) = ptrE ρ := by
  ext i j
  simp only [Finset.sum_apply, Matrix.sum_apply, ptrE, Matrix.of_apply, idTensor]
  rw [Finset.sum_comm]
  have := hTP (blk ρ i j)
  simp only [Matrix.trace, Matrix.diag, Matrix.sum_apply] at this
  rw [this]; simp [blk]
end NoSignal

/-! ### C03-162, C03-163, C03-168, C03-169, C03-172 -/

/-- C03-162: H(2.3)/H₀ = √(0.315·3.3³ + 0.685) ∈ (3.464, 3.465). -/
theorem hubble_ratio :
    3.464 < Real.sqrt (0.315 * 3.3 ^ 3 + 0.685) ∧ Real.sqrt (0.315 * 3.3 ^ 3 + 0.685) < 3.465 := by
  constructor
  · rw [show (3.464:ℝ) = Real.sqrt (3.464 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · rw [show (3.465:ℝ) = Real.sqrt (3.465 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- C03-168: with L² = ħG/c³, A/(4L²) = c³A/(4ħG). -/
theorem horizon_normalization {A ħ G c : ℝ} (hh : ħ ≠ 0) (hG : G ≠ 0) (hc : c ≠ 0) :
    A / (4 * (ħ * G / c ^ 3)) = c ^ 3 * A / (4 * ħ * G) := by field_simp

/-- C03-169: ∇²δS = −(κ/γ)ρ, Φ/c² = −δS/(2S) and G = c²κ/(8πγS) give ∇²Φ = 4πGρ. -/
theorem bulk_poisson {κ γ S c ρ lapS : ℝ} (hγ : γ ≠ 0) (hS : S ≠ 0) (h : lapS = -(κ / γ) * ρ) :
    c ^ 2 * (-(lapS) / (2 * S)) = 4 * π * (c ^ 2 * κ / (8 * π * γ * S)) * ρ := by
  have hp : π ≠ 0 := Real.pi_ne_zero
  rw [h]; field_simp; ring

/-- C03-172: A = 4πc²/H² gives S = A/(4L²) = πc²/(H²L²), and S_GfE/S = ω̄L²/(πℓ⁴) for S_GfE = ω̄c²/(ℓ⁴H²). -/
theorem cosmological_entropy {c H L ℓ ω : ℝ} (hH : H ≠ 0) (hL : L ≠ 0) (hℓ : ℓ ≠ 0) (hc : c ≠ 0) :
    4 * π * c ^ 2 / H ^ 2 / (4 * L ^ 2) = π * c ^ 2 / (H ^ 2 * L ^ 2) ∧
      (ω * c ^ 2 / (ℓ ^ 4 * H ^ 2)) / (π * c ^ 2 / (H ^ 2 * L ^ 2)) = ω * L ^ 2 / (π * ℓ ^ 4) := by
  have hp : π ≠ 0 := Real.pi_ne_zero
  constructor <;> field_simp

/-- C03-148: ε = g/(4π²) ∈ (0.187945, 0.187946) at the closure root (0.18795 to five digits). -/
theorem epsilon_value {η : ℝ} (h : Entropic.FiniteModel.ClosureStationary η) :
    0.187945 < Entropic.ClosureRoot.gshare η / (4 * π ^ 2) ∧ Entropic.ClosureRoot.gshare η / (4 * π ^ 2) < 0.187946 := by
  obtain ⟨g1, g2⟩ := Entropic.ClosureRoot.gshare_bracket h
  unfold Entropic.ClosureRoot.gLo at g1; unfold Entropic.ClosureRoot.gHi at g2
  have p1 := Real.pi_gt_d20; have p2 := Real.pi_lt_d20
  have hp : 0 < 4 * π ^ 2 := by positivity
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

end Entropic.Main.Cosmo
