import Entropic.ClosureRoot
import Mathlib.Analysis.Real.Pi.Bounds

/-! Numerical spine downstream of the closure root (main manuscript Sections 3, 13.5,
App. C.5 and R.2). The formulas (marked fugacity, shell factors, area blocking,
cell normalization) are the manuscript's stated definitions and are input here;
what is kernel checked is that the stated numbers follow from them exactly,
starting from the 1680-state spectrum, with certified rational error bounds. -/

noncomputable section
namespace Entropic.Spine
open Entropic.FiniteModel Entropic.ClosureRoot

/-! ## Charged-lepton ladder -/

/-- Marked fugacity ζ* = 9 e^{-g} (1 - 8η/49)^{21/2}. -/
def zeta (η : ℝ) : ℝ := 9 * Real.exp (-gshare η) * (1 - 8 * η / 49) ^ ((21 : ℝ) / 2)
def muRatio (η : ℝ) : ℝ := 720 * (2/7) * (1 + zeta η)
def tauRatio (η : ℝ) : ℝ := 720 ^ 2 * (2/7) ^ 4 * (1 + zeta η) * (1 + 2/7 * zeta η)

theorem rpow_21_2 {x : ℝ} (hx : 0 ≤ x) : x ^ ((21 : ℝ) / 2) = x ^ 10 * Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add' hx (by norm_num)]; norm_num

theorem exp_neg_gshare {η : ℝ} (h : ClosureStationary η) :
    Real.exp (-gshare η) = Real.exp (-(3/2 - η * (122/3))) / Sq (Real.exp (-η * (2/3))) := by
  have hroot : η * meanK2 η = 3/2 := by
    obtain ⟨he, hm⟩ := h; rw [hm]; field_simp <;> ring
  rw [gshare_eq, hroot, log_Z_eq]
  have hS := Sq_pos (Real.exp_pos (-η * (2/3))).le
  rw [show -(-η * (122/3) + Real.log (Sq (Real.exp (-η * (2/3)))) + 3/2) =
      -(3/2 - η * (122/3)) - Real.log (Sq (Real.exp (-η * (2/3)))) by ring,
    Real.exp_sub, Real.exp_log hS]

/-- n-term Taylor enclosure of exp(-a) for 0 ≤ a ≤ 1. -/
theorem exp_neg_encl (n : ℕ) (hn : 0 < n) {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    (∑ m ∈ Finset.range n, (-a) ^ m / m.factorial) - a ^ n * (n.succ / (n.factorial * n)) ≤ Real.exp (-a) ∧
    Real.exp (-a) ≤ (∑ m ∈ Finset.range n, (-a) ^ m / m.factorial) + a ^ n * (n.succ / (n.factorial * n)) := by
  have hb := Real.exp_bound (x := -a) (by rw [abs_neg, abs_of_nonneg h0]; exact h1) hn
  rw [abs_neg, abs_of_nonneg h0] at hb
  constructor <;> linarith [(abs_le.mp hb).1, (abs_le.mp hb).2]

def EL : ℝ := 7517022371604859613596436 / 10 ^ 25
def EU : ℝ := 7517022371665998068070473 / 10 ^ 25
def sL : ℝ := 9975589107953310979429895 / 10 ^ 25
def sU : ℝ := 9975589107953474644256462 / 10 ^ 25

theorem zeta_bracket {η : ℝ} (h : ClosureStationary η) :
    9 * (EL / (1254365353088095 / 10 ^ 12)) * (1 - 8 * etaHi / 49) ^ 10 * sL ≤ zeta η ∧
    zeta η ≤ 9 * (EU / (1254365353085696 / 10 ^ 12)) * (1 - 8 * etaLo / 49) ^ 10 * sU := by
  obtain ⟨b1, b2⟩ := stationary_bracket h
  obtain ⟨hSL, hSU⟩ := Sq_bracket b1 b2
  have hx0 : 0 ≤ 1 - 8 * η / 49 := by unfold etaHi at b2; linarith
  unfold zeta; rw [exp_neg_gshare h, rpow_21_2 hx0, ← mul_assoc]
  -- exp(-(3/2 - 122η/3)) enclosure
  have hE1 : EL ≤ Real.exp (-(3/2 - η * (122/3))) := by
    have e := (exp_neg_encl 14 (by norm_num) (a := 3/2 - etaLo * (122/3))
      (by norm_num [etaLo]) (by norm_num [etaLo])).1
    refine le_trans ?_ (le_trans e (Real.exp_le_exp.mpr (by linarith)))
    norm_num [EL, etaLo, Finset.sum_range_succ, Nat.factorial]
  have hE2 : Real.exp (-(3/2 - η * (122/3))) ≤ EU := by
    have e := (exp_neg_encl 14 (by norm_num) (a := 3/2 - etaHi * (122/3))
      (by norm_num [etaHi]) (by norm_num [etaHi])).2
    refine le_trans (le_trans (Real.exp_le_exp.mpr (by linarith)) e) ?_
    norm_num [EU, etaHi, Finset.sum_range_succ, Nat.factorial]
  have hxL : 1 - 8 * etaHi / 49 ≤ 1 - 8 * η / 49 := by linarith
  have hxU : 1 - 8 * η / 49 ≤ 1 - 8 * etaLo / 49 := by linarith
  have hs1 : sL ≤ Real.sqrt (1 - 8 * η / 49) := by
    rw [show sL = Real.sqrt (sL ^ 2) by rw [Real.sqrt_sq (by norm_num [sL])]]
    exact Real.sqrt_le_sqrt (le_trans (by norm_num [sL, etaHi]) hxL)
  have hs2 : Real.sqrt (1 - 8 * η / 49) ≤ sU := by
    rw [show sU = Real.sqrt (sU ^ 2) by rw [Real.sqrt_sq (by norm_num [sU])]]
    exact Real.sqrt_le_sqrt (le_trans hxU (by norm_num [sU, etaLo]))
  have hxL0 : 0 ≤ 1 - 8 * etaHi / 49 := by norm_num [etaHi]
  have hS0 : 0 < Sq (Real.exp (-η * (2/3))) := Sq_pos (Real.exp_pos _).le
  have hEL0 : 0 ≤ EL := by norm_num [EL]
  have hsL0 : 0 ≤ sL := by norm_num [sL]
  have hEU0 : 0 ≤ EU := by norm_num [EU]
  have hxU0 : 0 ≤ 1 - 8 * etaLo / 49 := by norm_num [etaLo]
  constructor
  · gcongr
  · gcongr

theorem zeta_pos {η : ℝ} (h : ClosureStationary η) : 0 < zeta η := by
  have := (zeta_bracket h).1
  exact lt_of_lt_of_le (by norm_num [EL, sL, etaHi]) this

/-- m_μ/m_e = 720·(2/7)·(1+ζ*) lies in (206.76828023, 206.76828024). -/
theorem muRatio_bracket {η : ℝ} (h : ClosureStationary η) :
    20676828023 / 10 ^ 8 < muRatio η ∧ muRatio η < 20676828024 / 10 ^ 8 := by
  obtain ⟨z1, z2⟩ := zeta_bracket h
  unfold muRatio
  constructor
  · have : 20676828023 / 10 ^ 8 < 720 * (2/7) * (1 + 9 * (EL / (1254365353088095 / 10 ^ 12)) *
        (1 - 8 * etaHi / 49) ^ 10 * sL) := by norm_num [EL, sL, etaHi]
    linarith
  · have : 720 * (2/7) * (1 + 9 * (EU / (1254365353085696 / 10 ^ 12)) *
        (1 - 8 * etaLo / 49) ^ 10 * sU) < 20676828024 / 10 ^ 8 := by norm_num [EU, sU, etaLo]
    linarith

/-- m_τ/m_e = 720²(2/7)⁴(1+ζ*)(1+2ζ*/7) lies in (3477.34330, 3477.34331). -/
theorem tauRatio_bracket {η : ℝ} (h : ClosureStationary η) :
    347734330 / 10 ^ 5 < tauRatio η ∧ tauRatio η < 347734331 / 10 ^ 5 := by
  obtain ⟨z1, z2⟩ := zeta_bracket h
  have z0 := zeta_pos h
  unfold tauRatio
  set zl := 9 * (EL / (1254365353088095 / 10 ^ 12)) * (1 - 8 * etaHi / 49) ^ 10 * sL with hzl
  set zu := 9 * (EU / (1254365353085696 / 10 ^ 12)) * (1 - 8 * etaLo / 49) ^ 10 * sU with hzu
  have hzl0 : 0 ≤ zl := by rw [hzl]; norm_num [EL, sL, etaHi]
  have hzu0 : 0 ≤ zu := le_trans z0.le z2
  constructor
  · have : 347734330 / 10 ^ 5 < 720 ^ 2 * (2/7) ^ 4 * (1 + zl) * (1 + 2/7 * zl) := by
      rw [hzl]; norm_num [EL, sL, etaHi]
    refine lt_of_lt_of_le this ?_
    gcongr
  · have : 720 ^ 2 * (2/7) ^ 4 * (1 + zu) * (1 + 2/7 * zu) < 347734331 / 10 ^ 5 := by
      rw [hzu]; norm_num [EU, sU, etaLo]
    refine lt_of_le_of_lt ?_ this
    gcongr

/-- Zero-load curvature of the dressed ladder: m_τ m_e / m_μ² = (2/7)²(1 + 2ζ/7)/(1 + ζ),
independent of the shell load 720. -/
theorem ladder_curvature {η : ℝ} (h : ClosureStationary η) :
    tauRatio η / muRatio η ^ 2 = (2/7) ^ 2 * (1 + 2/7 * zeta η) / (1 + zeta η) := by
  have hz := zeta_pos h
  unfold tauRatio muRatio
  field_simp <;> ring

/-! ## Horizon normalization and area blocking (App. C.5) -/

/-- n_hor · S_∞^cell = 1/4 for any nonzero lattice Green value G_tet. -/
theorem horizon_quarter (Gtet : ℝ) (hG : Gtet ≠ 0) :
    (8 * Real.pi * Gtet / (3 * Real.log 2)) * (3 * Real.log 2 / (32 * Real.pi * Gtet)) = 1/4 := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp <;> ring

def gammaBI : ℝ := Real.log 2 / (6 * Real.pi)

/-- Channel area a_ch / L*² = 24π γ_BI = 4 ln 2. -/
theorem channel_area : 24 * Real.pi * gammaBI = 4 * Real.log 2 := by
  unfold gammaBI; field_simp <;> ring

/-- Area-blocking identity, for every block size N ≥ 1 (the script checks N = 1, 2, 10, 1000):
Z_A(N) · 8π γ_BI √(3N(3N+1)) = 4 N ln 2 with Z_A(N) = √(3N/(3N+1)). -/
theorem area_blocking (N : ℕ) (hN : 1 ≤ N) :
    Real.sqrt (3 * N / (3 * N + 1)) * (8 * Real.pi * gammaBI) *
      Real.sqrt (3 * N * (3 * N + 1)) = 4 * N * Real.log 2 := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (0 : ℝ) < 3 * N + 1 := by linarith
  have hprod : Real.sqrt (3 * N / (3 * N + 1)) * Real.sqrt (3 * N * (3 * N + 1)) = 3 * N := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show 3 * (N:ℝ) / (3 * N + 1) * (3 * N * (3 * N + 1)) = (3 * N) ^ 2 by field_simp <;> ring]
    exact Real.sqrt_sq (by positivity)
  unfold gammaBI
  calc _ = (Real.sqrt (3 * N / (3 * N + 1)) * Real.sqrt (3 * N * (3 * N + 1))) *
        (8 * Real.pi * (Real.log 2 / (6 * Real.pi))) := by ring
    _ = _ := by rw [hprod]; field_simp <;> ring

/-- ε = g/(4π²) and σ* = π/g at the closure root. -/
theorem epsilon_bracket {η : ℝ} (h : ClosureStationary η) :
    0.1879 < gshare η / (4 * Real.pi ^ 2) ∧ gshare η / (4 * Real.pi ^ 2) < 0.1880 := by
  obtain ⟨g1, g2⟩ := gshare_bracket h
  unfold gLo at g1; unfold gHi at g2
  have p1 := Real.pi_gt_d6; have p2 := Real.pi_lt_d6
  have q1 : (3.141592:ℝ) ^ 2 < Real.pi ^ 2 := pow_lt_pow_left₀ p1 (by norm_num) (by norm_num)
  have q2 : Real.pi ^ 2 < (3.141593:ℝ) ^ 2 := pow_lt_pow_left₀ p2 (by positivity) (by norm_num)
  have hp : 0 < 4 * Real.pi ^ 2 := by positivity
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

/-- One statement for the spine: there is exactly one closure root, and at it
g_share,eff, m_μ/m_e and m_τ/m_e take the manuscript's values to the stated digits. -/
theorem spine_summary :
    ∃! r, ClosureStationary r ∧
      etaLo < r ∧ r < etaHi ∧
      gLo < gshare r ∧ gshare r < gHi ∧
      20676828023 / 10 ^ 8 < muRatio r ∧ muRatio r < 20676828024 / 10 ^ 8 ∧
      347734330 / 10 ^ 5 < tauRatio r ∧ tauRatio r < 347734331 / 10 ^ 5 := by
  obtain ⟨r, hr, h1, h2⟩ := stationary_exists
  refine ⟨r, ⟨hr, h1, h2, (gshare_bracket hr).1, (gshare_bracket hr).2,
    (muRatio_bracket hr).1, (muRatio_bracket hr).2,
    (tauRatio_bracket hr).1, (tauRatio_bracket hr).2⟩, fun y hy => stationary_unique hy.1 hr⟩

end Entropic.Spine
