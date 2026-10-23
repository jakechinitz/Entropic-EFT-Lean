import Entropic.FiniteModel
import Entropic.FiniteStatistics
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Closure root of the finite boundary ensemble (main manuscript App. P).
Closes the analytic steps that `FiniteModel` left as a definition:
existence, uniqueness and a decimal bracket for the stationary eta. -/

noncomputable section
namespace Entropic.ClosureRoot
open Entropic.FiniteModel

/-- The exact spectrum as real pairs (K² value, multiplicity). -/
def specR : List (ℝ × ℝ) :=
  [(122/3, 96), (134/3, 96), (142/3, 96), (146/3, 288), (152/3, 192), (154/3, 144),
   (158/3, 384), (162/3, 192), (164/3, 48), (166/3, 96), (170/3, 48)]

def Z (η : ℝ) : ℝ := (specR.map fun p => p.2 * Real.exp (-η * p.1)).sum
def S1 (η : ℝ) : ℝ := (specR.map fun p => p.2 * p.1 * Real.exp (-η * p.1)).sum
/-- η·S1 − (3/2)·Z, whose zeros are the stationary points. -/
def N (η : ℝ) : ℝ := (specR.map fun p => p.2 * (Real.exp (-η * p.1) * (η * p.1 - 3/2))).sum

theorem partition_eq (η : ℝ) : partition η = Z η := by
  unfold partition Z; rw [exact_spectrum]
  simp only [specR, List.map, List.sum_cons, List.sum_nil]; push_cast; ring_nf

theorem meanK2_eq (η : ℝ) : meanK2 η = S1 η / Z η := by
  unfold meanK2; rw [partition_eq]; congr 1
  unfold S1; rw [exact_spectrum]
  simp only [specR, List.map, List.sum_cons, List.sum_nil]; push_cast; ring_nf

theorem N_eq (η : ℝ) : N η = η * S1 η - 3/2 * Z η := by
  simp only [N, S1, Z, specR, List.map, List.sum_cons, List.sum_nil]; ring

theorem Z_pos (η : ℝ) : 0 < Z η := by
  simp only [Z, specR, List.map, List.sum_cons, List.sum_nil]; positivity

theorem S1_bounds (η : ℝ) : 122/3 * Z η ≤ S1 η ∧ S1 η ≤ 170/3 * Z η := by
  simp only [Z, S1, specR, List.map, List.sum_cons, List.sum_nil]
  have := fun x : ℝ => (Real.exp_pos x).le
  constructor <;> nlinarith [this (-η*(122/3)), this (-η*(134/3)), this (-η*(142/3)),
    this (-η*(146/3)), this (-η*(152/3)), this (-η*(154/3)), this (-η*(158/3)),
    this (-η*(162/3)), this (-η*(164/3)), this (-η*(166/3)), this (-η*(170/3))]

theorem meanK2_bounds (η : ℝ) : 122/3 ≤ meanK2 η ∧ meanK2 η ≤ 170/3 := by
  rw [meanK2_eq]; have hZ := Z_pos η; obtain ⟨h1, h2⟩ := S1_bounds η
  exact ⟨(le_div_iff₀ hZ).mpr (by linarith), (div_le_iff₀ hZ).mpr (by linarith)⟩

theorem stationary_iff (η : ℝ) : ClosureStationary η ↔ 0 < η ∧ N η = 0 := by
  unfold ClosureStationary; rw [meanK2_eq, N_eq]
  have hZ := Z_pos η
  constructor
  · rintro ⟨he, h⟩; refine ⟨he, ?_⟩
    rw [div_eq_iff hZ.ne'] at h; field_simp at h; nlinarith
  · rintro ⟨he, h⟩; refine ⟨he, ?_⟩
    rw [div_eq_div_iff hZ.ne' (by positivity)]; nlinarith

/-- Every stationary point lies in the window [9/340, 9/244]. -/
theorem stationary_in_window {η : ℝ} (h : ClosureStationary η) :
    9/340 ≤ η ∧ η ≤ 9/244 := by
  obtain ⟨he, hm⟩ := h
  obtain ⟨b1, b2⟩ := meanK2_bounds η
  exact Entropic.FiniteStatistics.stationary_window b1 b2 (by rw [hm]; field_simp <;> ring)


/-! ## Strict monotonicity of N below η = 15/340 -/

def Nd (η : ℝ) : ℝ :=
  (specR.map fun p => p.2 * (Real.exp (-η * p.1) * p.1 * (5/2 - η * p.1))).sum

theorem term_hasDerivAt (x η : ℝ) :
    HasDerivAt (fun t => Real.exp (-t * x) * (t * x - 3/2))
      (Real.exp (-η * x) * x * (5/2 - η * x)) η := by
  have h1 : HasDerivAt (fun t => -t * x) (-x) η := by
    simpa using ((hasDerivAt_id η).neg).mul_const x
  have h2 : HasDerivAt (fun t => t * x - 3/2) x η := by
    simpa using ((hasDerivAt_id η).mul_const x).sub_const (3/2)
  convert h1.exp.mul h2 using 1; ring

theorem listSum_hasDerivAt (L : List (ℝ × ℝ)) (η : ℝ) :
    HasDerivAt (fun t => (L.map fun p => p.2 * (Real.exp (-t * p.1) * (t * p.1 - 3/2))).sum)
      ((L.map fun p => p.2 * (Real.exp (-η * p.1) * p.1 * (5/2 - η * p.1))).sum) η := by
  induction L with
  | nil => simpa using hasDerivAt_const η (0 : ℝ)
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ((term_hasDerivAt p.1 η).const_mul p.2).add ih

theorem N_hasDerivAt (η : ℝ) : HasDerivAt N (Nd η) η := listSum_hasDerivAt specR η

theorem Nd_pos {η : ℝ} (h0 : 0 ≤ η) (h1 : η < 15/340) : 0 < Nd η := by
  have key : ∀ x : ℝ, 0 < x → x ≤ 170/3 →
      0 < Real.exp (-η * x) * x * (5/2 - η * x) := by
    intro x hx hxm
    have : η * x < 5/2 := by nlinarith
    have := Real.exp_pos (-η * x)
    have : 0 < 5/2 - η * x := by linarith
    positivity
  simp only [Nd, specR, List.map, List.sum_cons, List.sum_nil]
  nlinarith [key (122/3) (by norm_num) (by norm_num), key (134/3) (by norm_num) (by norm_num),
    key (142/3) (by norm_num) (by norm_num), key (146/3) (by norm_num) (by norm_num),
    key (152/3) (by norm_num) (by norm_num), key (154/3) (by norm_num) (by norm_num),
    key (158/3) (by norm_num) (by norm_num), key (162/3) (by norm_num) (by norm_num),
    key (164/3) (by norm_num) (by norm_num), key (166/3) (by norm_num) (by norm_num),
    key (170/3) (by norm_num) (by norm_num)]

theorem N_continuous : Continuous N :=
  continuous_iff_continuousAt.mpr fun η => (N_hasDerivAt η).continuousAt

theorem N_strictMonoOn : StrictMonoOn N (Set.Icc 0 (15/340)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) N_continuous.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [(N_hasDerivAt x).deriv]
  exact Nd_pos hx.1.le hx.2

/-- The stationary point is unique. -/
theorem stationary_unique {a b : ℝ} (ha : ClosureStationary a) (hb : ClosureStationary b) :
    a = b := by
  obtain ⟨wa1, wa2⟩ := stationary_in_window ha
  obtain ⟨wb1, wb2⟩ := stationary_in_window hb
  obtain ⟨-, Na⟩ := (stationary_iff a).mp ha
  obtain ⟨-, Nb⟩ := (stationary_iff b).mp hb
  exact N_strictMonoOn.injOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (Na.trans Nb.symm)

/-! ## Decimal bracket: rational certificate for the root -/

def P (η q : ℝ) : ℝ :=
  96*(η*(122/3)-3/2)*q^0 +
  96*(η*(134/3)-3/2)*q^6 +
  96*(η*(142/3)-3/2)*q^10 +
  288*(η*(146/3)-3/2)*q^12 +
  192*(η*(152/3)-3/2)*q^15 +
  144*(η*(154/3)-3/2)*q^16 +
  384*(η*(158/3)-3/2)*q^18 +
  192*(η*(162/3)-3/2)*q^20 +
  48*(η*(164/3)-3/2)*q^21 +
  96*(η*(166/3)-3/2)*q^22 +
  48*(η*(170/3)-3/2)*q^24

def Pup (η qL qU : ℝ) : ℝ :=
  96*(η*(122/3)-3/2)*qL^0 +
  96*(η*(134/3)-3/2)*qL^6 +
  96*(η*(142/3)-3/2)*qL^10 +
  288*(η*(146/3)-3/2)*qL^12 +
  192*(η*(152/3)-3/2)*qU^15 +
  144*(η*(154/3)-3/2)*qU^16 +
  384*(η*(158/3)-3/2)*qU^18 +
  192*(η*(162/3)-3/2)*qU^20 +
  48*(η*(164/3)-3/2)*qU^21 +
  96*(η*(166/3)-3/2)*qU^22 +
  48*(η*(170/3)-3/2)*qU^24

def Pdn (η qL qU : ℝ) : ℝ :=
  96*(η*(122/3)-3/2)*qU^0 +
  96*(η*(134/3)-3/2)*qU^6 +
  96*(η*(142/3)-3/2)*qU^10 +
  288*(η*(146/3)-3/2)*qU^12 +
  192*(η*(152/3)-3/2)*qL^15 +
  144*(η*(154/3)-3/2)*qL^16 +
  384*(η*(158/3)-3/2)*qL^18 +
  192*(η*(162/3)-3/2)*qL^20 +
  48*(η*(164/3)-3/2)*qL^21 +
  96*(η*(166/3)-3/2)*qL^22 +
  48*(η*(170/3)-3/2)*qL^24

theorem exp_split (η : ℝ) (j : ℕ) (k : ℝ) (hk : k = (122 + 2 * j) / 3) :
    Real.exp (-η * k) = Real.exp (-η * (122/3)) * Real.exp (-η * (2/3)) ^ j := by
  rw [← Real.exp_nat_mul, ← Real.exp_add, hk]; congr 1; ring

theorem N_factor (η : ℝ) : N η = Real.exp (-η * (122/3)) * P η (Real.exp (-η * (2/3))) := by
  simp only [N, specR, List.map, List.sum_cons, List.sum_nil]
  rw [exp_split η 6 (134/3) (by norm_num)]
  rw [exp_split η 10 (142/3) (by norm_num)]
  rw [exp_split η 12 (146/3) (by norm_num)]
  rw [exp_split η 15 (152/3) (by norm_num)]
  rw [exp_split η 16 (154/3) (by norm_num)]
  rw [exp_split η 18 (158/3) (by norm_num)]
  rw [exp_split η 20 (162/3) (by norm_num)]
  rw [exp_split η 21 (164/3) (by norm_num)]
  rw [exp_split η 22 (166/3) (by norm_num)]
  rw [exp_split η 24 (170/3) (by norm_num)]
  unfold P; ring

theorem tpos {c q b : ℝ} (j : ℕ) (hc : 0 ≤ c) (h0 : 0 ≤ q) (h : q ≤ b) :
    c * q ^ j ≤ c * b ^ j := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h j) hc
theorem tneg {c q b : ℝ} (j : ℕ) (hc : c ≤ 0) (h0 : 0 ≤ b) (h : b ≤ q) :
    c * q ^ j ≤ c * b ^ j := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ h0 h j) hc

theorem P_le_Pup {η q qL qU : ℝ} (he : 0 ≤ η) (hneg : η * (146/3) ≤ 3/2)
    (hpos : 3/2 ≤ η * (152/3)) (h0 : 0 ≤ qL) (hL : qL ≤ q) (hU : q ≤ qU) :
    P η q ≤ Pup η qL qU := by
  have hq : 0 ≤ q := h0.trans hL
  unfold P Pup
  have := tneg 0 (c := 96*(η*(122/3)-3/2)) (by nlinarith) h0 hL
  have := tneg 6 (c := 96*(η*(134/3)-3/2)) (by nlinarith) h0 hL
  have := tneg 10 (c := 96*(η*(142/3)-3/2)) (by nlinarith) h0 hL
  have := tneg 12 (c := 288*(η*(146/3)-3/2)) (by nlinarith) h0 hL
  have := tpos 15 (c := 192*(η*(152/3)-3/2)) (by nlinarith) hq hU
  have := tpos 16 (c := 144*(η*(154/3)-3/2)) (by nlinarith) hq hU
  have := tpos 18 (c := 384*(η*(158/3)-3/2)) (by nlinarith) hq hU
  have := tpos 20 (c := 192*(η*(162/3)-3/2)) (by nlinarith) hq hU
  have := tpos 21 (c := 48*(η*(164/3)-3/2)) (by nlinarith) hq hU
  have := tpos 22 (c := 96*(η*(166/3)-3/2)) (by nlinarith) hq hU
  have := tpos 24 (c := 48*(η*(170/3)-3/2)) (by nlinarith) hq hU
  linarith

theorem Pdn_le_P {η q qL qU : ℝ} (he : 0 ≤ η) (hneg : η * (146/3) ≤ 3/2)
    (hpos : 3/2 ≤ η * (152/3)) (h0 : 0 ≤ qL) (hL : qL ≤ q) (hU : q ≤ qU) :
    Pdn η qL qU ≤ P η q := by
  have hq : 0 ≤ q := h0.trans hL
  unfold P Pdn
  have := tneg 0 (c := 96*(η*(122/3)-3/2)) (by nlinarith) hq hU
  have := tneg 6 (c := 96*(η*(134/3)-3/2)) (by nlinarith) hq hU
  have := tneg 10 (c := 96*(η*(142/3)-3/2)) (by nlinarith) hq hU
  have := tneg 12 (c := 288*(η*(146/3)-3/2)) (by nlinarith) hq hU
  have := tpos 15 (c := 192*(η*(152/3)-3/2)) (by nlinarith) h0 hL
  have := tpos 16 (c := 144*(η*(154/3)-3/2)) (by nlinarith) h0 hL
  have := tpos 18 (c := 384*(η*(158/3)-3/2)) (by nlinarith) h0 hL
  have := tpos 20 (c := 192*(η*(162/3)-3/2)) (by nlinarith) h0 hL
  have := tpos 21 (c := 48*(η*(164/3)-3/2)) (by nlinarith) h0 hL
  have := tpos 22 (c := 96*(η*(166/3)-3/2)) (by nlinarith) h0 hL
  have := tpos 24 (c := 48*(η*(170/3)-3/2)) (by nlinarith) h0 hL
  linarith

/-- Eight-term Taylor enclosure of exp(-a) for 0 ≤ a ≤ 1. -/
theorem exp_neg_enclosure {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    (∑ m ∈ Finset.range 8, (-a) ^ m / m.factorial) - a ^ 8 * (9 / (40320 * 8)) ≤ Real.exp (-a) ∧
    Real.exp (-a) ≤ (∑ m ∈ Finset.range 8, (-a) ^ m / m.factorial) + a ^ 8 * (9 / (40320 * 8)) := by
  have hb := Real.exp_bound (x := -a) (by rw [abs_neg, abs_of_nonneg h0]; exact h1) (n := 8) (by norm_num)
  rw [abs_neg, abs_of_nonneg h0] at hb
  have hf : ((Nat.succ 8 : ℕ) : ℝ) / ((Nat.factorial 8 : ℕ) * (8 : ℕ)) = 9 / (40320 * 8) := by
    norm_num [Nat.factorial]
  rw [hf] at hb
  constructor <;> linarith [(abs_le.mp hb).1, (abs_le.mp hb).2]

def etaLo : ℝ := 298668443934 / 10 ^ 13
def etaHi : ℝ := 298668443936 / 10 ^ 13

theorem N_etaLo_neg : N etaLo < 0 := by
  rw [N_factor]
  apply mul_neg_of_pos_of_neg (Real.exp_pos _)
  have hq := exp_neg_enclosure (a := etaLo * (2/3)) (by norm_num [etaLo]) (by norm_num [etaLo])
  rw [show -(etaLo * (2/3)) = -etaLo * (2/3) by ring] at hq
  have hL : (98028568980156465105 / 10 ^ 20 : ℝ) ≤ Real.exp (-etaLo * (2/3)) := by
    refine le_trans ?_ hq.1; norm_num [etaLo, Finset.sum_range_succ, Nat.factorial]
  have hU : Real.exp (-etaLo * (2/3)) ≤ 98028568980156467106 / 10 ^ 20 := by
    refine le_trans hq.2 ?_; norm_num [etaLo, Finset.sum_range_succ, Nat.factorial]
  refine lt_of_le_of_lt (P_le_Pup (by norm_num [etaLo]) (by norm_num [etaLo])
    (by norm_num [etaLo]) (by norm_num) hL hU) ?_
  norm_num [Pup, etaLo]

theorem N_etaHi_pos : 0 < N etaHi := by
  rw [N_factor]
  apply mul_pos (Real.exp_pos _)
  have hq := exp_neg_enclosure (a := etaHi * (2/3)) (by norm_num [etaHi]) (by norm_num [etaHi])
  rw [show -(etaHi * (2/3)) = -etaHi * (2/3) by ring] at hq
  have hL : (98028568980143394629 / 10 ^ 20 : ℝ) ≤ Real.exp (-etaHi * (2/3)) := by
    refine le_trans ?_ hq.1; norm_num [etaHi, Finset.sum_range_succ, Nat.factorial]
  have hU : Real.exp (-etaHi * (2/3)) ≤ 98028568980143396630 / 10 ^ 20 := by
    refine le_trans hq.2 ?_; norm_num [etaHi, Finset.sum_range_succ, Nat.factorial]
  refine lt_of_lt_of_le ?_ (Pdn_le_P (by norm_num [etaHi]) (by norm_num [etaHi])
    (by norm_num [etaHi]) (by norm_num) hL hU)
  norm_num [Pdn, etaHi]

/-- Existence: a stationary point lies strictly inside the decimal bracket. -/
theorem stationary_exists : ∃ η, ClosureStationary η ∧ etaLo < η ∧ η < etaHi := by
  obtain ⟨η, ⟨h1, h2⟩, hN⟩ := intermediate_value_Ioo (by norm_num [etaLo, etaHi] : etaLo ≤ etaHi)
    N_continuous.continuousOn ⟨N_etaLo_neg, N_etaHi_pos⟩
  exact ⟨η, (stationary_iff η).mpr ⟨lt_trans (by norm_num [etaLo]) h1, hN⟩, h1, h2⟩

/-- Every stationary point lies in (0.0298668443934, 0.0298668443936). -/
theorem stationary_bracket {η : ℝ} (h : ClosureStationary η) : etaLo < η ∧ η < etaHi := by
  obtain ⟨η₀, h₀, hb⟩ := stationary_exists
  rw [stationary_unique h h₀]; exact hb

/-- ∃! form of the closure root. -/
theorem stationary_existsUnique : ∃! η, ClosureStationary η :=
  let ⟨η, h, _⟩ := stationary_exists
  ⟨η, h, fun _ h' => stationary_unique h' h⟩

/-! ## The sharing entropy g_share,eff -/

/-- Gibbs entropy (nats) of the closure ensemble over the 1680 oriented states,
grouped by K² level with the kernel-checked multiplicities. -/
def gshare (η : ℝ) : ℝ :=
  -(specR.map fun p => p.2 * ((Real.exp (-η * p.1) / Z η) * Real.log (Real.exp (-η * p.1) / Z η))).sum

theorem gshare_eq (η : ℝ) : gshare η = Real.log (Z η) + η * meanK2 η := by
  rw [meanK2_eq]
  have hZ := Z_pos η
  have hlog : ∀ x, Real.log (Real.exp (-η * x) / Z η) = -η * x - Real.log (Z η) := by
    intro x; rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  have hZdef : Z η = (specR.map fun p => p.2 * Real.exp (-η * p.1)).sum := rfl
  simp only [gshare, hlog, S1]
  simp only [specR, List.map, List.sum_cons, List.sum_nil] at hZdef ⊢
  generalize Real.exp (-η * (122/3)) = e122 at hZdef ⊢
  generalize Real.exp (-η * (134/3)) = e134 at hZdef ⊢
  generalize Real.exp (-η * (142/3)) = e142 at hZdef ⊢
  generalize Real.exp (-η * (146/3)) = e146 at hZdef ⊢
  generalize Real.exp (-η * (152/3)) = e152 at hZdef ⊢
  generalize Real.exp (-η * (154/3)) = e154 at hZdef ⊢
  generalize Real.exp (-η * (158/3)) = e158 at hZdef ⊢
  generalize Real.exp (-η * (162/3)) = e162 at hZdef ⊢
  generalize Real.exp (-η * (164/3)) = e164 at hZdef ⊢
  generalize Real.exp (-η * (166/3)) = e166 at hZdef ⊢
  generalize Real.exp (-η * (170/3)) = e170 at hZdef ⊢
  generalize Real.log (Z η) = L at hZdef ⊢
  generalize Z η = z at hZ hZdef ⊢
  subst hZdef
  field_simp
  ring

def Sq (q : ℝ) : ℝ :=
  96*q^0 + 96*q^6 + 96*q^10 + 288*q^12 + 192*q^15 + 144*q^16 + 384*q^18 + 192*q^20 + 48*q^21 + 96*q^22 + 48*q^24

theorem Z_factor (η : ℝ) : Z η = Real.exp (-η * (122/3)) * Sq (Real.exp (-η * (2/3))) := by
  simp only [Z, specR, List.map, List.sum_cons, List.sum_nil]
  rw [exp_split η 6 (134/3) (by norm_num)]
  rw [exp_split η 10 (142/3) (by norm_num)]
  rw [exp_split η 12 (146/3) (by norm_num)]
  rw [exp_split η 15 (152/3) (by norm_num)]
  rw [exp_split η 16 (154/3) (by norm_num)]
  rw [exp_split η 18 (158/3) (by norm_num)]
  rw [exp_split η 20 (162/3) (by norm_num)]
  rw [exp_split η 21 (164/3) (by norm_num)]
  rw [exp_split η 22 (166/3) (by norm_num)]
  rw [exp_split η 24 (170/3) (by norm_num)]
  unfold Sq; ring

theorem Sq_mono {q b : ℝ} (h0 : 0 ≤ q) (h : q ≤ b) : Sq q ≤ Sq b := by
  unfold Sq
  have hq : ∀ c : ℝ, c * q ^ 0 = c := by simp
  have := tpos 0 (c := 96) (by norm_num) h0 h
  have := tpos 6 (c := 96) (by norm_num) h0 h
  have := tpos 10 (c := 96) (by norm_num) h0 h
  have := tpos 12 (c := 288) (by norm_num) h0 h
  have := tpos 15 (c := 192) (by norm_num) h0 h
  have := tpos 16 (c := 144) (by norm_num) h0 h
  have := tpos 18 (c := 384) (by norm_num) h0 h
  have := tpos 20 (c := 192) (by norm_num) h0 h
  have := tpos 21 (c := 48) (by norm_num) h0 h
  have := tpos 22 (c := 96) (by norm_num) h0 h
  have := tpos 24 (c := 48) (by norm_num) h0 h
  simp only [pow_zero, mul_one] at *
  linarith

theorem Sq_pos {q : ℝ} (h0 : 0 ≤ q) : 0 < Sq q := by unfold Sq; positivity

theorem log_Z_eq (η : ℝ) : Real.log (Z η) = -η * (122/3) + Real.log (Sq (Real.exp (-η * (2/3)))) := by
  rw [Z_factor, Real.log_mul (Real.exp_pos _).ne' (Sq_pos (Real.exp_pos _).le).ne', Real.log_exp]

theorem qLo_U : Real.exp (-etaLo * (2/3)) ≤ 98028568980156467106 / 10 ^ 20 := by
  have hq := exp_neg_enclosure (a := etaLo * (2/3)) (by norm_num [etaLo]) (by norm_num [etaLo])
  rw [show -(etaLo * (2/3)) = -etaLo * (2/3) by ring] at hq
  refine le_trans hq.2 ?_; norm_num [etaLo, Finset.sum_range_succ, Nat.factorial]

theorem qHi_L : (98028568980143394629 / 10 ^ 20 : ℝ) ≤ Real.exp (-etaHi * (2/3)) := by
  have hq := exp_neg_enclosure (a := etaHi * (2/3)) (by norm_num [etaHi]) (by norm_num [etaHi])
  rw [show -(etaHi * (2/3)) = -etaHi * (2/3) by ring] at hq
  refine le_trans ?_ hq.1; norm_num [etaHi, Finset.sum_range_succ, Nat.factorial]

/-- Ten-term Taylor bounds used for log(Sq/1024). -/
theorem exp_upper10 {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    Real.exp a ≤ (∑ m ∈ Finset.range 10, a ^ m / m.factorial) + a ^ 10 * (10 + 1) / (Nat.factorial 10 * 10) :=
  by simpa using Real.exp_bound' h0 h1 (n := 10) (by norm_num)

theorem exp_lower10 {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    (∑ m ∈ Finset.range 10, a ^ m / m.factorial) - a ^ 10 * (11 / (Nat.factorial 10 * 10)) ≤ Real.exp a := by
  have hb := Real.exp_bound (x := a) (by rw [abs_of_nonneg h0]; exact h1) (n := 10) (by norm_num)
  rw [abs_of_nonneg h0] at hb
  have := (abs_le.mp hb).1
  push_cast at this ⊢
  linarith

/-- Enclosure of the reduced partition sum at any η in the root bracket. -/
theorem Sq_bracket {η : ℝ} (b1 : etaLo < η) (b2 : η < etaHi) :
    (1254365353085696 / 10 ^ 12 : ℝ) ≤ Sq (Real.exp (-η * (2/3))) ∧
    Sq (Real.exp (-η * (2/3))) ≤ 1254365353088095 / 10 ^ 12 := by
  have hqU : Real.exp (-η * (2/3)) ≤ 98028568980156467106 / 10 ^ 20 :=
    le_trans (Real.exp_le_exp.mpr (by nlinarith)) qLo_U
  have hqL : (98028568980143394629 / 10 ^ 20 : ℝ) ≤ Real.exp (-η * (2/3)) :=
    le_trans qHi_L (Real.exp_le_exp.mpr (by nlinarith))
  exact ⟨le_trans (by norm_num [Sq]) (Sq_mono (by norm_num) hqL),
    le_trans (Sq_mono (Real.exp_pos _).le hqU) (by norm_num [Sq])⟩

def gLo : ℝ := 74198000220 / 10 ^ 10
def gHi : ℝ := 74198000250 / 10 ^ 10

/-- g_share,eff at the closure root: 7.4198000220 < g < 7.4198000250. -/
theorem gshare_bracket {η : ℝ} (h : ClosureStationary η) : gLo < gshare η ∧ gshare η < gHi := by
  obtain ⟨b1, b2⟩ := stationary_bracket h
  have hroot : η * meanK2 η = 3/2 := by
    obtain ⟨he, hm⟩ := h; rw [hm]; field_simp <;> ring
  rw [gshare_eq, hroot, log_Z_eq]
  -- q at the root, enclosed using monotonicity of exp
  have hqU : Real.exp (-η * (2/3)) ≤ 98028568980156467106 / 10 ^ 20 :=
    le_trans (Real.exp_le_exp.mpr (by nlinarith)) qLo_U
  have hqL : (98028568980143394629 / 10 ^ 20 : ℝ) ≤ Real.exp (-η * (2/3)) :=
    le_trans qHi_L (Real.exp_le_exp.mpr (by nlinarith))
  have hSU : Sq (Real.exp (-η * (2/3))) ≤ 1254365353088095 / 10 ^ 12 :=
    le_trans (Sq_mono (Real.exp_pos _).le hqU) (by norm_num [Sq])
  have hSL : (1254365353085696 / 10 ^ 12 : ℝ) ≤ Sq (Real.exp (-η * (2/3))) :=
    le_trans (by norm_num [Sq]) (Sq_mono (by norm_num) hqL)
  -- log of the rational enclosure: Sq = 1024 · t
  have l2 := abs_le.mp Real.log_two_near_10
  have hpos : (0:ℝ) < 1254365353085696 / 10 ^ 12 := by norm_num
  have hlogL : 10 * Real.log 2 + 2029132233071 / 10 ^ 13 ≤ Real.log (Sq (Real.exp (-η * (2/3)))) := by
    have e : Real.exp (2029132233071 / 10 ^ 13) ≤ 1254365353085696 / 10 ^ 12 / 1024 :=
      le_trans (exp_upper10 (by norm_num) (by norm_num))
        (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have := Real.log_le_log (Real.exp_pos _) e
    rw [Real.log_exp, Real.log_div hpos.ne' (by norm_num)] at this
    have h1024 : Real.log 1024 = 10 * Real.log 2 := by
      rw [show (1024:ℝ) = 2 ^ 10 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log hpos hSL
    linarith
  have hlogU : Real.log (Sq (Real.exp (-η * (2/3)))) ≤ 10 * Real.log 2 + 2029132233093 / 10 ^ 13 := by
    have e : 1254365353088095 / 10 ^ 12 / 1024 ≤ Real.exp (2029132233093 / 10 ^ 13) :=
      le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (exp_lower10 (by norm_num) (by norm_num))
    have := Real.log_le_log (by norm_num) e
    rw [Real.log_exp, Real.log_div (by norm_num) (by norm_num)] at this
    have h1024 : Real.log 1024 = 10 * Real.log 2 := by
      rw [show (1024:ℝ) = 2 ^ 10 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (Sq_pos (Real.exp_pos _).le) hSU
    linarith
  unfold gLo gHi
  unfold etaLo at b1
  unfold etaHi at b2
  constructor <;> nlinarith [l2.1, l2.2]

/-! ## η* is the unique global maximiser of the closure evidence -/

/-- Normalized closure evidence 𝓕(η) = ln Z(η) + (3/2) ln η. -/
def evidence (η : ℝ) : ℝ := Real.log (Z η) + 3/2 * Real.log η

theorem Zsum_hasDerivAt (L : List (ℝ × ℝ)) (η : ℝ) :
    HasDerivAt (fun t => (L.map fun p => p.2 * Real.exp (-t * p.1)).sum)
      (-(L.map fun p => p.2 * p.1 * Real.exp (-η * p.1)).sum) η := by
  induction L with
  | nil => simpa using hasDerivAt_const η (0 : ℝ)
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons, neg_add]
    have h1 : HasDerivAt (fun t => -t * p.1) (-p.1) η := by
      simpa using ((hasDerivAt_id η).neg).mul_const p.1
    have := (h1.exp.const_mul p.2).add ih
    convert this using 1; ring

theorem Z_hasDerivAt (η : ℝ) : HasDerivAt Z (-S1 η) η := Zsum_hasDerivAt specR η

theorem evidence_hasDerivAt {η : ℝ} (he : 0 < η) :
    HasDerivAt evidence (-N η / (η * Z η)) η := by
  have hZ := Z_pos η
  have h := ((Z_hasDerivAt η).log hZ.ne').fun_add ((Real.hasDerivAt_log he.ne').const_mul (3/2))
  convert h using 1
  · funext y; rfl
  · rw [N_eq]; field_simp; ring

/-- Sign of N away from the root. -/
theorem N_neg_below {r η : ℝ} (hr : ClosureStationary r) (h0 : 0 ≤ η) (h : η < r) : N η < 0 := by
  obtain ⟨-, hr2⟩ := stationary_in_window hr
  obtain ⟨-, hN⟩ := (stationary_iff r).mp hr
  rw [← hN]
  exact N_strictMonoOn ⟨h0, by linarith⟩ ⟨by linarith, by linarith⟩ h

theorem N_pos_above {r η : ℝ} (hr : ClosureStationary r) (h : r < η) : 0 < N η := by
  obtain ⟨hr1, -⟩ := stationary_in_window hr
  obtain ⟨-, hN⟩ := (stationary_iff r).mp hr
  by_cases hη : η ≤ 15/340
  · rw [← hN]; exact N_strictMonoOn ⟨by linarith, by linarith⟩ ⟨by linarith, hη⟩ h
  · rw [N_eq]
    have hZ := Z_pos η
    have := (S1_bounds η).1
    nlinarith

/-- The stationary point is the unique global maximiser of the evidence on η > 0. -/
theorem evidence_unique_max {r : ℝ} (hr : ClosureStationary r) {η : ℝ} (he : 0 < η)
    (hne : η ≠ r) : evidence η < evidence r := by
  have hr0 : 0 < r := hr.1
  have cont : ∀ x, 0 < x → ContinuousAt evidence x := fun x hx => (evidence_hasDerivAt hx).continuousAt
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have mono : StrictMonoOn evidence (Set.Icc η r) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      · exact fun x hx => (cont x (by linarith [hx.1])).continuousWithinAt
      · intro x hx; rw [interior_Icc] at hx
        have hx0 : 0 < x := by linarith [hx.1]
        rw [(evidence_hasDerivAt hx0).deriv]
        have := N_neg_below hr hx0.le hx.2
        have := Z_pos x
        apply div_pos (by linarith); positivity
    exact mono ⟨le_refl _, hlt.le⟩ ⟨hlt.le, le_refl _⟩ hlt
  · have anti : StrictAntiOn evidence (Set.Icc r η) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      · exact fun x hx => (cont x (by linarith [hx.1])).continuousWithinAt
      · intro x hx; rw [interior_Icc] at hx
        have hx0 : 0 < x := by linarith [hx.1]
        rw [(evidence_hasDerivAt hx0).deriv]
        have := N_pos_above hr hx.1
        have := Z_pos x
        apply div_neg_of_neg_of_pos (by linarith); positivity
    exact anti ⟨le_refl _, hgt.le⟩ ⟨hgt.le, le_refl _⟩ hgt

/-- Summary: the closure evidence has exactly one maximiser η* on η > 0;
it satisfies the stationary condition, lies in (0.0298668443934, 0.0298668443936),
and gives 7.4198000220 < g_share,eff < 7.4198000250. -/
theorem closure_root_summary :
    ∃ r, ClosureStationary r ∧ etaLo < r ∧ r < etaHi ∧
      (∀ η, 0 < η → η ≠ r → evidence η < evidence r) ∧
      gLo < gshare r ∧ gshare r < gHi := by
  obtain ⟨r, hr, h1, h2⟩ := stationary_exists
  exact ⟨r, hr, h1, h2, fun η he hne => evidence_unique_max hr he hne,
    (gshare_bracket hr).1, (gshare_bracket hr).2⟩

end Entropic.ClosureRoot
