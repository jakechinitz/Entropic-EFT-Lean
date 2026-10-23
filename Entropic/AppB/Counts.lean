import Entropic.FiniteModel
import Entropic.GenerationCutoff
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Appendix B counts and ensemble symmetries (ledger C04-32, -42, -78, -79, -83, -90). -/

namespace Entropic.AppB
open Entropic.FiniteModel Entropic.GenerationCutoff

/-! ### B.3 rooted reduction (C04-32) -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Rooted closure classes α = (m_root, K²) over the 840 injective tuples: exactly 69. -/
theorem rooted_classes : ((states.map fun s => (s.1, threeK2 s)).dedup).length = 69 := by decide

/-- Rooted microstates (root label, unordered set of the other three labels): exactly
140 = 7·C(6,3). The unordered triple {b,c,d} is encoded by (min, max, sum), which
determines it. K² depends on a state only through this data. -/
def rootedKey (s : FaceState) : Int × Int × Int × Int :=
  let (a, b, c, d) := s
  (a, min (min b c) d, max (max b c) d, b + c + d)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rooted_microstates :
    ((states.map rootedKey).dedup).length = 140 ∧ 7 * Nat.choose 6 3 = 140 := by
  constructor <;> decide

/-! ### B.5.1 branch counts (C04-42, C04-78) -/

/-- Orientation-doubled injective count 2·P(n,4) = 2·n!/(n−4)!. -/
def branchCount (n : ℕ) : ℕ := 2 * Nat.descFactorial n 4

theorem branch_counts : branchCount 4 = 48 ∧ branchCount 5 = 240 ∧ branchCount 7 = 1680 ∧
    branchCount 11 = 15840 ∧ branchCount 16 = 87360 := by
  unfold branchCount; decide

set_option maxRecDepth 100000 in
/-- The state lists of `GenerationCutoff.tuples` realize the same counts. -/
theorem tuples_count_matches :
    2 * (tuples [-3, -2, -1, 0, 1, 2, 3]).length = branchCount 7 ∧
    2 * (tuples [-3, -1, 1, 3]).length = branchCount 4 ∧
    2 * (tuples [-4, -2, 0, 2, 4]).length = branchCount 5 := by
  unfold branchCount; decide

/-! ### B.5.1 the j = 3/2 row (C04-79): constant K², η = 9/100, g = ln 48 -/

/-- Labels in units of 1/2: m ∈ {−3/2, −1/2, 1/2, 3/2} ↦ 2m ∈ {−3, −1, 1, 3}.
For spin j, 4·(3K²)·... we use 12·K² = 48j(j+1)·... ; with half-integer labels written as
2m, 12K² = 12·4j(j+1) − ((Σ2m)² − Σ(2m)²) and for j = 3/2 this is 180 − (S² − Σ²). -/
def twelveK2_j32 (s : FaceState) : Int :=
  let (a, b, c, d) := s
  180 - ((a + b + c + d) ^ 2 - (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2))

theorem j32_constant : (tuples [-3, -1, 1, 3]).all (fun s => twelveK2_j32 s == 200) = true := by
  decide

/-- So K² = 200/12 = 50/3 on every state; stationarity ⟨K²⟩ = 3/(2η) gives η = 9/100,
and the Gibbs measure is uniform on 48 states, so g = ln 48. -/
theorem j32_eta : (3 : ℚ) / (2 * (50/3)) = 9 / 100 := by norm_num

theorem j32_entropy :
    -(∑ _i : Fin 48, (1/48 : ℝ) * Real.log (1/48)) = Real.log 48 := by
  simp [Finset.sum_const, Finset.card_univ, Real.log_inv, one_div]

/-! ### B.5.2 uniform multiplicity rescaling (C04-83) -/

section Rescale
variable {ι : Type*} [Fintype ι] (x : ι → ℝ) (η : ℝ)

noncomputable def Zw (c : ℝ) : ℝ := ∑ i, c * Real.exp (-η * x i)
noncomputable def meanW (c : ℝ) : ℝ := (∑ i, c * x i * Real.exp (-η * x i)) / Zw x η c

/-- Multiplying every multiplicity by c > 0 leaves the Gibbs mean (hence η*) unchanged. -/
theorem mean_rescale_invariant {c : ℝ} (hc : 0 < c) : meanW x η c = meanW x η 1 := by
  unfold meanW Zw
  simp only [mul_assoc, ← Finset.mul_sum, one_mul]
  rw [mul_div_mul_left _ _ hc.ne']

/-- ... and adds ln c to the entropy over the enlarged state space:
with Z' = cZ, ln Z' + η⟨K²⟩ = (ln Z + η⟨K²⟩) + ln c. -/
theorem entropy_rescale [Nonempty ι] {c : ℝ} (hc : 0 < c) :
    Real.log (Zw x η c) + η * meanW x η c = (Real.log (Zw x η 1) + η * meanW x η 1) + Real.log c := by
  have hZ : Zw x η c = c * Zw x η 1 := by unfold Zw; simp [Finset.mul_sum]
  have hpos : 0 < Zw x η 1 := by
    unfold Zw; exact Finset.sum_pos (fun i _ => by simpa using Real.exp_pos _) Finset.univ_nonempty
  rw [mean_rescale_invariant x η hc, hZ, Real.log_mul hc.ne' hpos.ne']; ring

end Rescale

/-! ### B.5 parity-odd tilts (C04-90) -/

section Parity
variable {α : Type*} [DecidableEq α]

/-- If an involution σ maps S to itself, f is odd (f ∘ σ = −f) and g is even (g ∘ σ = g),
then Σ_S f·g = 0. -/
theorem odd_sum_zero (S : Finset α) (σ : α → α) (hσ : ∀ a ∈ S, σ a ∈ S) (hinv : ∀ a, σ (σ a) = a)
    (f g : α → ℝ) (hf : ∀ a, f (σ a) = -f a) (hg : ∀ a, g (σ a) = g a) :
    ∑ a ∈ S, f a * g a = 0 := by
  have h : ∑ a ∈ S, f a * g a = ∑ a ∈ S, f (σ a) * g (σ a) :=
    Finset.sum_nbij' σ σ hσ hσ (fun a _ => hinv a) (fun a _ => hinv a) (fun a _ => by rw [hinv])
  simp only [hf, hg, neg_mul, Finset.sum_neg_distrib] at h
  linarith

/-- Label negation on face states. -/
def negState (s : FaceState) : FaceState := (-s.1, -s.2.1, -s.2.2.1, -s.2.2.2)

theorem negState_invol (s : FaceState) : negState (negState s) = s := by
  obtain ⟨a, b, c, d⟩ := s; simp [negState]

theorem threeK2_even (s : FaceState) : threeK2 (negState s) = threeK2 s := by
  obtain ⟨a, b, c, d⟩ := s; simp only [negState, threeK2]; ring

theorem mem_states (a b c d : Int) : (a, b, c, d) ∈ states ↔
    (a ∈ labels ∧ b ∈ labels ∧ c ∈ labels ∧ d ∈ labels) ∧
      (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) := by
  simp only [states, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨a', ha, b', hb, c', hc, d', hd, h⟩
    split_ifs at h with hne
    · cases h; exact ⟨⟨ha, hb, hc, hd⟩, hne⟩
  · rintro ⟨⟨ha, hb, hc, hd⟩, hne⟩
    exact ⟨a, ha, b, hb, c, hc, d, hd, by rw [ite_eq_left_iff.mpr (fun h => absurd hne h)]⟩

theorem labels_neg : ∀ x ∈ labels, -x ∈ labels := by decide

theorem states_closed : ∀ s ∈ states.toFinset, negState s ∈ states.toFinset := by
  rintro ⟨a, b, c, d⟩ h
  rw [List.mem_toFinset, mem_states] at h
  rw [List.mem_toFinset]
  simp only [negState]
  rw [mem_states]
  obtain ⟨⟨ha, hb, hc, hd⟩, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨⟨labels_neg _ ha, labels_neg _ hb, labels_neg _ hc, labels_neg _ hd⟩,
    by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4,
    by simpa using h5, by simpa using h6⟩

/-- C04-90: for any label-odd observable f, the closure-weighted sum vanishes at every η,
so a parity-odd tilt has zero linear response of η* and g. -/
theorem parity_odd_zero (f : FaceState → ℝ) (hf : ∀ s, f (negState s) = -f s) (φ : Int → ℝ) :
    ∑ s ∈ states.toFinset, f s * φ (threeK2 s) = 0 :=
  odd_sum_zero _ negState states_closed negState_invol f (fun s => φ (threeK2 s)) hf
    (fun s => by rw [threeK2_even])

end Parity

end Entropic.AppB
