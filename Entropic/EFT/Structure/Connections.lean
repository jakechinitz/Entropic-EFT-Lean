import Entropic.EFT.Gauge.VertexRealization
import Entropic.EFT.Marked.SingleStrandRecord

/-!
# Entropic.EFT.Structure.Connections

LOCAL CONTRACT
* New structural theorems made visible (and cheap) by the existing formal corpus.
  None were stated in the manuscript; all are consequences of objects already
  kernel-checked, surfaced by having them in one formal namespace.
* Closed here:
  1. `universal_channel_sharing` — any two admissible states share a channel
     (pigeonhole: 4 + 4 > 7).  The capacity-adjacency graph on the ensemble is
     COMPLETE.  Consequence: under geometry = capacity-sharing, locality cannot come
     from connectivity; it must come from weights/dynamics — exactly what the CDT sim
     measured as the short correlation length ξ ≈ 0.57.
  2. `johnson_fibration` — the ensemble fibers over the 35 four-element channel
     subsets (the Johnson scheme J(7,4)) with constant fiber 24 orderings × 2
     orientations = 48.  The 48 × 35 locality fracture observed in the simulation is
     this fibration.
  3. `unweighted_mean_exact` — Σ_ensemble 3K² = 255360, i.e. the flat mean of K² is
     EXACTLY 152/3.  The Gibbs tilt at η* moves it 152/3 → ≈ 50.223: the sim's
     measured mean is a two-term story (exact rational + certified tilt).
  4. `closureVec_bcc` — every closure vector has all-equal coordinate parity
     (≡ S mod 2): the resolved closure vectors are quantized on the body-centered
     sublattice of ℤ³.  Nonclosure is not continuum-valued at the cell level.
  5. `three_halves_bridge` — the stationarity target of the η* equation and the
     single-strand zero-point energy are the SAME rational 3/2, connecting the
     RootExistence and SingleStrandRecord modules by one identity.
  6. `stationarity_bracketing` — the general principle behind the η* window: any
     stationarity root of η·M = c with M ∈ [lo, hi] lies in [c/hi, c/lo].  Stated
     abstractly; the η* window [9/(2·170)·3, 9/244] is the instance lo = 122/3,
     hi = 170/3, c = 3/2.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Entropic.EFT.Structure
open Entropic.EFT.UV Entropic.EFT.Marked Entropic.EFT.Gauge

/-- The support of a code: the set of occupied channels. -/
def support (b : BoundaryCode) : Finset Label :=
  {b.assignment.m0, b.assignment.m1, b.assignment.m2, b.assignment.m3}

/-- (1) UNIVERSAL CHANNEL SHARING: two injective four-port codes over a seven-channel
alphabet must overlap.  The capacity graph on the full ensemble is complete. -/
theorem support_card_four : ∀ b ∈ boundaryStates, (support b).card = 4 :=
  forall_boundary (by decide)

/-- Pigeonhole at the subset level: two 4-element subsets of a 7-element alphabet
must intersect (4 + 4 > 7). -/
theorem four_subsets_share : ∀ s t : Finset Label,
    s.card = 4 → t.card = 4 → (s ∩ t).Nonempty := by
  intro s t hs ht
  rw [← Finset.card_pos]
  have h1 := Finset.card_union_add_card_inter s t
  have h2 : (s ∪ t).card ≤ 7 := by
    simpa using Finset.card_le_univ (s ∪ t)
  omega

theorem universal_channel_sharing :
    ∀ b ∈ boundaryStates, ∀ b' ∈ boundaryStates,
      (support b ∩ support b').Nonempty :=
  fun b hb b' hb' =>
    four_subsets_share _ _ (support_card_four b hb) (support_card_four b' hb')

/-- The 35 four-element subsets of the seven-label alphabet, listed. -/
theorem powersetCard_four_enum : (Finset.univ : Finset Label).powersetCard 4 =
    ({{0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 2, 5}, {0, 1, 2, 6}, {0, 1, 3, 4}, {0, 1, 3, 5}, {0, 1, 3, 6}, {0, 1, 4, 5}, {0, 1, 4, 6}, {0, 1, 5, 6}, {0, 2, 3, 4}, {0, 2, 3, 5}, {0, 2, 3, 6}, {0, 2, 4, 5}, {0, 2, 4, 6}, {0, 2, 5, 6}, {0, 3, 4, 5}, {0, 3, 4, 6}, {0, 3, 5, 6}, {0, 4, 5, 6}, {1, 2, 3, 4}, {1, 2, 3, 5}, {1, 2, 3, 6}, {1, 2, 4, 5}, {1, 2, 4, 6}, {1, 2, 5, 6}, {1, 3, 4, 5}, {1, 3, 4, 6}, {1, 3, 5, 6}, {1, 4, 5, 6}, {2, 3, 4, 5}, {2, 3, 4, 6}, {2, 3, 5, 6}, {2, 4, 5, 6}, {3, 4, 5, 6}} : Finset (Finset Label)) := by decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_0 : (boundaryStates.filter (fun b => support b = {0, 1, 2, 3})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_1 : (boundaryStates.filter (fun b => support b = {0, 1, 2, 4})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_2 : (boundaryStates.filter (fun b => support b = {0, 1, 2, 5})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_3 : (boundaryStates.filter (fun b => support b = {0, 1, 2, 6})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_4 : (boundaryStates.filter (fun b => support b = {0, 1, 3, 4})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_5 : (boundaryStates.filter (fun b => support b = {0, 1, 3, 5})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_6 : (boundaryStates.filter (fun b => support b = {0, 1, 3, 6})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_7 : (boundaryStates.filter (fun b => support b = {0, 1, 4, 5})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_8 : (boundaryStates.filter (fun b => support b = {0, 1, 4, 6})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_9 : (boundaryStates.filter (fun b => support b = {0, 1, 5, 6})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_10 : (boundaryStates.filter (fun b => support b = {0, 2, 3, 4})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_11 : (boundaryStates.filter (fun b => support b = {0, 2, 3, 5})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_12 : (boundaryStates.filter (fun b => support b = {0, 2, 3, 6})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_13 : (boundaryStates.filter (fun b => support b = {0, 2, 4, 5})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_14 : (boundaryStates.filter (fun b => support b = {0, 2, 4, 6})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_15 : (boundaryStates.filter (fun b => support b = {0, 2, 5, 6})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_16 : (boundaryStates.filter (fun b => support b = {0, 3, 4, 5})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_17 : (boundaryStates.filter (fun b => support b = {0, 3, 4, 6})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_18 : (boundaryStates.filter (fun b => support b = {0, 3, 5, 6})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_19 : (boundaryStates.filter (fun b => support b = {0, 4, 5, 6})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_20 : (boundaryStates.filter (fun b => support b = {1, 2, 3, 4})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_21 : (boundaryStates.filter (fun b => support b = {1, 2, 3, 5})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_22 : (boundaryStates.filter (fun b => support b = {1, 2, 3, 6})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_23 : (boundaryStates.filter (fun b => support b = {1, 2, 4, 5})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_24 : (boundaryStates.filter (fun b => support b = {1, 2, 4, 6})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_25 : (boundaryStates.filter (fun b => support b = {1, 2, 5, 6})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_26 : (boundaryStates.filter (fun b => support b = {1, 3, 4, 5})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_27 : (boundaryStates.filter (fun b => support b = {1, 3, 4, 6})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_28 : (boundaryStates.filter (fun b => support b = {1, 3, 5, 6})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_29 : (boundaryStates.filter (fun b => support b = {1, 4, 5, 6})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_30 : (boundaryStates.filter (fun b => support b = {2, 3, 4, 5})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_31 : (boundaryStates.filter (fun b => support b = {2, 3, 4, 6})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_32 : (boundaryStates.filter (fun b => support b = {2, 3, 5, 6})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_33 : (boundaryStates.filter (fun b => support b = {2, 4, 5, 6})).card = 48 := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem fiber_34 : (boundaryStates.filter (fun b => support b = {3, 4, 5, 6})).card = 48 := by decide

/-- (2) JOHNSON FIBRATION: the ensemble fibers over the 35 four-element subsets of the
channel alphabet with constant fiber 48 = 24 orderings × 2 orientations.  This is the
48 × 35 locality fracture of the simulation, as combinatorics. -/
theorem johnson_fibration :
    (∀ s ∈ (Finset.univ : Finset Label).powersetCard 4,
        (boundaryStates.filter (fun b => support b = s)).card = 48) ∧
    ((Finset.univ : Finset Label).powersetCard 4).card = 35 ∧
    35 * 48 = 1680 := by
  refine ⟨?_, by rw [powersetCard_four_enum]; decide, by norm_num⟩
  intro s hs
  rw [powersetCard_four_enum] at hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [fiber_0, fiber_1, fiber_2, fiber_3, fiber_4, fiber_5, fiber_6, fiber_7, fiber_8, fiber_9, fiber_10, fiber_11, fiber_12, fiber_13, fiber_14, fiber_15, fiber_16, fiber_17, fiber_18, fiber_19, fiber_20, fiber_21, fiber_22, fiber_23, fiber_24, fiber_25, fiber_26, fiber_27, fiber_28, fiber_29, fiber_30, fiber_31, fiber_32, fiber_33, fiber_34]

/-- (3) EXACT FLAT MEAN: the unweighted ensemble sum of 3K² is exactly 255360, so the
flat mean of K² is exactly 152/3.  The measured Gibbs mean ≈ 50.223 is this rational
number tilted by e^{-η*K²}. -/
theorem unweighted_mean_exact :
    (boundaryStates.sum quantumK3) = 255360 ∧ 255360 = 1680 * 152 := by
  refine ⟨?_, by norm_num⟩
  have h := sum_by_level (M := ℤ) id
  simp only [id] at h
  rw [show boundaryStates.sum quantumK3 = ∑ b ∈ boundaryStates, quantumK3 b from rfl, h]
  norm_num

/-- (4) BCC QUANTIZATION: every closure vector has all three coordinates of equal
parity (congruent to S mod 2) — the resolved nonclosure lives on the body-centered
sublattice of ℤ³, for EVERY assignment, by pure algebra. -/
theorem closureVec_bcc (a : PortAssignment) :
    ∃ i j k : ℤ,
      (closureVec a).1 - (closureVec a).2.1 = 2*i ∧
      (closureVec a).1 - (closureVec a).2.2 = 2*j ∧
      (closureVec a).1 - sumM a = 2*k := by
  refine ⟨labelInt a.m1 - labelInt a.m2, labelInt a.m1 - labelInt a.m3,
          -(labelInt a.m2) - labelInt a.m3, ?_, ?_, ?_⟩ <;>
    simp only [closureVec, sumM] <;> ring

/-- (5) THE 3/2 BRIDGE: the stationarity target of the η* equation equals the
single-strand record zero-point energy — one rational, two modules, now one theorem. -/
theorem three_halves_bridge :
    (singleStrandZeroPointEnergy : ℚ) = 3/2 ∧
    ∀ η : ℝ, StationaryClosure η → η * meanK2 η = ((3:ℝ)/2) := by
  refine ⟨singleStrandZeroPointEnergy_eq_three_halves, ?_⟩
  intro η h
  exact closure_saturation_of_stationary h

/-- (6) STATIONARITY BRACKETING (general principle): if η·M(η) = c with
lo ≤ M(η) ≤ hi and everything positive, then c/hi ≤ η ≤ c/lo.  The η* window is the
instance (lo, hi, c) = (122/3, 170/3, 3/2). -/
theorem stationarity_bracketing {M : ℝ → ℝ} {η c lo hi : ℝ}
    (hη : 0 < η) (hlo : 0 < lo)
    (hb : lo ≤ M η ∧ M η ≤ hi) (hst : η * M η = c) :
    c/hi ≤ η ∧ η ≤ c/lo := by
  have hMpos : 0 < M η := lt_of_lt_of_le hlo hb.1
  have hhi : 0 < hi := lt_of_lt_of_le hMpos hb.2
  constructor
  · rw [div_le_iff₀ hhi, ← hst]
    exact mul_le_mul_of_nonneg_left hb.2 hη.le
  · rw [le_div_iff₀ hlo, ← hst]
    exact mul_le_mul_of_nonneg_left hb.1 hη.le

end Entropic.EFT.Structure
