import EntropicEFT.Gauge.VertexRealization
import EntropicEFT.Marked.SingleStrandRecord

/-!
# EntropicEFT.Structure.Connections

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

namespace EntropicEFT.Structure
open EntropicEFT.UV EntropicEFT.Marked EntropicEFT.Gauge

/-- The support of a code: the set of occupied channels. -/
def support (b : BoundaryCode) : Finset Label :=
  {b.assignment.m0, b.assignment.m1, b.assignment.m2, b.assignment.m3}

/-- (1) UNIVERSAL CHANNEL SHARING: two injective four-port codes over a seven-channel
alphabet must overlap.  The capacity graph on the full ensemble is complete. -/
theorem support_card_four : ∀ b ∈ boundaryStates, (support b).card = 4 := by
  native_decide

/-- Pigeonhole at the subset level: two 4-element subsets of a 7-element alphabet
must intersect (4 + 4 > 7). -/
theorem four_subsets_share : ∀ s t : Finset Label,
    s.card = 4 → t.card = 4 → (s ∩ t).Nonempty := by
  native_decide

theorem universal_channel_sharing :
    ∀ b ∈ boundaryStates, ∀ b' ∈ boundaryStates,
      (support b ∩ support b').Nonempty :=
  fun b hb b' hb' =>
    four_subsets_share _ _ (support_card_four b hb) (support_card_four b' hb')

/-- (2) JOHNSON FIBRATION: the ensemble fibers over the 35 four-element subsets of the
channel alphabet with constant fiber 48 = 24 orderings × 2 orientations.  This is the
48 × 35 locality fracture of the simulation, as combinatorics. -/
theorem johnson_fibration :
    (∀ s ∈ (Finset.univ : Finset Label).powersetCard 4,
        (boundaryStates.filter (fun b => support b = s)).card = 48) ∧
    ((Finset.univ : Finset Label).powersetCard 4).card = 35 ∧
    35 * 48 = 1680 := by
  refine ⟨by native_decide, by native_decide, by norm_num⟩

/-- (3) EXACT FLAT MEAN: the unweighted ensemble sum of 3K² is exactly 255360, so the
flat mean of K² is exactly 152/3.  The measured Gibbs mean ≈ 50.223 is this rational
number tilted by e^{-η*K²}. -/
theorem unweighted_mean_exact :
    (boundaryStates.sum quantumK3) = 255360 ∧ 255360 = 1680 * 152 := by
  refine ⟨by native_decide, by norm_num⟩

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

end EntropicEFT.Structure
