import Entropic.EFT.UV.ClosureInvariant

/-!
# Entropic.EFT.UV.Spectrum

LOCAL CONTRACT
* Manuscript: Appendix B.2; Appendix P.
* Assumes: only the exact 1680-state boundary space and `quantumK3` formula.
* Closed outputs: complete eleven-value spectrum and exact degeneracies.
* No floating point; no empirical input.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Entropic.EFT.UV

/-- Exact multiplicity of `3*K^2 = k`. -/
def multiplicity (k : ℤ) : ℕ :=
  (boundaryStates.filter (fun b => quantumK3 b = k)).card

def allowedK3 : Finset ℤ :=
  [122, 134, 142, 146, 152, 154, 158, 162, 164, 166, 170].toFinset

theorem spectrum_complete :
    ∀ b ∈ boundaryStates, quantumK3 b ∈ allowedK3 :=
  forall_boundary (by decide)

theorem mult_122 : multiplicity 122 = 96 := by decide
theorem mult_134 : multiplicity 134 = 96 := by decide
theorem mult_142 : multiplicity 142 = 96 := by decide
theorem mult_146 : multiplicity 146 = 288 := by decide
theorem mult_152 : multiplicity 152 = 192 := by decide
theorem mult_154 : multiplicity 154 = 144 := by decide
theorem mult_158 : multiplicity 158 = 384 := by decide
theorem mult_162 : multiplicity 162 = 192 := by decide
theorem mult_164 : multiplicity 164 = 48 := by decide
theorem mult_166 : multiplicity 166 = 96 := by decide
theorem mult_170 : multiplicity 170 = 48 := by decide

theorem multiplicities_sum :
    multiplicity 122 + multiplicity 134 + multiplicity 142 +
    multiplicity 146 + multiplicity 152 + multiplicity 154 +
    multiplicity 158 + multiplicity 162 + multiplicity 164 +
    multiplicity 166 + multiplicity 170 = 1680 := by
  decide

theorem spectrum_min : ∀ b ∈ boundaryStates, 122 ≤ quantumK3 b :=
  forall_boundary (by decide)
theorem spectrum_max : ∀ b ∈ boundaryStates, quantumK3 b ≤ 170 :=
  forall_boundary (by decide)

/-- Exact K^2 range = (170-122)/3 = 16. -/
theorem spectrum_range : ((170 : ℚ) - 122) / 3 = 16 := by norm_num

/-- Any sum of a function of 3K² over the ensemble regroups by level with the exact
multiplicities. -/
theorem sum_by_level {M : Type*} [AddCommMonoid M] (φ : ℤ → M) :
    ∑ b ∈ boundaryStates, φ (quantumK3 b) =
      96 • φ 122 + 96 • φ 134 + 96 • φ 142 + 288 • φ 146 + 192 • φ 152 + 144 • φ 154 +
      384 • φ 158 + 192 • φ 162 + 48 • φ 164 + 96 • φ 166 + 48 • φ 170 := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := quantumK3) (t := allowedK3) spectrum_complete]
  have hfib : ∀ k, ∑ b ∈ boundaryStates with quantumK3 b = k, φ (quantumK3 b) =
      multiplicity k • φ k := by
    intro k
    rw [Finset.sum_congr rfl (fun b hb => by rw [(Finset.mem_filter.mp hb).2])]
    rw [Finset.sum_const]; rfl
  simp only [hfib]
  rw [show allowedK3 = {122, 134, 142, 146, 152, 154, 158, 162, 164, 166, 170} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [mult_122, mult_134, mult_142, mult_146, mult_152, mult_154, mult_158, mult_162, mult_164,
    mult_166, mult_170]
  abel

end Entropic.EFT.UV
