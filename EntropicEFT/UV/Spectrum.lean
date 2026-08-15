import EntropicEFT.UV.ClosureInvariant

/-!
# EntropicEFT.UV.Spectrum

LOCAL CONTRACT
* Manuscript: Appendix B.2; Appendix P.
* Assumes: only the exact 1680-state boundary space and `quantumK3` formula.
* Closed outputs: complete eleven-value spectrum and exact degeneracies.
* No floating point; no empirical input.
-/

namespace EntropicEFT.UV

/-- Exact multiplicity of `3*K^2 = k`. -/
def multiplicity (k : ℤ) : ℕ :=
  (boundaryStates.filter (fun b => quantumK3 b = k)).card

def allowedK3 : Finset ℤ :=
  [122, 134, 142, 146, 152, 154, 158, 162, 164, 166, 170].toFinset

theorem spectrum_complete :
    ∀ b ∈ boundaryStates, quantumK3 b ∈ allowedK3 := by
  native_decide

theorem mult_122 : multiplicity 122 = 96 := by native_decide
theorem mult_134 : multiplicity 134 = 96 := by native_decide
theorem mult_142 : multiplicity 142 = 96 := by native_decide
theorem mult_146 : multiplicity 146 = 288 := by native_decide
theorem mult_152 : multiplicity 152 = 192 := by native_decide
theorem mult_154 : multiplicity 154 = 144 := by native_decide
theorem mult_158 : multiplicity 158 = 384 := by native_decide
theorem mult_162 : multiplicity 162 = 192 := by native_decide
theorem mult_164 : multiplicity 164 = 48 := by native_decide
theorem mult_166 : multiplicity 166 = 96 := by native_decide
theorem mult_170 : multiplicity 170 = 48 := by native_decide

theorem multiplicities_sum :
    multiplicity 122 + multiplicity 134 + multiplicity 142 +
    multiplicity 146 + multiplicity 152 + multiplicity 154 +
    multiplicity 158 + multiplicity 162 + multiplicity 164 +
    multiplicity 166 + multiplicity 170 = 1680 := by
  native_decide

theorem spectrum_min : ∀ b ∈ boundaryStates, 122 ≤ quantumK3 b := by native_decide
theorem spectrum_max : ∀ b ∈ boundaryStates, quantumK3 b ≤ 170 := by native_decide

/-- Exact K^2 range = (170-122)/3 = 16. -/
theorem spectrum_range : ((170 : ℚ) - 122) / 3 = 16 := by norm_num

end EntropicEFT.UV
