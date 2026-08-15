import EntropicEFT.UV.Boundary

/-!
# EntropicEFT.UV.ClosureInvariant

LOCAL CONTRACT
* Manuscript: Appendix B.2 and the corrected H.9 audit.
* Critical separation:
    `quantumK3 = 3 <C_hat^2>`;
    `classicalClosure3 = 3 |<C_hat>|^2`.
* Closed outputs: exact decomposition and finite bounds on all 1680 states.
* Downstream rule: no marked/Gaussian module may identify these two quantities.
-/

namespace EntropicEFT.UV

def sumM (a : PortAssignment) : ℤ :=
  labelInt a.m0 + labelInt a.m1 + labelInt a.m2 + labelInt a.m3

def sumSq (a : PortAssignment) : ℤ :=
  labelInt a.m0 * labelInt a.m0 +
  labelInt a.m1 * labelInt a.m1 +
  labelInt a.m2 * labelInt a.m2 +
  labelInt a.m3 * labelInt a.m3

/-- `3*K^2 = 144 - S^2 + Sigma^2` for j_eff=3. -/
def quantumK3 (b : BoundaryCode) : ℤ :=
  144 - (sumM b.assignment)^2 + sumSq b.assignment

/-- `3*|c|^2 = 4 Sigma^2 - S^2` for regular tetrahedral normals. -/
def classicalClosure3 (b : BoundaryCode) : ℤ :=
  4 * sumSq b.assignment - (sumM b.assignment)^2

/-- Three times the irreducible quantum variance `V_q = 48 - Sigma^2`. -/
def quantumVariance3 (b : BoundaryCode) : ℤ :=
  3 * (48 - sumSq b.assignment)

/-- Exact operator-expectation decomposition. -/
theorem closure_decomposition (b : BoundaryCode) :
    quantumK3 b = classicalClosure3 b + quantumVariance3 b := by
  simp [quantumK3, classicalClosure3, quantumVariance3]
  ring

/-- Injectivity makes the mean classical closure nonzero everywhere: |c|^2 >= 20/3. -/
theorem classicalClosure3_lower_bound :
    ∀ b ∈ boundaryStates, 20 ≤ classicalClosure3 b := by
  native_decide

/-- Exact upper bound: |c|^2 <= 104/3. -/
theorem classicalClosure3_upper_bound :
    ∀ b ∈ boundaryStates, classicalClosure3 b ≤ 104 := by
  native_decide

/-- The irreducible quantum variance is quantitatively large: 22 <= V_q <= 42. -/
theorem quantumVariance3_bounds :
    ∀ b ∈ boundaryStates, 66 ≤ quantumVariance3 b ∧ quantumVariance3 b ≤ 126 := by
  native_decide

/-- Consequently the two closure quantities are nowhere equal on the physical ensemble. -/
theorem quantumK3_ne_classicalClosure3 :
    ∀ b ∈ boundaryStates, quantumK3 b ≠ classicalClosure3 b := by
  intro b hb hEq
  have hv := (quantumVariance3_bounds b hb).1
  have hd := closure_decomposition b
  omega

/-- Real-valued forms used by the Gibbs and marked modules. -/
noncomputable def quantumK2R (b : BoundaryCode) : ℝ := (quantumK3 b : ℝ) / 3

noncomputable def classicalClosureSqR (b : BoundaryCode) : ℝ := (classicalClosure3 b : ℝ) / 3

noncomputable def quantumVarianceR (b : BoundaryCode) : ℝ := (quantumVariance3 b : ℝ) / 3

theorem closure_decomposition_real (b : BoundaryCode) :
    quantumK2R b = classicalClosureSqR b + quantumVarianceR b := by
  have h : (quantumK3 b : ℝ) =
      (classicalClosure3 b : ℝ) + (quantumVariance3 b : ℝ) := by
    exact_mod_cast closure_decomposition b
  simp only [quantumK2R, classicalClosureSqR, quantumVarianceR]
  linarith

end EntropicEFT.UV
