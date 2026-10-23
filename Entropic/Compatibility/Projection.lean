import Mathlib.Tactic

/-! Finite-volume version of the paper's positive, mass-normalized target.
It repairs negative density by changing the target; it does not prove that
the repaired target still satisfies the unprojected exact acceleration law.
-/
noncomputable section
open scoped BigOperators
namespace Entropic.Compatibility.Projection

variable {I : Type*} [Fintype I]

def positiveMass (raw : I → ℝ) := ∑ i, max (raw i) 0
def projected (budget : ℝ) (raw : I → ℝ) (i : I) := budget*max (raw i) 0/positiveMass raw

theorem positive (budget : ℝ) (raw : I → ℝ) (hB : 0 ≤ budget)
    (hD : 0 < positiveMass raw) (i : I) : 0 ≤ projected budget raw i :=
  div_nonneg (mul_nonneg hB (le_max_right _ _)) hD.le

theorem mass_preserved (budget : ℝ) (raw : I → ℝ) (hD : positiveMass raw ≠ 0) :
    (∑ i, projected budget raw i)=budget := by
  unfold projected
  rw [← Finset.sum_div, ← Finset.mul_sum]
  change budget*positiveMass raw/positiveMass raw=budget
  exact mul_div_cancel_right₀ budget hD

theorem unchanged_if_admissible (raw : I → ℝ) (h : ∀ i, 0 ≤ raw i)
    (hD : (∑ i,raw i) ≠ 0) : projected (∑ i,raw i) raw=raw := by
  have hd : positiveMass raw=∑ i,raw i := by
    unfold positiveMass; apply Finset.sum_congr rfl
    intro i _; exact max_eq_left (h i)
  funext i
  dsimp [projected]
  rw [hd,max_eq_left (h i)]
  field_simp

def signedExample : Fin 2 → ℝ := ![3,-1]

theorem nontrivial_repair (budget : ℝ) (hB : 0 < budget) :
    signedExample 1 < 0 ∧
    (∀ i, 0 ≤ projected budget signedExample i) ∧
    (∑ i, projected budget signedExample i)=budget ∧
    projected budget signedExample 1 ≠ signedExample 1 := by
  have hd : positiveMass signedExample=3 := by norm_num [positiveMass,signedExample,Fin.sum_univ_two]
  refine ⟨by norm_num [signedExample], positive budget signedExample hB.le (by rw [hd]; norm_num),
    mass_preserved budget signedExample (by rw [hd]; norm_num), ?_⟩
  norm_num [projected,signedExample]

end Entropic.Compatibility.Projection
