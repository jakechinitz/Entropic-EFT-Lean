import EntropicEFT.UV.EtaStar

/-!
# EntropicEFT.Information.Renewal

LOCAL CONTRACT
* Manuscript: Section 1.2, 3.3, 13; Appendices D.4, G.8, H.4, H.8.
* Closed algebra: definition and uniqueness of the input-independent refresh kernel,
  stationarity once the marginal is normalized, and seven-layer additivity bookkeeping.
* External mathematics interface: Shannon/KL theorem that maximum conditional entropy at
  fixed marginal occurs iff mutual information vanishes.
* Physical premise: faithful full-support history resolution is NOT proved here.
-/

open scoped BigOperators
namespace EntropicEFT.Information

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Classical replacement kernel with prescribed output marginal. -/
noncomputable def refreshKernel (p : α → ℝ) (_a b : α) : ℝ := p b

/-- Input-independence written without information-theory notation. -/
noncomputable def InputIndependent (K : α → α → ℝ) (p : α → ℝ) : Prop :=
  ∀ a b, K a b = p b

theorem refresh_input_independent (p : α → ℝ) :
    InputIndependent (refreshKernel p) p := by
  intro a b
  rfl

theorem input_independent_unique {K : α → α → ℝ} {p : α → ℝ}
    (h : InputIndependent K p) : K = refreshKernel p := by
  funext a b
  exact h a b

/-- The replacement kernel preserves its prescribed marginal. -/
theorem refresh_stationary (p : α → ℝ) (hp : ∑ a, p a = 1) (b : α) :
    ∑ a, p a * refreshKernel p a b = p b := by
  simp [refreshKernel, ← Finset.sum_mul, hp]

/-- External finite-information theorem package; purely mathematical, not physical. -/
structure FiniteEntropyFacts where
  entropy : (α → ℝ) → ℝ
  mutualInfo : (α → α → ℝ) → ℝ
  conditionalEntropy : (α → α → ℝ) → ℝ
  independent : (α → α → ℝ) → Prop
  mutualInfo_nonneg : ∀ joint, 0 ≤ mutualInfo joint
  chainIdentity : ∀ joint, conditionalEntropy joint = entropy (fun b => ∑ a, joint a b) - mutualInfo joint
  zero_iff_independent : ∀ joint, mutualInfo joint = 0 ↔ independent joint

/-- The paper's maximum-caliber step is explicitly conditional on faithful full-support resolution. -/
structure MaximumCaliberSelection where
  faithfulFullSupport : Prop
  fixedMarginal : Prop
  maximumConditionalEntropy : Prop
  selectsRefresh : Prop

/-- Seven resolved channels; this is the combinatorial ceiling, not yet a mass theorem. -/
def resolvedChannelCount : ℕ := 7

theorem pairRecordCount : Nat.choose resolvedChannelCount 2 = 21 := by decide

/-- Entropy-deficit bookkeeping used for the lightest branch. -/
structure LayerEntropyBudget where
  k : ℕ
  marginalEntropy : ℝ
  totalEntropy : ℝ
  deficit : ℝ
  identity : totalEntropy = k * marginalEntropy - deficit
  deficit_nonneg : 0 ≤ deficit

end EntropicEFT.Information
