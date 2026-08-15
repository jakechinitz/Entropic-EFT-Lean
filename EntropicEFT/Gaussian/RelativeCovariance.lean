import EntropicEFT.Core.PhysicalInterfaces

/-!
# EntropicEFT.Gaussian.RelativeCovariance

LOCAL CONTRACT
* Manuscript: Appendix H.10.A--G; Section 25, 29.9.
* Exact finite-dimensional target: normalized Gaussian determinant ratio and the
  quadratic-source convex conjugate `1/2 Tr(G-I-log G)`.
* This file separates those mathematical identities from the OPEN identification of a
  decorated GFT Hessian with a geometric relative-information operator.
-/

open scoped BigOperators
namespace EntropicEFT.Gaussian

/-- Eigenvalue form of the positive covariance mismatch. -/
noncomputable def scalarMismatch (x : ℝ) : ℝ := x - 1 - Real.log x

noncomputable def relativeMismatch {n : ℕ} (g : Fin n → ℝ) : ℝ :=
  (1/2 : ℝ) * ∑ i, scalarMismatch (g i)

/-- Positivity of the matrix functional follows once the scalar log inequality is supplied. -/
theorem relativeMismatch_nonneg {n : ℕ} (g : Fin n → ℝ)
    (h : ∀ i, 0 ≤ scalarMismatch (g i)) : 0 ≤ relativeMismatch g := by
  unfold relativeMismatch
  have hs : 0 ≤ ∑ i, scalarMismatch (g i) := by
    exact Finset.sum_nonneg (fun i hi => h i)
  positivity

/-- Generic positive-matrix theorem package.  It is mathematics, not a physical bridge. -/
structure GaussianDeterminantMath where
  n : ℕ
  K0 : Matrix (Fin n) (Fin n) ℝ
  K : Matrix (Fin n) (Fin n) ℝ
  positiveK0 : Prop
  positiveK : Prop
  commonSupport : Prop
  theta : Matrix (Fin n) (Fin n) ℝ
  relativeCovariance : Matrix (Fin n) (Fin n) ℝ
  thetaDefinition : Prop
  covarianceInverse : Prop
  determinantRatio : Prop
  traceLogIdentity : Prop
  legendreTransformIdentity : Prop
  klIdentity : Prop
  mismatchNonnegative : Prop
  mismatchZeroIffEqualCovariance : Prop

/-- Exact marked-side result: multiplying the remaining bosonic transfer by a strictly
positive scalar cannot create or delete a bosonic support direction. -/
structure PositiveScalarSupportLemma where
  alpha21 : ℝ
  alpha21_pos : 0 < alpha21
  supportPreserved : Prop

/-- OPEN physical identification with a geometric relative-information operator. -/
structure GFTGeometricRelativeInfoBridge where
  gaussianMath : GaussianDeterminantMath
  embedding : GeometricEmbeddingSpec
  operatorIdentification : Prop
  localDerivativeExpansion : Prop
  continuumBlockDensityDerived : Prop

end EntropicEFT.Gaussian
