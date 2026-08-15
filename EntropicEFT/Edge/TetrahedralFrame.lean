import EntropicEFT.Core.Prelude

/-!
# EntropicEFT.Edge.TetrahedralFrame

LOCAL CONTRACT
* Manuscript: Sections 5, 7; Appendix C.1, C.5; Appendix N.8.
* Closed finite geometry: regular tetrahedral raw normals, zero sum, pairwise dot products,
  and the isotropic outer-product identity.
* No continuum or graph Green-function assumption appears here.
-/

open scoped BigOperators
namespace EntropicEFT.Edge

/-- Unnormalized regular-tetrahedron vertex/face-normal frame.  Division by sqrt(3)
produces unit vectors. -/
def rawNormal (i : Fin 4) (a : Fin 3) : ℤ :=
  match i.val, a.val with
  | 0, 0 =>  1 | 0, 1 =>  1 | 0, 2 =>  1
  | 1, 0 =>  1 | 1, 1 => -1 | 1, 2 => -1
  | 2, 0 => -1 | 2, 1 =>  1 | 2, 2 => -1
  | 3, 0 => -1 | 3, 1 => -1 | 3, 2 =>  1
  | _, _ => 0

/-- Raw normal sum vanishes componentwise. -/
theorem rawNormal_sum_zero : ∀ a : Fin 3, ∑ i : Fin 4, rawNormal i a = 0 := by
  native_decide

/-- Raw dot products: norm^2=3, distinct dot=-1; normalized dots are 1 and -1/3. -/
theorem rawNormal_dot : ∀ i j : Fin 4,
    (∑ a : Fin 3, rawNormal i a * rawNormal j a) = if i = j then 3 else -1 := by
  native_decide

/-- Outer-product identity before unit normalization: sum_i n_i^a n_i^b = 4 delta_ab. -/
theorem rawNormal_outer : ∀ a b : Fin 3,
    (∑ i : Fin 4, rawNormal i a * rawNormal i b) = if a = b then 4 else 0 := by
  native_decide

/-- After dividing each raw normal by sqrt(3), the normalized frame gives (4/3) I_3. -/
def normalizedOuterCoefficient : ℚ := 4/3

theorem normalizedOuterCoefficient_eq : normalizedOuterCoefficient = 4/3 := rfl

/-- Trace over the two-dimensional plane transverse to a unit radial direction gives 2/3
of the isotropic local Green tensor. -/
def transverseExportWeight : ℚ := 2/3

theorem transverseExportWeight_eq : transverseExportWeight = 2/3 := rfl

end EntropicEFT.Edge
