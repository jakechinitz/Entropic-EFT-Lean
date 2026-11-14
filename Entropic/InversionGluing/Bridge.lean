import Entropic.DiamondGreen.Walks
import Entropic.AppIJ.Color
import Entropic.AppH1.Kinematics
import Entropic.AppP.Numbers
import Entropic.Compatibility.All
import Entropic.InversionGluing.Core

/-!
# Inversion gluing: bridge to the existing formalization

`Entropic.InversionGluing.Core` proves, with no imports, that cells glued by point inversion through their face
centres form the diamond complex. This file ties that complex to the objects the project already
uses, so that the inversion premise is checked against them and not against copies:

* the bond vectors are `Entropic.EFT.Edge.rawNormal` and `Entropic.AppIJ.tet`;
* the project's diamond adjacency `Entropic.DiamondGreen.dNbr` is the inversion gluing (`embed_nbr`),
  so the Green function, walk, girth and cell-volume theorems are theorems about this complex;
* the manuscript's frame transport, the half turn `Entropic.AppP.Num.mirror`, is unchanged; the
  plane reflection is its negative, and its irrational product angle forbids a closed ring of
  regular mirror-glued cells (`no_mirror_ring`);
* the hopping zero modes hold on both orientation classes;
* `inversion_vacuum_compatible` exhibits one placement satisfying all of these at once, jointly with
  the existing `Entropic.Compatibility.EffectiveModel`.
-/

open scoped BigOperators
open Matrix

set_option maxRecDepth 100000

namespace Entropic.InversionGluing.Bridge
open Entropic.InversionGluing
open Entropic.DiamondGreen (DSite dNbr bond)

/-! ### The bond vectors are the project's -/

theorem tet_eq_rawNormal : ∀ i : Fin 4,
    (tet i).x = Entropic.EFT.Edge.rawNormal i 0 ∧ (tet i).y = Entropic.EFT.Edge.rawNormal i 1 ∧
      (tet i).z = Entropic.EFT.Edge.rawNormal i 2 := by decide

theorem tet_eq_color_tet : ∀ i : Fin 4,
    (tet i).x = Entropic.AppIJ.tet i 0 ∧ (tet i).y = Entropic.AppIJ.tet i 1 ∧
      (tet i).z = Entropic.AppIJ.tet i 2 := by decide

/-! ### The project's diamond adjacency is the inversion gluing -/

theorem bond_x : ∀ i : Fin 4, (tet i).x = 1 - 2 * (bond i).2.1 - 2 * (bond i).2.2 := by decide
theorem bond_y : ∀ i : Fin 4, (tet i).y = 1 - 2 * (bond i).1 - 2 * (bond i).2.2 := by decide
theorem bond_z : ∀ i : Fin 4, (tet i).z = 1 - 2 * (bond i).1 - 2 * (bond i).2.1 := by decide

/-- Placement of the project's diamond sites: A sites at `Σ n_k (tet k - tet 0)`, B sites shifted
by `tet 0`. -/
def embed (u : DSite) : Cell :=
  ⟨u.1, ⟨-2 * u.2.2.1 - 2 * u.2.2.2 + (if u.1 then 1 else 0),
         -2 * u.2.1 - 2 * u.2.2.2 + (if u.1 then 1 else 0),
         -2 * u.2.1 - 2 * u.2.2.1 + (if u.1 then 1 else 0)⟩⟩

/-- `dNbr` is the neighbour rule of the inversion complex. -/
theorem embed_nbr (u : DSite) (i : Fin 4) : embed (dNbr u i) = nbr (embed u) i := by
  obtain ⟨b, n1, n2, n3⟩ := u
  have hx := bond_x i; have hy := bond_y i; have hz := bond_z i
  cases b <;> simp [embed, nbr, dNbr, V3.eq_iff] <;> omega

theorem embed_injective : Function.Injective embed := by
  rintro ⟨b, n1, n2, n3⟩ ⟨c, m1, m2, m3⟩ h
  have h0 : b = c := congrArg Cell.odd h
  subst h0
  have hx := congrArg (fun q : Cell => q.pos.x) h
  have hy := congrArg (fun q : Cell => q.pos.y) h
  have hz := congrArg (fun q : Cell => q.pos.z) h
  cases b
  all_goals
    simp [embed] at hx hy hz
    obtain ⟨e1, e2, e3⟩ : n1 = m1 ∧ n2 = m2 ∧ n3 = m3 := by omega
    subst e1 e2 e3
    rfl

/-- Walks of the project's diamond graph are walks of the inversion complex. -/
theorem embed_walk : ∀ (w : List (Fin 4)) (u : DSite),
    walk w (embed u) = embed (w.foldl dNbr u)
  | [], _ => rfl
  | i :: w, u => by
    simp only [walk, List.foldl_cons]
    rw [← embed_nbr]
    exact embed_walk w (dNbr u i)

/-! ### The frame transport of the manuscript is unchanged -/

/-- The reflection in the face plane is minus the manuscript's half turn: inversion times half turn. -/
theorem plane_reflection_eq (n : Fin 3 → ℝ) :
    -(Entropic.AppP.Num.mirror n) =
      1 - (2 : ℝ) • (Matrix.replicateCol Unit n * Matrix.replicateRow Unit n) := by
  unfold Entropic.AppP.Num.mirror
  exact neg_sub _ _

theorem plane_reflection_det (n : Fin 3 → ℝ) (hn : n ⬝ᵥ n = 1) :
    (-(Entropic.AppP.Num.mirror n)).det = -1 := by
  rw [Matrix.det_neg, (Entropic.AppP.Num.mirror_rotation n hn).2.2.1]
  norm_num

/-- No number of successive pairs of mirror gluings returns the frame: the product angle
`arccos(-7/9) = 2 arccos(1/3)` is not a rational multiple of `π`. -/
theorem no_mirror_ring (m : ℕ) (hm : 0 < m) (k : ℤ) :
    (m : ℝ) * Real.arccos (-7/9) ≠ 2 * Real.pi * k := by
  intro h
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have key : Real.arccos (-7/9) = (2 * (k : ℝ) / (m : ℝ)) * Real.pi := by
    rw [div_mul_eq_mul_div, eq_div_iff hm']; linarith
  exact Entropic.AppP.Num.gluing_angle_irrational ⟨2 * (k : ℚ) / (m : ℚ), by push_cast; exact key⟩

/-! ### The hopping identities hold on both orientation classes -/

theorem gluing_sum_zero_inverted :
    ∑ j : Fin 4, Entropic.AppH1.sdot (-(Entropic.AppCDE.d j)) = 0 := by
  have h : ∀ j : Fin 4, Entropic.AppH1.sdot (-(Entropic.AppCDE.d j)) =
      (((-1 : ℝ)) : ℂ) • Entropic.AppH1.sdot (Entropic.AppCDE.d j) := fun j => by
    rw [← neg_one_smul ℝ (Entropic.AppCDE.d j), Entropic.AppH1.sdot_smul]
  simp_rw [h]
  rw [← Finset.smul_sum, Entropic.AppH1.gluing_sum_zero, smul_zero]

theorem d_dot_inverted (i j : Fin 4) :
    ∑ a, (-(Entropic.AppCDE.d i)) a * (-(Entropic.AppCDE.d j)) a = if i = j then 1 else -1/3 := by
  simp only [Pi.neg_apply, neg_mul_neg]
  exact Entropic.AppCDE.d_dot i j

/-! ### Constants of the cell (bond length 1) -/

/-- `star_1 / star_0`: (face area / hinge length) over cell volume. -/
theorem star_ratio_10 : (4 / Real.sqrt 3) / (8 / (3 * Real.sqrt 3)) = 3 / 2 := by
  have h : Real.sqrt 3 ≠ 0 := by positivity
  field_simp
  ring

/-- Completeness: four bonds per primitive cell, `Σ n nᵀ = (4/3) I`, primitive volume `16/(3√3)`. -/
theorem completeness : (4 / Real.sqrt 3) * (4 / 3) = 16 / (3 * Real.sqrt 3) := by
  have h : Real.sqrt 3 ≠ 0 := by positivity
  field_simp
  ring

/-! ### Compatibility -/

/-- The vacuum cell complex under the inversion premise, stated with the project's own objects. -/
structure InversionVacuum where
  /-- placement of the project's diamond sites in the developed complex -/
  place : DSite → Cell
  place_injective : Function.Injective place
  /-- the project's diamond adjacency is the inversion gluing -/
  place_nbr : ∀ u i, place (dNbr u i) = nbr (place u) i
  /-- neighbours are point inversions of each other -/
  developed : ∀ (g : Iso) (j : Fin 4), (g.comp (invIso j)).cell = nbr g.cell j
  /-- closure rule of the complex -/
  closed : ∀ (w : List (Fin 4)) (c : Cell), walk w c = c ↔
      (cnt 0 w c.odd = 0 ∧ cnt 1 w c.odd = 0 ∧ cnt 2 w c.odd = 0 ∧ cnt 3 w c.odd = 0)
  /-- the manuscript's frame transport keeps its irrational product angle -/
  frame : ¬ ∃ r : ℚ, Real.arccos (-7/9) = r * Real.pi
  /-- zero modes of the hopping operator on the two orientation classes -/
  zero_even : ∑ j : Fin 4, Entropic.AppH1.sdot (Entropic.AppCDE.d j) = 0
  zero_odd : ∑ j : Fin 4, Entropic.AppH1.sdot (-(Entropic.AppCDE.d j)) = 0

theorem inversion_vacuum_compatible : Nonempty InversionVacuum :=
  ⟨{ place := embed
     place_injective := embed_injective
     place_nbr := embed_nbr
     developed := develop
     closed := closed_iff_balanced
     frame := Entropic.AppP.Num.gluing_angle_irrational
     zero_even := Entropic.AppH1.gluing_sum_zero
     zero_odd := gluing_sum_zero_inverted }⟩

/-- Joint inhabitation with the existing effective model. The two structures share no variable. -/
theorem joint_with_effective_model :
    Nonempty (Entropic.Compatibility.EffectiveModel × InversionVacuum) := by
  obtain ⟨m⟩ := Entropic.Compatibility.effective_assumptions_compatible
  obtain ⟨v⟩ := inversion_vacuum_compatible
  exact ⟨(m, v)⟩

end Entropic.InversionGluing.Bridge
