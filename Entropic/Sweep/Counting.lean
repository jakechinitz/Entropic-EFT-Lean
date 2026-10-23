import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-! Chunk 14 sweep: C07-62, the S₇ average of the 21×21 edge permutation matrices. -/

namespace Entropic.Sweep.Count
open Finset

abbrev Pair := {s : Finset (Fin 7) // s.card = 2}

def act (σ : Equiv.Perm (Fin 7)) (t : Pair) : Pair :=
  ⟨t.1.map σ.toEmbedding, by rw [card_map]; exact t.2⟩

theorem act_mul (σ τ : Equiv.Perm (Fin 7)) (t : Pair) : act (τ * σ) t = act τ (act σ t) := by
  apply Subtype.ext; simp [act, Finset.map_map]; rfl

theorem card_pairs : Fintype.card Pair = 21 := by decide

theorem transitive (s s' : Pair) : ∃ τ : Equiv.Perm (Fin 7), act τ s = s' := by
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp s.2
  obtain ⟨c, d, hcd, hs'⟩ := Finset.card_eq_two.mp s'.2
  let τ1 := Equiv.swap a c
  let τ2 := Equiv.swap (τ1 b) d
  have hb : τ1 b ≠ c := by
    intro h; apply hab
    have : τ1 b = τ1 a := by rw [h]; simp [τ1]
    exact (τ1.injective this).symm
  refine ⟨τ2 * τ1, Subtype.ext ?_⟩
  show s.1.map (τ2 * τ1).toEmbedding = s'.1
  rw [hs, hs']
  have e1 : (τ2 * τ1) a = c := by
    simp only [Equiv.Perm.coe_mul, Function.comp, τ2, τ1, Equiv.swap_apply_left]
    rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hb) hcd]
  have e2 : (τ2 * τ1) b = d := by
    simp only [Equiv.Perm.coe_mul, Function.comp, τ2, Equiv.swap_apply_left]
  simp [Finset.map_insert, Finset.map_singleton, e1, e2]

/-- The fibre of t over s. -/
def fibre (t s : Pair) : Finset (Equiv.Perm (Fin 7)) := univ.filter (fun σ => act σ t = s)

theorem fibre_card_eq (t s s' : Pair) : (fibre t s).card = (fibre t s').card := by
  obtain ⟨τ, hτ⟩ := transitive s s'
  refine Finset.card_bij (fun σ _ => τ * σ) ?_ ?_ ?_
  · intro σ hσ; simp only [fibre, mem_filter, mem_univ, true_and] at hσ ⊢; rw [act_mul, hσ, hτ]
  · intro σ₁ _ σ₂ _ h; exact mul_left_cancel h
  · intro ρ hρ
    refine ⟨τ⁻¹ * ρ, ?_, by group⟩
    simp only [fibre, mem_filter, mem_univ, true_and] at hρ ⊢
    rw [act_mul, hρ, ← hτ, ← act_mul, inv_mul_cancel]
    apply Subtype.ext; ext x; simp [act]; rfl

/-- C07-62: for every pair of 2-subsets (s, t), exactly 240 = 5040/21 permutations σ ∈ S₇ send t to s. -/
theorem fibre_card (t s : Pair) : (fibre t s).card = 240 := by
  have hsum : ∑ s' : Pair, (fibre t s').card = Fintype.card (Equiv.Perm (Fin 7)) := by
    rw [← Finset.card_univ]
    exact (Finset.card_eq_sum_card_fiberwise (f := fun σ => act σ t) (fun _ _ => mem_univ _)).symm
  rw [Fintype.card_perm, Fintype.card_fin] at hsum
  have hall : ∀ s', (fibre t s').card = (fibre t s).card := fun s' => fibre_card_eq t s' s
  simp only [hall, sum_const, card_univ, card_pairs, smul_eq_mul] at hsum
  have : (7 : ℕ).factorial = 5040 := by decide
  omega

/-- The 21×21 permutation matrix of σ on 2-subsets: Π_σ e_t = e_{σt}. -/
def Pi (σ : Equiv.Perm (Fin 7)) : Matrix Pair Pair ℚ := fun s t => if act σ t = s then 1 else 0

/-- C07-62: (1/7!) Σ_σ Π_σ = 𝟏𝟏ᵀ/21 (7! = 5040). -/
theorem average (s t : Pair) : (1 / 5040 : ℚ) * ∑ σ, Pi σ s t = 1 / 21 := by
  have : ∑ σ, Pi σ s t = ((fibre t s).card : ℚ) := by
    simp only [Pi, fibre]; rw [Finset.sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
  rw [this, fibre_card]; norm_num

end Entropic.Sweep.Count
