import Mathlib.Algebra.Lie.Classical
import Mathlib.Tactic

/-! Second pass, chunk 19: a Lie subalgebra of 𝔤𝔩(n, ℂ) that contains the Chevalley generators
E_{i,i+1}, E_{i+1,i} contains every traceless matrix. Used with kernel-checked bracket certificates to
identify generated Lie algebras with 𝔰𝔩(n, ℂ). -/

namespace Entropic.Pass2.SlGen
open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

/-- Matrix unit E_ij. -/
noncomputable abbrev E (i j : Fin n) : Matrix (Fin n) (Fin n) ℂ := single i j 1

theorem bracket_units (i j k : Fin n) (hik : i ≠ k) : ⁅E i j, E j k⁆ = E i k := by
  have h0 : single j k (1:ℂ) * single i j 1 = 0 := by
    rw [single_mul_single_of_ne]; exact Ne.symm hik
  simp only [E, Ring.lie_def, single_mul_single_same, h0, mul_one, sub_zero]

theorem bracket_diag (i j : Fin n) : ⁅E i j, E j i⁆ = E i i - E j j := by
  simp only [E, Ring.lie_def, single_mul_single_same, mul_one]

variable (L : LieSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))

theorem upper_mem
    (hup : ∀ (i : ℕ) (h : i + 1 < n), E ⟨i, by omega⟩ ⟨i + 1, h⟩ ∈ L) :
    ∀ d i (h : i + d + 1 < n), E ⟨i, by omega⟩ ⟨i + d + 1, h⟩ ∈ L := by
  intro d
  induction d with
  | zero => intro i h; simpa using hup i h
  | succ d ih =>
    intro i h
    have h1 := ih i (by omega)
    have h2 := hup (i + d + 1) (by omega)
    have := L.lie_mem h1 h2
    rw [bracket_units] at this
    · simpa [show i + (d + 1) + 1 = i + d + 1 + 1 by omega] using this
    · intro e; simp [Fin.ext_iff] at e <;> omega

theorem lower_mem
    (hdn : ∀ (i : ℕ) (h : i + 1 < n), E ⟨i + 1, h⟩ ⟨i, by omega⟩ ∈ L) :
    ∀ d i (h : i + d + 1 < n), E ⟨i + d + 1, h⟩ ⟨i, by omega⟩ ∈ L := by
  intro d
  induction d with
  | zero => intro i h; simpa using hdn i h
  | succ d ih =>
    intro i h
    have h1 := hdn (i + d + 1) (by omega)
    have h2 := ih i (by omega)
    have := L.lie_mem h1 h2
    rw [bracket_units] at this
    · simpa [show i + (d + 1) + 1 = i + d + 1 + 1 by omega] using this
    · intro e; simp [Fin.ext_iff] at e <;> omega

theorem offdiag_mem
    (hup : ∀ (i : ℕ) (h : i + 1 < n), E ⟨i, by omega⟩ ⟨i + 1, h⟩ ∈ L)
    (hdn : ∀ (i : ℕ) (h : i + 1 < n), E ⟨i + 1, h⟩ ⟨i, by omega⟩ ∈ L) (i j : Fin n) (hij : i ≠ j) :
    E i j ∈ L := by
  rcases lt_or_gt_of_ne hij with h | h
  · have := upper_mem L hup (j.val - i.val - 1) i.val (by omega)
    convert this using 2 <;> ext <;> simp <;> omega
  · have := lower_mem L hdn (i.val - j.val - 1) j.val (by omega)
    convert this using 2 <;> ext <;> simp <;> omega

/-- Chevalley generators generate 𝔰𝔩(n): every traceless matrix lies in L. -/
theorem traceless_mem (hn : 0 < n)
    (hup : ∀ (i : ℕ) (h : i + 1 < n), E ⟨i, by omega⟩ ⟨i + 1, h⟩ ∈ L)
    (hdn : ∀ (i : ℕ) (h : i + 1 < n), E ⟨i + 1, h⟩ ⟨i, by omega⟩ ∈ L)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.trace = 0) : X ∈ L := by
  set z : Fin n := ⟨0, hn⟩
  have hoff := offdiag_mem L hup hdn
  have hdiag : ∀ i : Fin n, E i i - E z z ∈ L := by
    intro i
    by_cases hi : i = z
    · subst hi; simp
    · rw [← bracket_diag i z]; exact L.lie_mem (hoff i z hi) (hoff z i (Ne.symm hi))
  have hdecomp : X = ∑ i, ∑ j, (if i = j then X i i • (E i i - E z z) else X i j • E i j) := by
    have hsum : ∑ i, ∑ j, (if i = j then X i i • E z z else 0) = X.trace • E z z := by
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.trace, Matrix.diag, Finset.sum_smul]
    conv_lhs => rw [matrix_eq_sum_single X]
    have : ∀ i j, (if i = j then X i i • (E i i - E z z) else X i j • E i j) =
        single i j (X i j) - (if i = j then X i i • E z z else 0) := by
      intro i j
      split_ifs with h
      · subst h; rw [smul_sub]; simp [E, smul_single]
      · simp [E, smul_single]
    simp only [this, Finset.sum_sub_distrib, hsum, hX, zero_smul, sub_zero]
  rw [hdecomp]
  refine L.sum_mem fun i _ => L.sum_mem fun j _ => ?_
  split_ifs with h
  · exact L.smul_mem _ (hdiag i)
  · exact L.smul_mem _ (hoff i j h)

end Entropic.Pass2.SlGen
