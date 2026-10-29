import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-! # Release ledger (Appendix O.12, linear-depletion benchmark)

Ledger kinds A and B. As halos assemble, a fraction `η* F(a)` of the committed stock is released, and each
released parcel keeps the density it had at release, `ρ_c0 a⁻³`, as vacuum energy (the linear-depletion
benchmark of App. O.12, `a³ C̄ = B(1 − η* F)`, `I_rel = ∫ a⁻³ dF`):

`ρ_C(a) = ρ_c0 a⁻³ [1 − η* F(a)]`,  `ρ_Λ(a) = η* ρ_c0 ∫ a'⁻³ dF(a')`.

A history is a finite list of release events: event `k` releases the fraction `f k ≥ 0` at scale factor
`a k ∈ (0, 1]`. Units: `ρ_c0 = 1`.

* `committed_add_released`: committed plus released stock is conserved.
* `vacuum_nonneg`, `vacuum_mono`: the vacuum density never decreases as release proceeds (the one-signed
  accumulation that the paper's dark-energy falsifier tests).
* `released_le_releaseIntegral`: `I_rel = ∑ f k / a k³ ≥ F(1)`.
* `early_release_needed`: some release happens at `a³ ≤ F(1)/I_rel`.
* `reference_history_releases_early`: for the paper's reference history (`F(1) = 0.6633922061`,
  `I_rel = 94.2116`), some release happens at `a < 1/5.2`, before redshift 4.2.

Ported from the held-out-test record of 2026-10-26 (`verification/heldout_bestfit_2026-10-26.md`), with the
paper's current reference numbers in place of the 2026-10-26 fit.
-/

noncomputable section

namespace Entropic.ReleaseLedger

open Finset

variable {n : ℕ}

/-- Released fraction `F(1) = ∑ f k`. -/
def released (f : Fin n → ℝ) : ℝ := ∑ k, f k

/-- Release integral `I_rel = ∑ f k / a k³`. -/
def releaseIntegral (a f : Fin n → ℝ) : ℝ := ∑ k, f k / a k ^ 3

/-- Vacuum density today in units of `ρ_c0`. -/
def vacuum (η : ℝ) (a f : Fin n → ℝ) : ℝ := η * releaseIntegral a f

/-- Committed stock today in units of `ρ_c0`. -/
def committed (η : ℝ) (f : Fin n → ℝ) : ℝ := 1 - η * released f

theorem committed_add_released (η : ℝ) (f : Fin n → ℝ) :
    committed η f + η * released f = 1 := by
  unfold committed; ring

/-- A valid history: nonnegative fractions released at scale factors in `(0, 1]`. -/
def Valid (a f : Fin n → ℝ) : Prop := ∀ k, 0 ≤ f k ∧ 0 < a k ∧ a k ≤ 1

theorem vacuum_nonneg {η : ℝ} {a f : Fin n → ℝ} (hη : 0 ≤ η) (h : Valid a f) :
    0 ≤ vacuum η a f := by
  unfold vacuum releaseIntegral
  apply mul_nonneg hη
  apply sum_nonneg
  intro k _
  have := h k
  have : 0 < a k ^ 3 := pow_pos this.2.1 3
  exact div_nonneg (h k).1 this.le

/-- Releasing more never lowers the vacuum density: if every fraction grows, so does `ρ_Λ`. -/
theorem vacuum_mono {η : ℝ} {a f g : Fin n → ℝ} (hη : 0 ≤ η) (ha : ∀ k, 0 < a k)
    (hfg : ∀ k, f k ≤ g k) : vacuum η a f ≤ vacuum η a g := by
  unfold vacuum releaseIntegral
  apply mul_le_mul_of_nonneg_left _ hη
  apply sum_le_sum
  intro k _
  exact div_le_div_of_nonneg_right (hfg k) (pow_pos (ha k) 3).le

/-- `I_rel ≥ F(1)`: every parcel is released at `a ≤ 1`, where `a⁻³ ≥ 1`. -/
theorem released_le_releaseIntegral {a f : Fin n → ℝ} (h : Valid a f) :
    released f ≤ releaseIntegral a f := by
  unfold released releaseIntegral
  apply sum_le_sum
  intro k _
  obtain ⟨hf, ha, ha1⟩ := h k
  have h3 : a k ^ 3 ≤ 1 := pow_le_one₀ ha.le ha1
  have h3p : 0 < a k ^ 3 := pow_pos ha 3
  rw [le_div_iff₀ h3p]
  nlinarith

/-- If `F/I < x` with `F, I, f > 0`, then `f < f (I/F) x`. -/
theorem lt_scaled {F I x f : ℝ} (hF : 0 < F) (hI : 0 < I) (hf : 0 < f) (hx : F / I < x) :
    f < f * (I / F) * x := by
  have hIF : 0 < I / F := div_pos hI hF
  have h3 : 1 < I / F * x := by
    calc (1 : ℝ) = I / F * (F / I) := by field_simp
      _ < I / F * x := mul_lt_mul_of_pos_left hx hIF
  calc f = f * 1 := (mul_one f).symm
    _ < f * (I / F * x) := mul_lt_mul_of_pos_left h3 hf
    _ = f * (I / F) * x := by ring

/-- Some release happens at `a³ ≤ F(1) / I_rel`. -/
theorem early_release_needed {a f : Fin n → ℝ} (h : Valid a f) (hF : 0 < released f) :
    ∃ k, 0 < f k ∧ a k ^ 3 ≤ released f / releaseIntegral a f := by
  have hI : 0 < releaseIntegral a f := lt_of_lt_of_le hF (released_le_releaseIntegral h)
  by_contra hcon
  have hcon' : ∀ k, 0 < f k → released f / releaseIntegral a f < a k ^ 3 := by
    intro k hk
    by_contra hle
    exact hcon ⟨k, hk, not_lt.mp hle⟩
  set F := released f with hFdef
  set I := releaseIntegral a f with hIdef
  have hterm : ∀ k ∈ (univ : Finset (Fin n)), f k / a k ^ 3 ≤ f k * (I / F) := by
    intro k _
    obtain ⟨hf, ha, _⟩ := h k
    have h3p : 0 < a k ^ 3 := pow_pos ha 3
    rcases hf.lt_or_eq with hfpos | hf0
    · rw [div_le_iff₀ h3p]
      exact (lt_scaled hF hI hfpos (hcon' k hfpos)).le
    · rw [← hf0]; simp
  have hstrict : ∃ k ∈ (univ : Finset (Fin n)), f k / a k ^ 3 < f k * (I / F) := by
    have hex : ∃ k, 0 < f k := by
      by_contra hno
      have hle : ∀ k, f k ≤ 0 := fun k => not_lt.mp (fun hk => hno ⟨k, hk⟩)
      have : F ≤ 0 := by
        rw [hFdef]; unfold released
        exact sum_nonpos (fun k _ => hle k)
      linarith
    obtain ⟨k, hk⟩ := hex
    refine ⟨k, mem_univ _, ?_⟩
    obtain ⟨_, ha, _⟩ := h k
    have h3p : 0 < a k ^ 3 := pow_pos ha 3
    rw [div_lt_iff₀ h3p]
    exact lt_scaled hF hI hk (hcon' k hk)
  have hsum := sum_lt_sum hterm hstrict
  have hrhs : ∑ k, f k * (I / F) = I := by
    rw [← sum_mul]
    show F * (I / F) = I
    field_simp
  rw [hrhs] at hsum
  have : releaseIntegral a f = ∑ k, f k / a k ^ 3 := rfl
  linarith

/-- Released fraction of the paper's reference history (App. O.12). -/
def referenceReleased : ℝ := 0.6633922061

/-- Linear-depletion release integral of the paper's reference history (App. O.12). -/
def referenceIntegral : ℝ := 94.2116

/-- The reference history (`F(1) = 0.6633922061`, `I_rel = 94.2116`): some release happens at a scale
factor below `1/5.2`, i.e. before redshift 4.2. -/
theorem reference_history_releases_early {a f : Fin n → ℝ} (h : Valid a f)
    (hF : released f = referenceReleased) (hI : releaseIntegral a f = referenceIntegral) :
    ∃ k, 0 < f k ∧ a k < 1 / 5.2 := by
  have hFpos : 0 < released f := by rw [hF]; unfold referenceReleased; norm_num
  obtain ⟨k, hk, hk3⟩ := early_release_needed h hFpos
  refine ⟨k, hk, ?_⟩
  rw [hF, hI] at hk3
  have hbound : referenceReleased / referenceIntegral < (1 / 5.2) ^ 3 := by
    unfold referenceReleased referenceIntegral; norm_num
  have hlt : a k ^ 3 < (1 / 5.2) ^ 3 := lt_of_le_of_lt hk3 hbound
  obtain ⟨_, ha, _⟩ := h k
  by_contra hge
  have hge' : 1 / 5.2 ≤ a k := not_lt.mp hge
  have : (1 / 5.2 : ℝ) ^ 3 ≤ a k ^ 3 := pow_le_pow_left₀ (by norm_num) hge' 3
  linarith

end Entropic.ReleaseLedger

end
