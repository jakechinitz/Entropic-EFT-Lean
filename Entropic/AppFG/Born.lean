import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! Born rule from norm dependence plus orthogonal additivity (ledger C06-45).
If branch weights depend only on the squared norm, w(ψ) = F(‖ψ‖²), with F ≥ 0 additive over
orthogonal splits and F(1) = 1, then F(s) = s on [0, 1]. -/

namespace Entropic.AppFG.Born
open Set

variable {F : ℝ → ℝ} (hnn : ∀ s, 0 ≤ s → s ≤ 1 → 0 ≤ F s)
  (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → s + t ≤ 1 → F (s + t) = F s + F t) (h1 : F 1 = 1)

include hadd in
theorem F_zero : F 0 = 0 := by
  have := hadd 0 0 le_rfl le_rfl (by norm_num); simp at this; linarith

include hnn hadd in
theorem F_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) : F s ≤ F t := by
  have := hadd s (t - s) hs (by linarith) (by linarith)
  rw [add_sub_cancel] at this
  have := hnn (t - s) (by linarith) (by linarith)
  linarith

include hadd in
theorem F_mul {n : ℕ} (hn : 0 < n) : ∀ k : ℕ, k ≤ n → F (k / n) = k * F (1 / n) := by
  intro k
  induction k with
  | zero => intro _; simp [F_zero hadd]
  | succ k ih =>
    intro hk
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    have hk' : (k:ℝ) + 1 ≤ n := by exact_mod_cast hk
    have e : ((k + 1 : ℕ) : ℝ) / n = k / n + 1 / n := by push_cast; ring
    rw [e, hadd _ _ (by positivity) (by positivity) (by rw [← add_div]; rw [div_le_one hn']; linarith),
      ih (by omega)]
    push_cast; ring

include hadd h1 in
theorem F_unit {n : ℕ} (hn : 0 < n) : F (1 / n) = 1 / n := by
  have := F_mul hadd hn n le_rfl
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [div_self hn', h1] at this
  field_simp; linarith

include hnn hadd h1 in
/-- C06-45: F(s) = s on [0, 1]. -/
theorem born (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : F s = s := by
  have bound : ∀ n : ℕ, 0 < n → |F s - s| ≤ 1 / n := by
    intro n hn
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    set k := ⌊s * n⌋₊ with hk
    have hk1 : (k:ℝ) ≤ s * n := Nat.floor_le (by positivity)
    have hk2 : s * n < k + 1 := Nat.lt_floor_add_one _
    have hkn : k ≤ n := by
      have : (k:ℝ) ≤ n := le_trans hk1 (by nlinarith)
      exact_mod_cast this
    have hFk : F (k / n) = k / n := by
      rw [F_mul hadd hn k hkn, F_unit hadd h1 hn]; ring
    have lo : (k:ℝ) / n ≤ s := by rw [div_le_iff₀ hn']; linarith
    rcases Nat.lt_or_ge k n with hlt | hge
    · have hFk1 : F ((k + 1 : ℕ) / n) = (k + 1 : ℕ) / n := by
        rw [F_mul hadd hn (k + 1) hlt, F_unit hadd h1 hn]; ring
      have hi : s ≤ ((k + 1 : ℕ) : ℝ) / n := by
        rw [le_div_iff₀ hn']; push_cast; linarith
      have hi1 : ((k + 1 : ℕ) : ℝ) / n ≤ 1 := by
        rw [div_le_one hn']; exact_mod_cast hlt
      have m1 := F_mono hnn hadd (by positivity) lo hs1
      have m2 := F_mono hnn hadd hs0 hi hi1
      rw [hFk] at m1; rw [hFk1] at m2
      have d : ((k + 1 : ℕ) : ℝ) / n - k / n = 1 / n := by push_cast; ring
      rw [abs_le]; constructor <;> linarith
    · have hkn' : k = n := le_antisymm hkn hge
      have : s = 1 := by
        have : (n:ℝ) ≤ s * n := by
          have e : (k:ℝ) = n := by exact_mod_cast hkn'
          rw [← e]; calc (k:ℝ) ≤ s * n := hk1
            _ = s * k := by rw [e]
        nlinarith
      subst this; rw [h1]; simp
  by_contra hne
  have hpos : 0 < |F s - s| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / |F s - s|)
  have hn0 : 0 < n := by
    have : (0:ℝ) < n := lt_trans (by positivity) hn
    exact_mod_cast this
  have := bound n hn0
  rw [div_lt_iff₀ hpos] at hn
  have hn' : (0:ℝ) < n := by exact_mod_cast hn0
  rw [le_div_iff₀ hn'] at this
  linarith

end Entropic.AppFG.Born
