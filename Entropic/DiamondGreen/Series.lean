import Entropic.DiamondGreen.Walks

/-!
# The diamond on-site Green function equals one third of the fcc return series

`greenDiamond = ∑_L W_L / 4^(L+1)` is the on-site entry of `(4·I − A_diamond)⁻¹` written as
its Neumann series, i.e. the lattice Green function `G_tet(0)` of the diamond Laplacian with
unit bonds. `returnFCC = ∑_k w_k / 12^k` is the expected number of visits to the origin of the
simple random walk on the fcc lattice (Watson's generating function at `z = 1`). Both are
sums of nonnegative terms, taken in `ℝ≥0∞`, so the identity below holds with no convergence
hypothesis; finiteness follows once either side is known to be finite.
-/

open scoped ENNReal

namespace Entropic.DiamondGreen

/-- `G_tet(0)`: on-site diamond Green function `[(4 − A)⁻¹]₀₀ = ∑_L (A^L)₀₀ / 4^(L+1)`. -/
noncomputable def greenDiamond : ℝ≥0∞ :=
  ∑' L, (dWalks L (false, 0) (false, 0) : ℝ≥0∞) / 4 ^ (L + 1)

/-- Expected visits to the origin of the fcc simple random walk, `∑_k (P^k)₀₀`. -/
noncomputable def returnFCC : ℝ≥0∞ := ∑' k, (fWalks k 0 0 : ℝ≥0∞) / 12 ^ k

/-! ### Bipartiteness: odd A→A walks vanish -/

theorem dNbr_fst (u : DSite) (i : Fin 4) : (dNbr u i).1 = !u.1 := by
  obtain ⟨b, n⟩ := u; cases b <;> rfl

theorem dWalks_parity : ∀ (L : ℕ) (u v : DSite), dWalks L u v ≠ 0 → (u.1 = v.1 ↔ Even L)
  | 0, u, v, h => by
    simp only [dWalks, ne_eq, ite_eq_right_iff, Classical.not_imp] at h
    simp [h.1]
  | L + 1, u, v, h => by
    simp only [dWalks] at h
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have ih := dWalks_parity L _ _ hi
    rw [dNbr_fst] at ih
    rw [Nat.even_add_one, ← ih]
    cases u.1 <;> cases v.1 <;> simp

theorem dWalks_odd (n : ℕ) (y x : Z3) : dWalks (2 * n + 1) (false, y) (false, x) = 0 := by
  by_contra h
  have := (dWalks_parity _ _ _ h).1 rfl
  exact Nat.not_even_two_mul_add_one n this

/-! ### Real-valued helpers -/

theorem nat_div_pow (a q p : ℕ) (hq : 0 < q) :
    (a : ℝ≥0∞) / (q : ℝ≥0∞) ^ p = ENNReal.ofReal ((a : ℝ) / (q : ℝ) ^ p) := by
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]

theorem div_four_pow (a p : ℕ) :
    (a : ℝ≥0∞) / (4 : ℝ≥0∞) ^ p = ENNReal.ofReal ((a : ℝ) / (4 : ℝ) ^ p) := by
  simpa using nat_div_pow a 4 p (by norm_num)

private theorem div_twelve_pow (a p : ℕ) :
    (a : ℝ≥0∞) / (12 : ℝ≥0∞) ^ p = ENNReal.ofReal ((a : ℝ) / (12 : ℝ) ^ p) := by
  simpa using nat_div_pow a 12 p (by norm_num)

/-- Negative binomial series at `r = 1/4`. -/
private theorem negbin (k : ℕ) :
    HasSum (fun m : ℕ => ((m + k).choose k : ℝ) * (1 / 4 : ℝ) ^ m) ((4 / 3 : ℝ) ^ (k + 1)) := by
  have h := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) k (r := 1 / 4)
    (by rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]; norm_num)
  convert h using 1
  rw [one_div, ← inv_pow]; norm_num

/-- The inner sum over walk lengths `2(m+k)` that contain exactly `k` fcc steps. -/
private theorem inner_sum (k f : ℕ) :
    ∑' m : ℕ, ENNReal.ofReal (((m + k).choose k : ℝ) * 4 ^ m * f / 4 ^ (2 * (m + k) + 1)) =
      ENNReal.ofReal ((f : ℝ) / 12 ^ k / 3) := by
  have hs := (negbin k).mul_left ((f : ℝ) / 4 ^ (2 * k + 1))
  have key : ∀ m : ℕ, ((m + k).choose k : ℝ) * 4 ^ m * f / 4 ^ (2 * (m + k) + 1) =
      (f : ℝ) / 4 ^ (2 * k + 1) * (((m + k).choose k : ℝ) * (1 / 4 : ℝ) ^ m) := by
    intro m
    rw [show 2 * (m + k) + 1 = m + (m + (2 * k + 1)) by ring, pow_add, pow_add, one_div_pow]
    field_simp
  simp_rw [key]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hs.summable, hs.tsum_eq]
  congr 1
  rw [show (12 : ℝ) ^ k = 4 ^ k * 3 ^ k by rw [← mul_pow]; norm_num,
    show 2 * k + 1 = k + k + 1 by ring, div_pow, pow_add, pow_add, pow_succ (3 : ℝ)]
  field_simp
  ring

/-- **`G_tet(0) = P_fcc / 3`.** The on-site diamond Green function equals one third of the
fcc return series, with no convergence hypothesis (identity in `[0, ∞]`). -/
theorem greenDiamond_eq : greenDiamond = returnFCC / 3 := by
  unfold greenDiamond returnFCC
  set d : ℕ → ℝ≥0∞ := fun L => (dWalks L (false, 0) (false, 0) : ℝ≥0∞) / 4 ^ (L + 1) with hd
  rw [← tsum_even_add_odd (f := d) ENNReal.summable ENNReal.summable]
  have hodd : ∀ n, d (2 * n + 1) = 0 := fun n => by simp [hd, dWalks_odd]
  simp only [hodd, tsum_zero, add_zero]
  -- even lengths: expand by the diamond → fcc reduction
  have heven : ∀ n, d (2 * n) = ∑' k : ℕ, if k ≤ n then
      ENNReal.ofReal (((n - k + k).choose k : ℝ) * 4 ^ (n - k) * fWalks k 0 0 /
        4 ^ (2 * (n - k + k) + 1)) else 0 := by
    intro n
    rw [tsum_eq_sum (s := Finset.range (n + 1)) (fun k hk => by
      simp only [Finset.mem_range, not_lt] at hk; simp [show ¬ k ≤ n by omega])]
    rw [hd]; dsimp only
    rw [dWalks_even, div_four_pow]
    push_cast
    rw [Finset.sum_div, ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [Nat.sub_add_cancel hk']
    simp [hk']
  simp_rw [heven]
  rw [ENNReal.tsum_comm, div_eq_mul_inv, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun k => ?_
  rw [← (ENNReal.summable).sum_add_tsum_nat_add' (k := k)]
  have h0 : ∑ i ∈ Finset.range k, (if k ≤ i then
      ENNReal.ofReal (((i - k + k).choose k : ℝ) * 4 ^ (i - k) * fWalks k 0 0 /
        4 ^ (2 * (i - k + k) + 1)) else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by simp [show ¬ k ≤ i by simpa using hi]
  rw [h0, zero_add]
  simp only [le_add_iff_nonneg_left, zero_le, ite_true, Nat.add_sub_cancel]
  rw [inner_sum, ← div_eq_mul_inv, div_twelve_pow,
    ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 3)]
  norm_num

end Entropic.DiamondGreen
