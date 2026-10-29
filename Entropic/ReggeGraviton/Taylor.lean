import Mathlib

/-!
# Small-momentum limits of trigonometric sums

For a finite family of integer coefficients `a_x` and real phases `θ_x`:

* if `∑ a = 0`, then `ε⁻¹ ∑ a e^{iεθ} → i ∑ a θ`;
* if `∑ a = 0` and `∑ a θ = 0`, then `ε⁻² ∑ a e^{iεθ} → −½ ∑ a θ²`,

as `ε → 0`, `ε ≠ 0`. These turn moment identities of a lattice symbol into its continuum limit.
-/

open Complex Filter Topology

namespace Entropic.ReggeGraviton

/-- Third-order Taylor bound for `e^{ix}`, `|x| ≤ 1`. -/
theorem exp_I_taylor (x : ℝ) (hx : |x| ≤ 1) :
    ‖cexp (x * I) - (1 + x * I - x ^ 2 / 2)‖ ≤ |x| ^ 3 := by
  have hn : ‖(x : ℂ) * I‖ = |x| := by simp
  have h := Complex.exp_bound (x := (x : ℂ) * I) (by rw [hn]; exact hx) (n := 3) (by norm_num)
  have hs : ∑ m ∈ Finset.range 3, ((x : ℂ) * I) ^ m / (m.factorial : ℂ) = 1 + x * I - x ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring_nf
    simp [I_sq]
    ring
  rw [hs, hn] at h
  calc _ ≤ |x| ^ 3 * (((Nat.succ 3 : ℕ) : ℝ) * ((Nat.factorial 3 : ℝ) * (3 : ℕ))⁻¹) := h
    _ ≤ |x| ^ 3 := by
        have : (((Nat.succ 3 : ℕ) : ℝ) * ((Nat.factorial 3 : ℝ) * (3 : ℕ))⁻¹) ≤ 1 := by
          norm_num [Nat.factorial]
        exact mul_le_of_le_one_right (by positivity) this

/-- `(e^{iεθ} − 1)/ε → iθ`. -/
theorem tendsto_exp_first (θ : ℝ) :
    Tendsto (fun ε : ℝ => (cexp ((ε * θ : ℝ) * I) - 1) / ε) (𝓝[≠] 0) (𝓝 (θ * I)) := by
  have hd : HasDerivAt (fun t : ℝ => cexp ((t * θ : ℝ) * I)) (θ * I) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => ((t * θ : ℝ) : ℂ) * I) (θ * I) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).mul_const θ).ofReal_comp.mul_const I
      simpa using this
    have := h1.cexp
    simpa using this
  have := hd.tendsto_slope_zero
  refine this.congr' (Eventually.of_forall fun ε => ?_)
  simp [div_eq_inv_mul]

/-- `(e^{iεθ} − 1 − iεθ)/ε² → −θ²/2`. -/
theorem tendsto_exp_second (θ : ℝ) :
    Tendsto (fun ε : ℝ => (cexp ((ε * θ : ℝ) * I) - 1 - (ε * θ : ℝ) * I) / (ε : ℂ) ^ 2)
      (𝓝[≠] 0) (𝓝 (-(θ : ℂ) ^ 2 / 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ᶠ ε : ℝ in 𝓝[≠] 0, ‖(cexp ((ε * θ : ℝ) * I) - 1 - (ε * θ : ℝ) * I) / (ε : ℂ) ^ 2 -
      -(θ : ℂ) ^ 2 / 2‖ ≤ |ε| * |θ| ^ 3 := by
    have hsmall : ∀ᶠ ε : ℝ in 𝓝[≠] 0, |ε * θ| ≤ 1 := by
      have : Tendsto (fun ε : ℝ => ε * θ) (𝓝[≠] 0) (𝓝 0) := by
        have hc : Continuous fun ε : ℝ => ε * θ := by fun_prop
        have := hc.tendsto (0 : ℝ)
        simpa using this.mono_left nhdsWithin_le_nhds
      exact (this.abs).eventually (ge_mem_nhds (by simp))
    filter_upwards [hsmall, self_mem_nhdsWithin] with ε hε hne
    have hne' : (ε : ℂ) ≠ 0 := by exact_mod_cast hne
    have key : (cexp ((ε * θ : ℝ) * I) - 1 - (ε * θ : ℝ) * I) / (ε : ℂ) ^ 2 - -(θ : ℂ) ^ 2 / 2 =
        (cexp ((ε * θ : ℝ) * I) - (1 + (ε * θ : ℝ) * I - (ε * θ : ℝ) ^ 2 / 2)) / (ε : ℂ) ^ 2 := by
      field_simp; push_cast; ring
    rw [key, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have hpos : 0 < |ε| ^ 2 := by have := abs_pos.mpr hne; positivity
    rw [div_le_iff₀ hpos]
    calc _ ≤ |ε * θ| ^ 3 := by
          have := exp_I_taylor (ε * θ) hε
          push_cast at this ⊢
          exact this
      _ = |ε| * |θ| ^ 3 * |ε| ^ 2 := by rw [abs_mul]; ring
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hb ?_
  have : Tendsto (fun ε : ℝ => |ε| * |θ| ^ 3) (𝓝 0) (𝓝 (|0| * |θ| ^ 3)) :=
    (continuous_abs.mul continuous_const).tendsto 0
  simpa using this.mono_left nhdsWithin_le_nhds

variable {ι : Type*} [Fintype ι]

/-- First-order limit of a trigonometric sum with vanishing zeroth moment. -/
theorem tendsto_trig_first (a : ι → ℤ) (θ : ι → ℝ) (h0 : ∑ x, a x = 0) :
    Tendsto (fun ε : ℝ => (∑ x, (a x : ℂ) * cexp ((ε * θ x : ℝ) * I)) / ε) (𝓝[≠] 0)
      (𝓝 (∑ x, (a x : ℂ) * (θ x * I))) := by
  have e : ∀ ε : ℝ, (∑ x, (a x : ℂ) * cexp ((ε * θ x : ℝ) * I)) / ε =
      ∑ x, (a x : ℂ) * ((cexp ((ε * θ x : ℝ) * I) - 1) / ε) := by
    intro ε
    have h0' : ∑ x, (a x : ℂ) = 0 := by exact_mod_cast h0
    rw [Finset.sum_div]
    have : ∑ x, (a x : ℂ) * ((cexp ((ε * θ x : ℝ) * I) - 1) / ε) =
        ∑ x, (a x : ℂ) * cexp ((ε * θ x : ℝ) * I) / ε - (∑ x, (a x : ℂ)) / ε := by
      rw [Finset.sum_div, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [this, h0', zero_div, sub_zero]
  simp_rw [e]
  exact tendsto_finsetSum _ fun x _ => (tendsto_exp_first (θ x)).const_mul _

/-- Second-order limit of a trigonometric sum with vanishing zeroth and first moments. -/
theorem tendsto_trig_second (a : ι → ℤ) (θ : ι → ℝ) (h0 : ∑ x, a x = 0)
    (h1 : ∑ x, (a x : ℝ) * θ x = 0) :
    Tendsto (fun ε : ℝ => (∑ x, (a x : ℂ) * cexp ((ε * θ x : ℝ) * I)) / (ε : ℂ) ^ 2) (𝓝[≠] 0)
      (𝓝 (∑ x, (a x : ℂ) * (-(θ x : ℂ) ^ 2 / 2))) := by
  have h0' : ∑ x, (a x : ℂ) = 0 := by exact_mod_cast h0
  have h1' : ∑ x, (a x : ℂ) * (θ x : ℂ) = 0 := by exact_mod_cast h1
  have e : ∀ ε : ℝ, (∑ x, (a x : ℂ) * cexp ((ε * θ x : ℝ) * I)) / (ε : ℂ) ^ 2 =
      ∑ x, (a x : ℂ) * ((cexp ((ε * θ x : ℝ) * I) - 1 - (ε * θ x : ℝ) * I) / (ε : ℂ) ^ 2) := by
    intro ε
    have : ∑ x, (a x : ℂ) * ((cexp ((ε * θ x : ℝ) * I) - 1 - (ε * θ x : ℝ) * I) / (ε : ℂ) ^ 2) =
        (∑ x, (a x : ℂ) * cexp ((ε * θ x : ℝ) * I)) / (ε : ℂ) ^ 2 -
          (∑ x, (a x : ℂ)) / (ε : ℂ) ^ 2 - (ε * I) * (∑ x, (a x : ℂ) * (θ x : ℂ)) / (ε : ℂ) ^ 2 := by
      rw [Finset.mul_sum, Finset.sum_div, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      push_cast; ring
    rw [this, h0', h1']; simp
  simp_rw [e]
  exact tendsto_finsetSum _ fun x _ => (tendsto_exp_second (θ x)).const_mul _

end Entropic.ReggeGraviton
