import Mathlib

noncomputable section
open scoped BigOperators
namespace ClusterOutliers

-- Accelerations: outward gas acceleration, inward gravity, outward support.
theorem gas_momentum_accounting (a g thermal nonthermal contact : ℝ)
    (h : a = -g + thermal + nonthermal + contact) :
    g = thermal + nonthermal + contact - a := by linarith

theorem quiet_static_contact_requirement (g thermal contact : ℝ)
    (h : 0 = -g + thermal + contact) : contact = g - thermal := by linarith

theorem redistribution_does_not_change_mass_estimator_identity
    (b c thermal other : ℝ) (h : b + c = thermal + other) :
    (b + c) - thermal = other := by linarith

theorem reciprocal_static_pressure (pb pc rb rc g f : ℝ)
    (hb : pb = -rb * g + f) (hc : pc = -rc * g - f) :
    pb + pc = -(rb + rc) * g := by rw [hb, hc]; ring

theorem reciprocal_exchange_power (f vb vc : ℝ) :
    f * vb + (-f) * vc = f * (vb - vc) := by ring

theorem passive_drag_heats (gamma vb vc : ℝ) (hg : 0 ≤ gamma) :
    0 ≤ -(gamma * (vc - vb) * (vb - vc)) := by
  have hsq : 0 ≤ gamma * (vb - vc)^2 := mul_nonneg hg (sq_nonneg _)
  nlinarith

theorem passive_drag_zero_at_equal_velocity (gamma vb vc : ℝ)
    (h : vc = vb) : gamma * (vc - vb) = 0 := by simp [h]

theorem symmetric_pair_has_no_mean_impulse (rate impulse : ℝ) :
    rate * impulse + rate * (-impulse) = 0 := by ring

theorem constant_fraction_pressure_mass (thermal q : ℝ) :
    thermal + q * thermal = (1 + q) * thermal := by ring

-- The integral or quadrature I is an explicit input, not proved from data.
theorem integrated_support_lower_bound (pInner pOuter I : ℝ)
    (balance : pInner - pOuter = I) (positive : 0 ≤ pOuter) :
    I ≤ pInner := by linarith

theorem pressure_cap_obstruction (pInner pOuter I cap : ℝ)
    (balance : pInner - pOuter = I) (positive : 0 ≤ pOuter)
    (bounded : pInner ≤ cap) : I ≤ cap := by linarith

theorem shell_positive_iff_cumulative_order (inner outer : ℝ) :
    0 ≤ outer - inner ↔ inner ≤ outer := sub_nonneg

theorem forward_drop_impossible (inner outer : ℝ)
    (drop : outer < inner) : ¬ 0 ≤ outer - inner := by linarith

-- A necessary lower bound on the maximum marginal-error displacement.
theorem interval_monotonicity_obstruction (yi yj ei ej t xi xj : ℝ)
    (lo : yi - t * ei ≤ xi) (hi : xj ≤ yj + t * ej)
    (mono : xi ≤ xj) : yi - yj ≤ t * (ei + ej) := by nlinarith

-- One conserved source cohort and a nonnegative outside-aperture ledger.
def cohort (k b c : ℝ) : ℝ := max b (c / k)

theorem minimum_cohort_suffices (k b c : ℝ) (hk : 0 < k) :
    b ≤ cohort k b c ∧ c ≤ k * cohort k b c := by
  constructor
  · exact le_max_left _ _
  · have h : c / k ≤ cohort k b c := le_max_right _ _
    have h' := (div_le_iff₀ hk).mp h
    nlinarith

theorem cohort_is_minimal (k b c b0 : ℝ) (hk : 0 < k)
    (hb : b ≤ b0) (hc : c ≤ k * b0) : cohort k b c ≤ b0 := by
  apply max_le hb
  apply (div_le_iff₀ hk).mpr
  nlinarith

theorem outside_stocks_nonnegative (k b c : ℝ) (hk : 0 < k) :
    0 ≤ cohort k b c - b ∧ 0 ≤ k * cohort k b c - c := by
  obtain ⟨hb, hc⟩ := minimum_cohort_suffices k b c hk
  constructor <;> linarith

theorem global_inventory_unchanged (k b c b0 : ℝ) :
    c + (k * b0 - c) = k * (b + (b0 - b)) := by ring

theorem retention_cross_identity (k b0 rb rc : ℝ) :
    k * (rb * b0) * rc = (rc * k * b0) * rb := by ring

theorem transport_nonnegative {n m : ℕ} (T : Fin n → Fin m → ℝ)
    (h : ∀ i j, 0 ≤ T i j) (j : Fin m) : 0 ≤ ∑ i, T i j := by
  exact Finset.sum_nonneg (fun i _ => h i j)

theorem transport_preserves_total {n m : ℕ} (T : Fin n → Fin m → ℝ) :
    (∑ j, ∑ i, T i j) = ∑ i, ∑ j, T i j := by
  exact Finset.sum_comm

theorem prescribed_marginals_preserve_mass {n m : ℕ}
    (T : Fin n → Fin m → ℝ) (source : Fin n → ℝ) (dest : Fin m → ℝ)
    (rows : ∀ i, ∑ j, T i j = source i)
    (cols : ∀ j, ∑ i, T i j = dest j) :
    ∑ i, source i = ∑ j, dest j := by
  simp_rw [← rows, ← cols]
  exact Finset.sum_comm

end ClusterOutliers
