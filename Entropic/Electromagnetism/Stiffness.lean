import Mathlib

/-! Electromagnetic stiffness: algebra behind Appendix S.9 and S.10.

The native fidelity gluing has a cubic order-parameter invariant, so its ordering
transition is first order in mean field; the induced stiffness of the nine fiber
components stays below the compact U(1) deconfinement value unless the fiber mass is
exponentially small; the native charged leptons cannot induce the observed coupling;
an asymptotically free factor cannot be induced at the cutoff; and the reversible
diamond transfer has adjoint eigenvalue 1 - 2(1-k)/(d+1), which gives t_8 = 13/14.
Physical identifications (records, charges, the Coulomb phase) are not formalized. -/

namespace Entropic.Electromagnetism.Stiffness

/-- Haar-averaged adjoint eigenvalue of the reversible transfer `K_P = I - (1-k)P`,
`L_P = l P` with `l^2 = 1 - k^2`, using `∫P = I/d` and the traceless part of
`∫PXP = (X + Tr X I)/(d(d+1))`. -/
theorem adjoint_transfer_eigenvalue (d k : ℝ) (hd : 0 < d) :
    1 - 2*(1-k)/d + ((1-k)^2 + (1-k^2))/(d*(d+1)) = 1 - 2*(1-k)/(d+1) := by
  have hd1 : d + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- The color case: a qutrit (`d = 3`) with direct amplitude `k = 6/7` gives `13/14`. -/
theorem color_transfer : (1:ℝ) - 2*(1 - 6/7)/(3+1) = 13/14 := by norm_num

/-- A traceless order parameter with nonzero cubic invariant exists for `N = 3`
(`Q = diag(2,-1,-1)`), so the Landau expansion of the CP^{N-1} ordering has a cubic term. -/
theorem cubic_invariant_nonzero :
    (2:ℝ) + (-1) + (-1) = 0 ∧ (2:ℝ)^3 + (-1)^3 + (-1)^3 = 6 := by norm_num

/-- Mean-field ordering coupling `N(N+1)/(2z)` for `N = 9` on the 4D cubic lattice. -/
theorem mean_field_coupling : (9:ℝ)*(9+1)/(2*8) = 45/8 := by norm_num

/-- Induced stiffness of the nine fiber components, `9 ℓ/(24π^2)` with `ℓ = ln(Λ/m)`,
stays below the compact U(1) deconfinement value `1.0111331` whenever `ℓ ≤ 26`. -/
theorem fiber_stiffness_below_deconfinement (ℓ : ℝ) (h : ℓ ≤ 26) :
    9*ℓ/(24*Real.pi^2) < 1.0111331 := by
  have hpi : 3.14 < Real.pi := Real.pi_gt_d2
  have hp2 : (3.14:ℝ)^2 < Real.pi^2 := by nlinarith
  have hpos : 0 < 24*Real.pi^2 := by positivity
  rw [div_lt_iff₀ hpos]
  nlinarith

/-- Native charged leptons cannot induce the observed coupling: with each
`ln(m_P/m_ℓ) ≤ 51.6`, the one-loop induced `α^{-1} = (2/3π) Σ ln` stays below `33`,
far from `137`. -/
theorem leptons_cannot_induce_alpha (l1 l2 l3 : ℝ)
    (h1 : l1 ≤ 51.6) (h2 : l2 ≤ 51.6) (h3 : l3 ≤ 51.6) :
    2/(3*Real.pi)*(l1+l2+l3) < 33 := by
  have hpi : 3.14 < Real.pi := Real.pi_gt_d2
  have hpos : 0 < 3*Real.pi := by positivity
  have hsum : l1 + l2 + l3 ≤ 154.8 := by linarith
  rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
  nlinarith

/-- Standard Model `SU(2)_L` one-loop coefficient `b_2 = -22/3 + (4/3) n_g + (1/6) n_H`
with three generations and one doublet. -/
theorem su2_coefficient : -(22:ℝ)/3 + 4/3*3 + 1/6*1 = -19/6 := by norm_num

/-- An asymptotically free factor cannot be induced at the cutoff: if `b < 0` and the
inverse coupling is positive at a lower scale, it stays positive at every higher scale,
`α^{-1}(μ) = α^{-1}(M) - (b/2π) ln(μ/M)`. -/
theorem asymptotically_free_not_induced (a b L : ℝ) (ha : 0 < a) (hb : b < 0) (hL : 0 ≤ L) :
    0 < a - b/(2*Real.pi)*L := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have : b/(2*Real.pi)*L ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg _ hL
    exact div_nonpos_of_nonpos_of_nonneg hb.le (by positivity)
  linarith

/-- Heat-kernel coordinate: `t = e^{-s C}` per primitive step and `g^2 = 4 √6 s` on the
diamond regulator; for color `C_A = 3`, `s = ln(14/13)/3`, so `g^2 = (4√6/3) ln(14/13)`. -/
theorem color_heat_kernel_coordinate :
    4*Real.sqrt 6*(Real.log (14/13)/3) = 4*Real.sqrt 6/3*Real.log (14/13) := by ring

end Entropic.Electromagnetism.Stiffness
