import Mathlib

/-! Exact identities and obstructions for the proposed electromagnetic extension.
No determinant convergence, Gaussian measure construction, native charge selection,
unbounded-operator dynamics, or interacting continuum phase is asserted here. -/
noncomputable section
open scoped BigOperators
namespace Entropic.Electromagnetism

theorem projective_channel_phase {n : Type*} [Fintype n]
    (U X : Matrix n n ℂ) (z : ℂ) (hz : z*star z=1) :
    (z • U)*X*(z • U).conjTranspose=U*X*U.conjTranspose := by
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm (star z) z, hz, one_smul]

theorem scalar_channel_same_opposite_phase (x : ℂ) :
    (1:ℂ)*x*star (1:ℂ)=(-1:ℂ)*x*star (-1:ℂ) := by simp

theorem loop_phase_distinguishes_lifts : (1:ℂ) ≠ -1 := by norm_num

theorem no_phase_readout_from_scalar_channels :
    ¬ ∃ F : (ℂ → ℂ) → ℂ, ∀ u : ℂ, u*star u=1 →
      F (fun x => u*x*star u)=u := by
  rintro ⟨F,h⟩
  have hp := h 1 (by simp)
  have hm := h (-1) (by simp)
  have he : (fun x : ℂ => (1:ℂ)*x*star (1:ℂ)) =
      (fun x : ℂ => (-1:ℂ)*x*star (-1:ℂ)) := by
    funext x
    exact scalar_channel_same_opposite_phase x
  rw [he] at hp
  exact loop_phase_distinguishes_lifts (hp.symm.trans hm)

theorem finite_rotor_obstruction {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (E U V : Matrix n n ℂ) (hvu : V*U=1) (huv : U*V=1) :
    E*U-U*E ≠ U := by
  intro h
  have he : V*E*U-E=1 := by
    have hh := congrArg (fun A => V*A) h
    simpa only [mul_sub, ← mul_assoc, hvu, one_mul] using hh
  have ht := congrArg Matrix.trace he
  rw [Matrix.trace_sub, Matrix.trace_mul_cycle, huv, Matrix.one_mul,
    sub_self, Matrix.trace_one] at ht
  have hc : (Fintype.card n : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card n ≠ 0)
  exact hc ht.symm

theorem gaussian_link_square (x y ar ai kappa : ℝ) (hk : kappa ≠ 0) :
    -(x*x+y*y)/kappa+2*(x*ar-y*ai) =
      -((x-kappa*ar)^2+(y+kappa*ai)^2)/kappa+kappa*(ar^2+ai^2) := by
  field_simp
  ring

def berryAmplitude (A B t : ℝ) : ℝ := t^2*A/(1+t^2*B)

theorem composite_connection_zero_linearization (A B : ℝ) :
    HasDerivAt (berryAmplitude A B) 0 0 := by
  have hnum : HasDerivAt (fun t : ℝ => t^2*A) 0 0 := by
    convert ((hasDerivAt_id (0:ℝ)).pow 2).mul_const A using 1 <;> norm_num
  have hden : HasDerivAt (fun t : ℝ => 1+t^2*B) 0 0 := by
    convert (((hasDerivAt_id (0:ℝ)).pow 2).mul_const B).const_add 1 using 1 <;> norm_num
  convert hnum.div hden (by norm_num) using 1 <;> norm_num [berryAmplitude]
  ext t
  rfl

theorem first_loop_coefficient (L : ℕ) (hL : L ≠ 0) (r phi : ℝ) :
    -(r^L/(L:ℝ))*(2*(L:ℝ)*(Real.cos phi-1)) = 2*r^L*(1-Real.cos phi) := by
  have h : (L:ℝ) ≠ 0 := by exact_mod_cast hL
  field_simp
  ring

theorem loop_stiffness_positive (r : ℝ) (hr : 0 < r) (L : ℕ) :
    0 < 2*r^L := by positivity

theorem loop_action_nonnegative (r phi : ℝ) (hr : 0 ≤ r) (L : ℕ) :
    0 ≤ 2*r^L*(1-Real.cos phi) := by
  exact mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one phi))

theorem curvature_four_control : 2*((14:ℚ)/100)^4=76832/100000000 := by norm_num
theorem curvature_six_control : 2*((14:ℚ)/100)^6=15059072/1000000000000 := by norm_num

theorem positive_stiffness_not_unique :
    ∃ b c : ℝ, 0 < b ∧ 0 < c ∧ b ≠ c := by
  exact ⟨1,2,by norm_num,by norm_num,by norm_num⟩

theorem different_stiffness_different_action (b c fluxCost : ℝ)
    (hbc : b ≠ c) (hcost : fluxCost ≠ 0) : b*fluxCost ≠ c*fluxCost := by
  exact fun h => hbc (mul_right_cancel₀ hcost h)

end Entropic.Electromagnetism
