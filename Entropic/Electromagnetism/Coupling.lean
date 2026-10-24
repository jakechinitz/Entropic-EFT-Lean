import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Coupling-identification audit for Appendix S.
These are exact finite algebra/calculus statements, not a construction of a
native gauge measure, a continuum phase, a fermion determinant, or RG dynamics.
The transfer multipliers are the stated product-heat ansatz. The current-response
identity is conditional on the displayed partition derivatives. -/
noncomputable section
open scoped BigOperators
namespace Entropic.Electromagnetism.Coupling

def hypercharge : Fin 5 → ℚ := ![-1/3,-1/3,-1/3,1/2,1/2]

theorem hypercharge_trace : ∑ i, hypercharge i = 0 := by
  norm_num [hypercharge, Fin.sum_univ_succ]

theorem hypercharge_squared_trace : ∑ i, (hypercharge i)^2 = 5/6 := by
  norm_num [hypercharge, Fin.sum_univ_succ]

theorem canonical_hypercharge_normalization : (3:ℚ)/5*(5/6)=1/2 := by norm_num

theorem unified_inverse_coupling (gSquared : ℝ) (hg : gSquared ≠ 0) :
    1/gSquared + 1/((3/5)*gSquared) = 1/((3/8)*gSquared) := by
  field_simp
  ring

theorem sm_electromagnetic_beta_combination :
    (5:ℚ)/3*(41/10) - 19/6 = 11/3 := by norm_num

theorem sm_one_loop_combination (u ell : ℝ) :
    (5/3)*(u+(41/10)*ell/(2*Real.pi)) +
      (u-(19/6)*ell/(2*Real.pi)) = (8/3)*u+11*ell/(6*Real.pi) := by ring

theorem running_cannot_lower_trial (u ell : ℝ) (hell : 0 ≤ ell) :
    (8/3)*u ≤ (8/3)*u+11*ell/(6*Real.pi) := by
  have : 0 ≤ 11*ell/(6*Real.pi) := by positivity
  linarith

theorem lower_target_excluded (u ell target : ℝ)
    (hell : 0 ≤ ell) (ht : target < (8/3)*u) :
    target < (8/3)*u+11*ell/(6*Real.pi) :=
  lt_of_lt_of_le ht (running_cannot_lower_trial u ell hell)

/-- Off-diagonal matrix units are in the complex span of the full color
generators. A commuting independent weak action on this same irreducible
qutrit therefore has only scalar generators. This does not restrict extra
tensor factors or a separately supplied unified representation. -/
theorem full_color_commutant_scalar (Q : Matrix (Fin 3) (Fin 3) ℂ)
    (h : ∀ i j, i ≠ j → Commute (Matrix.single i j 1) Q) :
    ∃ c : ℂ, Matrix.scalar (Fin 3) c = Q :=
  Matrix.mem_range_scalar_of_commute_single h

/-- The same algebraic restriction applies to any charge required to commute
with the entire retained matrix control algebra. It does not assert that every
available control is a term in the physical Hamiltonian. -/
theorem full_retained_commutant_scalar (Q : Matrix (Fin 9) (Fin 9) ℂ)
    (h : ∀ i j, i ≠ j → Commute (Matrix.single i j 1) Q) :
    ∃ c : ℂ, Matrix.scalar (Fin 9) c = Q :=
  Matrix.mem_range_scalar_of_commute_single h

/-- Neutral transfer data cannot see the independent central heat time. -/
def liftedMultiplier (colorHeat centralHeat casimir charge : ℝ) : ℝ :=
  Real.exp (-(colorHeat*casimir+centralHeat*charge^2))

theorem neutral_multiplier_independent (s u v C : ℝ) :
    liftedMultiplier s u C 0 = liftedMultiplier s v C 0 := by
  simp [liftedMultiplier]

theorem charged_multiplier_injective (s C u v : ℝ)
    (h : liftedMultiplier s u C 1 = liftedMultiplier s v C 1) : u=v := by
  simp only [liftedMultiplier, one_pow, mul_one] at h
  have he := Real.exp_injective h
  linarith

theorem no_central_heat_inference_from_neutral_data (s : ℝ) :
    ¬ ∃ f : (ℝ → ℝ) → ℝ, ∀ u : ℝ, 0<u →
      f (fun C => liftedMultiplier s u C 0)=u := by
  rintro ⟨f,h⟩
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  have he : (fun C => liftedMultiplier s 1 C 0) =
      (fun C => liftedMultiplier s 2 C 0) := by
    funext C
    exact neutral_multiplier_independent s 1 2 C
  rw [he] at h1
  linarith

theorem finite_partition_phase_blind {ι : Type*} [Fintype ι]
    (weight : ι → ℝ) (action : ℝ → ι → ℝ)
    (h : ∀ phi i, action phi i = action 0 i) (phi : ℝ) :
    (∑ i, weight i*Real.exp (-action phi i)) =
      ∑ i, weight i*Real.exp (-action 0 i) := by simp_rw [h phi]

theorem constant_effective_action_zero_curvature (Z : ℝ) :
    deriv (fun phi : ℝ => deriv (fun _ : ℝ => -Real.log Z) phi) 0=0 := by simp

/-- Scalar derivative of -log Z, with a nonzero partition function. -/
theorem effective_action_first_derivative (Z : ℝ → ℝ) (z1 x : ℝ)
    (h : HasDerivAt Z z1 x) (hz : Z x ≠ 0) :
    HasDerivAt (fun phi => -Real.log (Z phi)) (-z1/Z x) x := by
  have hf : (fun phi => -Real.log (Z phi)) = -(fun phi => Real.log (Z phi)) := by
    ext phi
    rfl
  rw [hf, neg_div]
  exact (h.log hz).neg

/-- With Z'=-Z<J> and Z''=Z<J^2-K>, -log Z has curvature
<K>-<J^2>+<J>^2. This theorem verifies the substitution; differentiation
under an interacting path integral is a separate analytic obligation. -/
theorem partition_curvature_identity (Z z1 z2 J J2 K : ℝ)
    (hz : Z ≠ 0) (h1 : z1 = -Z*J) (h2 : z2=Z*(J2-K)) :
    (z1/Z)^2-z2/Z = K-(J2-J^2) := by
  rw [h1,h2]
  field_simp
  ring

theorem response_with_counterterm (K Zlocal : ℝ) :
    (K+Zlocal)-K=Zlocal := by ring

/-- Product diamond area tensors, with positive geometrical quantities.
Here r is temporal spacing / spatial bond length, not a hopping ratio. -/
def electricCoefficient (kE r : ℝ) := Real.sqrt 3*kE*r/4
def magneticCoefficient (kM r : ℝ) := 4*Real.sqrt 3*kM/(3*r)

theorem diamond_equal_speed_condition (kE kM r : ℝ) (hr : r ≠ 0) :
    electricCoefficient kE r = magneticCoefficient kM r ↔
      3*kE*r^2=16*kM := by
  unfold electricCoefficient magneticCoefficient
  constructor
  · intro h
    field_simp at h
    nlinarith [h]
  · intro h
    field_simp
    nlinarith [h]

theorem equal_transfer_ratio (kE kM r : ℝ) (hr2 : r^2=32/9)
    (h : 3*kE*r^2=16*kM) : 2*kE=3*kM := by
  rw [hr2] at h
  linarith

/-- Exact isolated-cycle bosonic curvatures, parameterized by x=(t/m)^2.
The determinant-to-rational-form derivation is supplied analytically and
checked numerically; these definitions do not claim a full graph determinant. -/
def cycle4 (x : ℝ) := 2*x^2/(1-4*x)
def cycle6 (x : ℝ) := 2*x^3/((1-x)^2*(1-4*x))

theorem cycle_ratio_identity (x : ℝ) (hx : x ≠ 0)
    (h1 : 1-x ≠ 0) (h4 : 1-4*x ≠ 0) :
    cycle4 x / cycle6 x = (1-x)^2/x := by
  unfold cycle4 cycle6
  have h4' : 1-x*4 ≠ 0 := by simpa [mul_comm] using h4
  field_simp [hx,h1,h4,h4']

theorem cycle_ratio_bound (x : ℝ) (hx : 0<x) (hx4 : x<1/4) :
    9/4 < (1-x)^2/x := by
  apply (lt_div_iff₀ hx).2
  have hp : 0 < (4-x)*(1-4*x) := mul_pos (by linarith) (by linarith)
  nlinarith

theorem cycle_ratio_incompatible_with_equal_transfer (x : ℝ)
    (hx : 0<x) (hx4 : x<1/4) : (1-x)^2/x ≠ 3/2 := by
  have h := cycle_ratio_bound x hx hx4
  intro he
  rw [he] at h
  norm_num at h

end Entropic.Electromagnetism.Coupling
