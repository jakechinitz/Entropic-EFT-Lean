import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! Maximum-entropy volume state (ledger C05-42). For a finite real spectrum v (eigenvalues of
a Hermitian V) that is not constant, the tilted mean ⟨V⟩_λ = Σv e^{λv}/Σe^{λv} has derivative
Var_λ(V) > 0, so it is strictly increasing and each attainable target fixes λ uniquely. -/

noncomputable section
namespace Entropic.AppCDE.Tilted
open Finset

variable {ι : Type*} [Fintype ι] (v : ι → ℝ)

def Z (l : ℝ) : ℝ := ∑ i, Real.exp (l * v i)
def S1 (l : ℝ) : ℝ := ∑ i, v i * Real.exp (l * v i)
def S2 (l : ℝ) : ℝ := ∑ i, v i ^ 2 * Real.exp (l * v i)
def M (l : ℝ) : ℝ := S1 v l / Z v l

theorem Z_pos [Nonempty ι] (l : ℝ) : 0 < Z v l :=
  Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

theorem Z_deriv (l : ℝ) : HasDerivAt (Z v) (S1 v l) l := by
  unfold Z S1
  have := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    ((hasDerivAt_id l).mul_const (v i)).exp)
  convert this using 1
  · funext x; simp [Finset.sum_apply]
  · congr 1; funext i; simp; ring

theorem S1_deriv (l : ℝ) : HasDerivAt (S1 v) (S2 v l) l := by
  unfold S1 S2
  have := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (((hasDerivAt_id l).mul_const (v i)).exp).const_mul (v i))
  convert this using 1
  · funext x; simp [Finset.sum_apply]
  · congr 1; funext i; simp; ring

/-- Z·S₂ − S₁² = ½ΣΣ wᵢwⱼ(vᵢ − vⱼ)². -/
theorem lagrange (l : ℝ) :
    Z v l * S2 v l - S1 v l ^ 2 =
      (1/2) * ∑ i, ∑ j, Real.exp (l * v i) * Real.exp (l * v j) * (v i - v j) ^ 2 := by
  unfold Z S1 S2
  have hg : ∀ i j, Real.exp (l * v i) * Real.exp (l * v j) * (v i - v j) ^ 2 =
      (Real.exp (l * v i) * (v j ^ 2 * Real.exp (l * v j)) -
          v i * Real.exp (l * v i) * (v j * Real.exp (l * v j))) +
        (Real.exp (l * v j) * (v i ^ 2 * Real.exp (l * v i)) -
          v j * Real.exp (l * v j) * (v i * Real.exp (l * v i))) := by intro i j; ring
  simp_rw [hg, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => Real.exp (l * v j) * (v i ^ 2 * Real.exp (l * v i)) -
    v j * Real.exp (l * v j) * (v i * Real.exp (l * v i)))]
  rw [sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [Finset.sum_sub_distrib]
  ring

theorem M_deriv [Nonempty ι] (l : ℝ) :
    HasDerivAt (M v) ((Z v l * S2 v l - S1 v l ^ 2) / Z v l ^ 2) l := by
  have h := (S1_deriv v l).div (Z_deriv v l) (Z_pos v l).ne'
  unfold M
  convert h using 1
  field_simp

/-- Strict monotonicity when the spectrum is not constant. -/
theorem M_strictMono [Nonempty ι] (hv : ∃ i j, v i ≠ v j) : StrictMono (M v) := by
  apply strictMono_of_deriv_pos
  intro l
  rw [(M_deriv v l).deriv]
  apply div_pos _ (pow_pos (Z_pos v l) 2)
  rw [lagrange]
  obtain ⟨i, j, hij⟩ := hv
  apply mul_pos (by norm_num)
  apply lt_of_lt_of_le _ (Finset.single_le_sum (f := fun i => ∑ j, Real.exp (l * v i) *
    Real.exp (l * v j) * (v i - v j) ^ 2) (fun i _ => Finset.sum_nonneg (fun j _ => by positivity))
    (Finset.mem_univ i))
  apply lt_of_lt_of_le _ (Finset.single_le_sum (f := fun j => Real.exp (l * v i) *
    Real.exp (l * v j) * (v i - v j) ^ 2) (fun j _ => by positivity) (Finset.mem_univ j))
  have : 0 < (v i - v j) ^ 2 := by positivity
  positivity

theorem M_continuous [Nonempty ι] : Continuous (M v) :=
  continuous_iff_continuousAt.mpr fun l => (M_deriv v l).continuousAt

/-- Any target between two attained values is attained at exactly one λ. -/
theorem unique_tilt [Nonempty ι] (hv : ∃ i j, v i ≠ v j) {a b t : ℝ} (hab : a ≤ b)
    (ha : M v a ≤ t) (hb : t ≤ M v b) : ∃! l, M v l = t := by
  obtain ⟨l, _, hl⟩ := intermediate_value_Icc hab (M_continuous v).continuousOn ⟨ha, hb⟩
  exact ⟨l, hl, fun y hy => (M_strictMono v hv).injective (hy.trans hl.symm)⟩

end Entropic.AppCDE.Tilted
