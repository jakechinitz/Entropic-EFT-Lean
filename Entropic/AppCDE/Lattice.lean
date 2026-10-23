import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-! Discrete variation on a finite graph (ledger C05-10). With each undirected edge counted
once, F(Q) = (J/2)Σ_{edges}(Q_a − Q_b)² − Σ s_a Q_a = (J/4)Σ_{a}Σ_{b∼a}(Q_a − Q_b)² − Σ s_aQ_a
has ∂F/∂Q_a = J(LQ)_a − s_a with L the graph Laplacian; on a 4-regular graph L = 4I − A. -/

noncomputable section
namespace Entropic.AppCDE.Lattice
open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def F (J : ℝ) (s Q : V → ℝ) : ℝ :=
  J / 4 * ∑ i, ∑ j, (if G.Adj i j then (Q i - Q j) ^ 2 else 0) - ∑ i, s i * Q i

/-- The same functional as a quadratic form: (J/4)ΣΣ = (J/2)·Qᵀ L Q. -/
theorem F_quadratic (J : ℝ) (s Q : V → ℝ) :
    F G J s Q = J / 2 * Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) Q Q - ∑ i, s i * Q i := by
  rw [F, SimpleGraph.lapMatrix_toLinearMap₂']; ring

theorem gradient (J : ℝ) (s Q : V → ℝ) (a : V) :
    HasDerivAt (fun t : ℝ => F G J s (Q + t • Pi.single a 1))
      (J * (G.lapMatrix ℝ *ᵥ Q) a - s a) 0 := by
  set e : V → ℝ := Pi.single a 1
  -- termwise derivatives
  have hterm : ∀ i j, HasDerivAt
      (fun t : ℝ => if G.Adj i j then ((Q + t • e) i - (Q + t • e) j) ^ 2 else 0)
      (if G.Adj i j then 2 * (Q i - Q j) * (e i - e j) else 0) 0 := by
    intro i j
    by_cases hij : G.Adj i j
    · simp only [hij, if_true]
      have h1 : HasDerivAt (fun t : ℝ => Q i + t * e i - (Q j + t * e j)) (e i - e j) 0 := by
        have := (((hasDerivAt_id (0:ℝ)).mul_const (e i)).const_add (Q i)).fun_sub
          (((hasDerivAt_id (0:ℝ)).mul_const (e j)).const_add (Q j))
        simpa using this
      have h2 := h1.fun_pow 2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      convert h2 using 1
      simp
    · simp only [hij, if_false]; exact hasDerivAt_const _ _
  have hlin : HasDerivAt (fun t : ℝ => ∑ i, s i * (Q + t • e) i) (s a) 0 := by
    have : (fun t : ℝ => ∑ i, s i * (Q + t • e) i) = fun t => (∑ i, s i * Q i) + t * s a := by
      funext t
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
      congr 1
      simp [e, Pi.single_apply, mul_comm]
    rw [this]
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (s a)).const_add (∑ i, s i * Q i)
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.sum (u := Finset.univ) (fun j _ => hterm i j))
  have hF := (hsum.const_mul (J / 4)).sub hlin
  convert hF using 1
  · funext t; simp only [F]; congr 1; congr 1
    funext; simp only [Finset.sum_apply]
  · -- evaluate the derivative
    rw [SimpleGraph.lapMatrix_mulVec_apply']
    have key : ∑ i, ∑ j, (if G.Adj i j then 2 * (Q i - Q j) * (e i - e j) else 0) =
        4 * ∑ u ∈ G.neighborFinset a, (Q a - Q u) := by
      have split : ∀ i j, (if G.Adj i j then 2 * (Q i - Q j) * (e i - e j) else 0) =
          (if G.Adj i j then 2 * (Q i - Q j) * e i else 0) -
            (if G.Adj i j then 2 * (Q i - Q j) * e j else 0) := by
        intro i j; by_cases h : G.Adj i j <;> simp [h]; ring
      simp_rw [split, Finset.sum_sub_distrib]
      have A : ∑ i, ∑ j, (if G.Adj i j then 2 * (Q i - Q j) * e i else 0) =
          2 * ∑ u ∈ G.neighborFinset a, (Q a - Q u) := by
        rw [Finset.sum_eq_single a]
        · simp only [e, Pi.single_eq_same, mul_one]
          rw [Finset.mul_sum, ← Finset.sum_filter]
          congr 1; ext u; simp [SimpleGraph.mem_neighborFinset]
        · intro i _ hi; apply Finset.sum_eq_zero; intro j _
          simp [e, Pi.single_apply, hi]
        · simp
      have B : ∑ i, ∑ j, (if G.Adj i j then 2 * (Q i - Q j) * e j else 0) =
          -(2 * ∑ u ∈ G.neighborFinset a, (Q a - Q u)) := by
        rw [Finset.sum_comm, Finset.sum_eq_single a]
        · simp only [e, Pi.single_eq_same, mul_one]
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_filter]
          refine Finset.sum_congr (by ext u; simp [SimpleGraph.mem_neighborFinset, G.adj_comm]) ?_
          intro u _; ring
        · intro j _ hj; apply Finset.sum_eq_zero; intro i _
          simp [e, Pi.single_apply, hj]
        · simp
      rw [A, B, Finset.sum_sub_distrib]; ring
    rw [key]; simp only [Finset.sum_sub_distrib]; ring

/-- Stationarity in every direction is J L Q = s. -/
theorem stationary_iff (J : ℝ) (s Q : V → ℝ) :
    (∀ a, J * (G.lapMatrix ℝ *ᵥ Q) a - s a = 0) ↔ J • (G.lapMatrix ℝ *ᵥ Q) = s := by
  constructor
  · intro h; funext a; simpa [sub_eq_zero] using h a
  · intro h a; rw [← h]; simp

/-- On a 4-regular graph the Laplacian is 4I − A. -/
theorem lap_regular {d : ℕ} (hd : G.IsRegularOfDegree d) :
    G.lapMatrix ℝ = (d : Matrix V V ℝ) - G.adjMatrix ℝ := by
  rw [SimpleGraph.lapMatrix, SimpleGraph.IsRegularOfDegree.degMatrix_eq ℝ G hd]

end Entropic.AppCDE.Lattice
