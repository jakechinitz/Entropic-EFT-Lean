import Mathlib

/-! Selected exchange extension of O.3, not a derivation of its constitutive
choice. Algebraic covariant decomposition is in 1+1 dimensions; the finite
budget result uses arbitrary finite collections of signed momenta. No full
Einstein--Vlasov existence theorem or galactic formation claim is made. -/
noncomputable section
open scoped BigOperators
namespace Entropic.FourItems.Streams

def forceTime (w Q gamma : ℝ) := w*Q*(gamma^2-1)
def forceSpace (w Q gamma k : ℝ) := w*Q*gamma*k

theorem force_orthogonal (w Q gamma k : ℝ) (hu : gamma^2-k^2=1) :
    -gamma*forceTime w Q gamma+k*forceSpace w Q gamma k=0 := by
  unfold forceTime forceSpace
  calc
    -gamma*(w*Q*(gamma^2-1))+k*(w*Q*gamma*k) =
        -w*Q*gamma*(gamma^2-k^2-1) := by ring
    _ = 0 := by rw [hu]; ring

theorem source_time (w Q gamma : ℝ) :
    -(w*Q*gamma)*gamma+forceTime w Q gamma = -w*Q := by
  unfold forceTime; ring

theorem source_space (w Q gamma k : ℝ) :
    -(w*Q*gamma)*k+forceSpace w Q gamma k = 0 := by
  unfold forceSpace; ring

theorem rest_loss_nonnegative (w Q gamma : ℝ)
    (hw : 0 ≤ w) (hQ : 0 ≤ Q) (hg : 0 ≤ gamma) : 0 ≤ w*Q*gamma := by positivity

theorem source_weights {ι : Type*} [Fintype ι] (w : ι → ℝ) (Q : ℝ)
    (hw : ∑ i, w i = 1) : (∑ i, -(w i*Q))+Q=0 := by
  rw [Finset.sum_neg_distrib, ← Finset.sum_mul, hw]; ring

theorem normalized_weights {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : (∑ i, a i) ≠ 0) : ∑ i, a i/(∑ j, a j) = 1 := by
  rw [← Finset.sum_div, div_self ha]

def updateEnergy (E p s : ℝ) := |p|+s*(E-|p|)

theorem reserve_positive (E p : ℝ) (h : |p|<E) : 0<E-|p| := sub_pos.mpr h

theorem timelike_preserved (E p s : ℝ) (h : |p|<E) (hs : 0<s) :
    |p| < updateEnergy E p s := by
  unfold updateEnergy
  have := mul_pos hs (sub_pos.mpr h)
  linarith

theorem causal_endpoint (E p s : ℝ) (h : |p| ≤ E) (hs : 0 ≤ s) :
    |p| ≤ updateEnergy E p s := by
  unfold updateEnergy
  exact le_add_of_nonneg_right (mul_nonneg hs (sub_nonneg.mpr h))

theorem removed_energy (E p s : ℝ) :
    E-updateEnergy E p s=(1-s)*(E-|p|) := by unfold updateEnergy; ring

theorem global_energy_ledger {ι : Type*} [Fintype ι]
    (E p : ι → ℝ) (s V : ℝ) :
    (∑ i, updateEnergy (E i) (p i) s)+(V+(1-s)*(∑ i, (E i-|p i|))) =
      (∑ i, E i)+V := by
  simp only [updateEnergy, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  ring

theorem exact_budget (A d : ℝ) (hA : A≠0) : (1-(1-d/A))*A=d := by field_simp; ring

theorem admissible_survival (A d : ℝ) (hA : 0<A) (hd : 0 ≤ d) (hbudget : d<A) :
    0<1-d/A ∧ 1-d/A ≤ 1 := by
  constructor
  · have := (div_lt_one hA).mpr hbudget; linarith
  · have := div_nonneg hd hA.le; linarith

theorem internal_positive (U R release survival : ℝ)
    (hU : 0 ≤ U) (hR : 0 ≤ R) (hp : 0 ≤ release) (hp1 : release ≤ 1) (hs : 0 ≤ survival) :
    0 ≤ survival*(1-release)*U ∧ 0 ≤ survival*(R+release*U) := by
  constructor
  · exact mul_nonneg (mul_nonneg hs (by linarith)) hU
  · positivity

theorem internal_sum (U R release survival : ℝ) :
    survival*(1-release)*U+survival*(R+release*U)=survival*(U+R) := by ring

-- Two distinct streams, with positive masses, exchange nonzero energy with
-- one clock and retain zero total spatial momentum in that clock frame.
theorem two_stream_witness :
    let E : ℝ := 2
    let p : ℝ := 1
    let s : ℝ := 1/2
    |p| < updateEnergy E p s ∧ |-p| < updateEnergy E (-p) s ∧
    updateEnergy E p s+updateEnergy E (-p) s+1=2*E ∧ p+(-p)=0 := by
  norm_num [updateEnergy]

-- If all momentum is zero this is exactly O.3's common-flow finite drain.
theorem cold_reduction (E s : ℝ) : updateEnergy E 0 s=s*E := by
  simp [updateEnergy]

-- Einstein Bianchi-I constraint propagation. C is the combined beam energy
-- density; P is its longitudinal pressure. Q is prescribed independently.
def theta (x y : ℝ) := x+2*y
def dx (x y b C V P : ℝ) := (b+C+2*V+P)/2-theta x y*x
def dy (x y b C V P : ℝ) := (b+C+2*V-P)/2-theta x y*y
def constraint (x y b C V : ℝ) := 2*x*y+y^2-b-C-V

theorem bianchi_constraint_propagation (x y b C V P Q : ℝ) :
    2*dx x y b C V P*y+2*x*dy x y b C V P+2*y*dy x y b C V P
      -(-theta x y*b)-(-theta x y*C-x*P-Q)-Q =
    -2*theta x y*constraint x y b C V := by
  unfold dx dy theta constraint; ring

theorem bianchi_total_balance (x y b C V P Q : ℝ) :
    (-theta x y*b)+(-theta x y*C-x*P-Q)+Q
      +theta x y*(b+C+V)+x*(P-V)+2*y*(-V)=0 := by
  unfold theta; ring

end Entropic.FourItems.Streams
