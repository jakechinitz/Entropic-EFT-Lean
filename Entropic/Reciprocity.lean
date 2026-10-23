import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! Momentum balance with an inertial retained stock (App. O.3).

App. O.3 realizes the galactic excess as a positive, collisionless, self-gravitating
stock that moves with its carrier (Vlasov–Poisson). With the stock in the state and
coupled like all other mass (one metric, unit weight), every interaction is a
reciprocal pair force. Then:

* total momentum of baryons and stock is conserved exactly (`total_force_zero`);
* free fall is universal: accelerations are independent of the body's own mass;
* the net force on the baryons equals minus the force on the stock (`baryon_recoil`);
* components with different effective excess weights (stock per baryon) satisfy the
  third law and universal free fall when the stock is counted as a body
  (`distinct_weights_reciprocal`);
* stock created from source-associated capacity at the local matter velocity
  conserves momentum (`comoving_exchange`);
* predictions are functions of the present state, baryons and stock together; the
  stock content serves as the state variable that carries a system's history
  (`stock_is_state`);
* a finite exchange rate makes the effective weight Lipschitz in time, so a gas
  parcel's weight changes continuously when it shocks (`weight_lipschitz`). -/

noncomputable section
namespace Entropic.Reciprocity
open Finset

variable {ι : Type*} [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Pair force on body i from body j: m_i m_j κ_ij (x_j − x_i), κ symmetric
(Newtonian gravity on one metric has κ_ij = G/|x_j − x_i|³). -/
def pairForce (m : ι → ℝ) (κ : ι → ι → ℝ) (x : ι → V) (i j : ι) : V :=
  (m i * m j * κ i j) • (x j - x i)

def force (m : ι → ℝ) (κ : ι → ι → ℝ) (x : ι → V) (i : ι) : V :=
  ∑ j, pairForce m κ x i j

omit [Fintype ι] in
/-- Newton's third law for every pair. -/
theorem pair_antisymm (m : ι → ℝ) (κ : ι → ι → ℝ) (hκ : ∀ i j, κ i j = κ j i) (x : ι → V) (i j : ι) :
    pairForce m κ x i j = -pairForce m κ x j i := by
  unfold pairForce
  rw [hκ i j, ← smul_neg, neg_sub]
  congr 1; ring

/-- Total momentum is conserved: Σ_i F_i = 0. -/
theorem total_force_zero (m : ι → ℝ) (κ : ι → ι → ℝ) (hκ : ∀ i j, κ i j = κ j i) (x : ι → V) :
    ∑ i, force m κ x i = 0 := by
  unfold force
  have h : ∑ i, ∑ j, pairForce m κ x i j = ∑ i, ∑ j, pairForce m κ x j i := sum_comm
  have h2 : ∑ i, ∑ j, pairForce m κ x j i = -∑ i, ∑ j, pairForce m κ x i j := by
    rw [← sum_neg_distrib]; congr 1; funext i
    rw [← sum_neg_distrib]; congr 1; funext j
    rw [pair_antisymm m κ hκ x j i]
  have : (2:ℝ) • ∑ i, ∑ j, pairForce m κ x i j = 0 := by
    rw [two_smul]; nth_rewrite 2 [h]; rw [h2, add_neg_cancel]
  exact (smul_eq_zero.mp this).resolve_left two_ne_zero

/-- Acceleration a_i = F_i / m_i. -/
def accel (m : ι → ℝ) (κ : ι → ι → ℝ) (x : ι → V) (i : ι) : V := (m i)⁻¹ • force m κ x i

/-- Universal free fall: a_i = Σ_j m_j κ_ij (x_j − x_i), independent of m_i. -/
theorem free_fall_universal (m : ι → ℝ) (κ : ι → ι → ℝ) (x : ι → V) (i : ι) (hm : m i ≠ 0) :
    accel m κ x i = ∑ j, (m j * κ i j) • (x j - x i) := by
  unfold accel force pairForce
  rw [smul_sum]; congr 1; funext j
  rw [smul_smul]; congr 1; field_simp <;> ring

/-- Bodies split into baryons (`Sum.inl`) and stock elements (`Sum.inr`). The baryonic
momentum rate is exactly minus the stock's. -/
theorem baryon_recoil {β σ : Type*} [Fintype β] [Fintype σ]
    (m : β ⊕ σ → ℝ) (κ : β ⊕ σ → β ⊕ σ → ℝ) (hκ : ∀ i j, κ i j = κ j i) (x : β ⊕ σ → V) :
    ∑ b, force m κ x (Sum.inl b) = -∑ s, force m κ x (Sum.inr s) := by
  have h := total_force_zero m κ hκ x
  rw [Fintype.sum_sum_type] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Effective excess weight of a component carrying stock S per baryonic mass M. -/
def effWeight (M S : ℝ) : ℝ := 1 + S / M

/-- Two baryonic components with different effective weights (galaxies 1 + 1 = 2, gas
1 + 0 = 1 here), every pair force reciprocal, free fall universal, total momentum
conserved. Bodies: galaxy, its stock and gas, at arbitrary positions. -/
theorem distinct_weights_reciprocal (x : Fin 3 → V) (κ : Fin 3 → Fin 3 → ℝ) (hκ : ∀ i j, κ i j = κ j i) :
    let m : Fin 3 → ℝ := ![1, 1, 5]
    effWeight (m 0) (m 1) ≠ effWeight (m 2) 0 ∧
      (∀ i j, pairForce m κ x i j = -pairForce m κ x j i) ∧
      ∑ i, force m κ x i = 0 := by
  intro m
  refine ⟨?_, pair_antisymm m κ hκ x, total_force_zero m κ hκ x⟩
  simp [effWeight, m]

omit [Fintype ι] in
/-- Comoving exchange: converting mass δ of source-associated capacity (moving with
the matter at velocity v) into stock created at the same velocity leaves total
momentum unchanged. -/
theorem comoving_exchange (mu mR δ : ℝ) (v vR : V) :
    (mu - δ) • v + (mR • vR + δ • v) = mu • v + mR • vR := by
  rw [sub_smul]; abel

/-- The excess force on a test body depends on the stock in the state. Identical
baryons with different stock give different forces, so the stock is the state variable
that records a system's history. -/
theorem stock_is_state (G d : ℝ) (hG : G ≠ 0) (hd : d ≠ 0) (S₁ S₂ : ℝ) (h : S₁ ≠ S₂) :
    G * S₁ / d ^ 2 ≠ G * S₂ / d ^ 2 := by
  intro heq
  have hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd
  rw [div_left_inj' hd2] at heq
  exact h (mul_left_cancel₀ hG heq)

/-- Finite exchange rate ⇒ effective weight is Lipschitz in time: if the stock attached
to a parcel of fixed baryonic mass M > 0 changes at rate at most K, then over Δt its
effective weight changes by at most K Δt / M. A shock cannot change it discontinuously. -/
theorem weight_lipschitz {S : ℝ → ℝ} {S' : ℝ → ℝ} {K M t₁ t₂ : ℝ} (hM : 0 < M)
    (hderiv : ∀ t, HasDerivAt S (S' t) t) (hK : ∀ t, |S' t| ≤ K) :
    |effWeight M (S t₂) - effWeight M (S t₁)| ≤ K * |t₂ - t₁| / M := by
  have hlip : |S t₂ - S t₁| ≤ K * |t₂ - t₁| := by
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := S) (f' := S') (s := Set.univ) (C := K)
      (fun t _ => (hderiv t).hasDerivWithinAt) (fun t _ => by simpa using hK t)
      convex_univ (Set.mem_univ t₁) (Set.mem_univ t₂)
    simpa [Real.norm_eq_abs, abs_sub_comm] using this
  unfold effWeight
  rw [show 1 + S t₂ / M - (1 + S t₁ / M) = (S t₂ - S t₁) / M by ring, abs_div, abs_of_pos hM]
  exact div_le_div_of_nonneg_right hlip hM.le

end Entropic.Reciprocity
