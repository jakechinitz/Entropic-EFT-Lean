import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! Stock settling: momentum, reversibility and a finite work budget (Sec. 18, App. O.3).

1. Momentum. Each central pair contact at fixed positions (impulse `α (x i - x j)` on
   `i`, the opposite on `j`) conserves total linear and angular momentum, and so does any
   finite schedule of such contacts (`schedule_conserves`). Symmetric central pair forces
   have zero resultant and zero total torque (`central_forces_balance`), and the kinetic
   term of the angular-momentum rate vanishes (`streaming_angular_rate`). A force acting
   on the stock alone conserves momentum only if its resultant vanishes; otherwise the
   carriers take the opposite resultant (`recoil_required`).

2. Reversibility. A reversible dynamics on a finite phase space maps exactly `|T|` states
   into a target set `T` (`reversible_no_concentration`) and preserves every Casimir sum
   of a transported density (`casimir_invariant`). These are fine-grained statements;
   coarse-grained relaxation by phase mixing is not addressed.

3. Budget. For the contact of the effective-dynamics note, with work `W` per net
   transition charged on a signed ledger and supply `D`, the population when the supply
   runs out is `w₀ + D / W` for every rate `ν > 0` (`endpoint_rate_free`); the time to
   reach it depends on `ν`. A ledger that charges each event without refund gives a
   rate-dependent endpoint and is not covered. If the work per transition is `κ σ²` and
   the supply per unit stock `d` is fixed, the attained fraction `min(1, σ_c² / σ²)` of the
   population gap is settled (`settled_fraction_eq`). Both scalings are hypotheses: the
   bath term `Θ ln (h_j / h_i)` of the work scales with `σ²` only if `Θ` does. -/

namespace Entropic.StockSettling

open Finset Matrix

/-! ## 1. Momentum under arbitrary contact schedules -/

section Momentum

variable {N : ℕ}

/-- Total linear momentum. -/
def totalMomentum (p : Fin N → Fin 3 → ℝ) : Fin 3 → ℝ := ∑ k, p k

/-- Total angular momentum about the origin. -/
def angularMomentum (x p : Fin N → Fin 3 → ℝ) : Fin 3 → ℝ := ∑ k, x k ⨯₃ p k

/-- A central contact: element `i` receives the impulse `α (x i - x j)` and element `j`
the opposite impulse. -/
structure Contact (N : ℕ) where
  i : Fin N
  j : Fin N
  α : ℝ

/-- Momenta after one contact at fixed positions. -/
def applyContact (x : Fin N → Fin 3 → ℝ) (c : Contact N) (p : Fin N → Fin 3 → ℝ) :
    Fin N → Fin 3 → ℝ := fun k =>
  p k + (if k = c.i then c.α • (x c.i - x c.j) else 0)
      - (if k = c.j then c.α • (x c.i - x c.j) else 0)

theorem contact_momentum (x : Fin N → Fin 3 → ℝ) (c : Contact N) (p : Fin N → Fin 3 → ℝ) :
    totalMomentum (applyContact x c p) = totalMomentum p := by
  unfold totalMomentum applyContact
  rw [sum_sub_distrib, sum_add_distrib, sum_ite_eq', sum_ite_eq']
  simp

theorem contact_angular (x : Fin N → Fin 3 → ℝ) (c : Contact N) (p : Fin N → Fin 3 → ℝ) :
    angularMomentum x (applyContact x c p) = angularMomentum x p := by
  unfold angularMomentum applyContact
  simp only [map_sub, map_add]
  rw [sum_sub_distrib, sum_add_distrib]
  have h1 : ∑ k, x k ⨯₃ (if k = c.i then c.α • (x c.i - x c.j) else 0)
      = x c.i ⨯₃ (c.α • (x c.i - x c.j)) := by
    rw [sum_eq_single c.i (fun b _ hb => by simp [hb]) (fun h => absurd (mem_univ _) h)]
    simp
  have h2 : ∑ k, x k ⨯₃ (if k = c.j then c.α • (x c.i - x c.j) else 0)
      = x c.j ⨯₃ (c.α • (x c.i - x c.j)) := by
    rw [sum_eq_single c.j (fun b _ hb => by simp [hb]) (fun h => absurd (mem_univ _) h)]
    simp
  rw [h1, h2]
  have h3 : x c.i ⨯₃ (c.α • (x c.i - x c.j)) - x c.j ⨯₃ (c.α • (x c.i - x c.j))
      = c.α • ((x c.i - x c.j) ⨯₃ (x c.i - x c.j)) := by
    simp only [map_smul, map_sub, LinearMap.sub_apply, smul_sub]
    abel
  rw [add_sub_assoc, h3, cross_self, smul_zero, add_zero]

/-- Momenta after a finite schedule of contacts, applied in order. -/
def applySchedule (x : Fin N → Fin 3 → ℝ) : List (Contact N) → (Fin N → Fin 3 → ℝ) →
    Fin N → Fin 3 → ℝ
  | [], p => p
  | c :: cs, p => applySchedule x cs (applyContact x c p)

/-- Every schedule of central contacts conserves total linear and angular momentum. -/
theorem schedule_conserves (x : Fin N → Fin 3 → ℝ) (cs : List (Contact N))
    (p : Fin N → Fin 3 → ℝ) :
    totalMomentum (applySchedule x cs p) = totalMomentum p ∧
      angularMomentum x (applySchedule x cs p) = angularMomentum x p := by
  induction cs generalizing p with
  | nil => exact ⟨rfl, rfl⟩
  | cons c cs ih =>
    obtain ⟨h1, h2⟩ := ih (applyContact x c p)
    exact ⟨h1.trans (contact_momentum x c p), h2.trans (contact_angular x c p)⟩

/-- Symmetric central pair forces: `F k = ∑ l, c k l • (x l - x k)`. -/
def pairForce (c : Fin N → Fin N → ℝ) (x : Fin N → Fin 3 → ℝ) (k : Fin N) : Fin 3 → ℝ :=
  ∑ l, c k l • (x l - x k)

/-- Common-potential streaming: symmetric central pair forces have zero resultant and
zero total torque. -/
theorem central_forces_balance (c : Fin N → Fin N → ℝ) (hc : ∀ k l, c k l = c l k)
    (x : Fin N → Fin 3 → ℝ) :
    ∑ k, pairForce c x k = 0 ∧ ∑ k, x k ⨯₃ pairForce c x k = 0 := by
  constructor
  · unfold pairForce
    have hs : ∑ k, ∑ l, c k l • (x l - x k) = -∑ k, ∑ l, c k l • (x l - x k) := by
      conv_rhs => rw [sum_comm]
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun k _ => ?_
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun l _ => ?_
      rw [hc, ← smul_neg, neg_sub]
    have := eq_neg_iff_add_eq_zero.mp hs
    rwa [← two_smul ℝ, smul_eq_zero, or_iff_right (by norm_num)] at this
  · unfold pairForce
    simp only [map_sum, map_smul, map_sub, cross_self, sub_zero]
    have hs : ∑ k, ∑ l, c k l • (x k ⨯₃ x l) = -∑ k, ∑ l, c k l • (x k ⨯₃ x l) := by
      conv_rhs => rw [sum_comm]
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun k _ => ?_
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun l _ => ?_
      rw [hc, ← smul_neg, cross_anticomm]
    have := eq_neg_iff_add_eq_zero.mp hs
    rwa [← two_smul ℝ, smul_eq_zero, or_iff_right (by norm_num)] at this

/-- Angular momentum rate under streaming with velocities `p k / m k` and forces `F`:
the kinetic term vanishes identically, so the rate is the total torque. -/
theorem streaming_angular_rate (m : Fin N → ℝ) (p F x : Fin N → Fin 3 → ℝ) :
    ∑ k, ((m k)⁻¹ • p k) ⨯₃ p k + ∑ k, x k ⨯₃ F k = ∑ k, x k ⨯₃ F k := by
  simp [cross_self]

/-- A force field acting on the stock only. The total momentum rate is its resultant;
conservation requires the carriers to receive the opposite resultant. -/
theorem recoil_required (stock : Finset (Fin N)) (g : Fin N → Fin 3 → ℝ)
    (Fcarrier : Fin N → Fin 3 → ℝ)
    (hbal : ∑ k, ((if k ∈ stock then g k else 0) + Fcarrier k) = 0) :
    ∑ k, Fcarrier k = -∑ k ∈ stock, g k := by
  rw [sum_add_distrib, ← sum_filter] at hbal
  have : ∑ k ∈ univ.filter (· ∈ stock), g k = ∑ k ∈ stock, g k := by
    congr 1; ext k; simp
  rw [this] at hbal
  exact eq_neg_of_add_eq_zero_right hbal

end Momentum

/-! ## 2. Reversible dynamics cannot select a target -/

section Selection

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The number of states that reach `T` after `n` ticks of a reversible dynamics equals
`|T|`: no reversible dynamics concentrates an ensemble onto a smaller target. -/
theorem reversible_no_concentration (σ : Equiv.Perm Ω) (n : ℕ) (T : Finset Ω) :
    (univ.filter fun ω => (σ ^ n) ω ∈ T).card = T.card := by
  refine card_bij (fun ω _ => (σ ^ n) ω) (fun ω hω => by simpa using hω)
    (fun a _ b _ h => (σ ^ n).injective h) ?_
  intro t ht
  exact ⟨((σ ^ n).symm) t, by simpa using ht, by simp⟩

omit [DecidableEq Ω] in
/-- Casimir invariance: transporting a density by a reversible map preserves every sum
`∑ C(f ω)`, in particular the fine-grained entropy. -/
theorem casimir_invariant (σ : Equiv.Perm Ω) (f : Ω → ℝ) (C : ℝ → ℝ) :
    ∑ ω, C (f ((σ.symm) ω)) = ∑ ω, C (f ω) :=
  Equiv.sum_comp σ.symm (fun ω => C (f ω))

end Selection

/-! ## 3. The finite work budget selects by velocity dispersion -/

section Budget

/-- Population along contact activity `s`: `w(s) = p + (w₀ - p) e^{-ν s}`. -/
noncomputable def population (p w₀ ν s : ℝ) : ℝ := p + (w₀ - p) * Real.exp (-ν * s)

/-- Activity at which the work supply `D` is exhausted. -/
noncomputable def exhaustion (p w₀ ν D W : ℝ) : ℝ :=
  -(1 / ν) * Real.log (1 - D / (W * (p - w₀)))

/-- The population reached when the supply runs out is `w₀ + D / W`, for every contact
rate `ν > 0`. -/
theorem endpoint_rate_free {p w₀ ν D W : ℝ} (hν : 0 < ν) (hW : 0 < W) (hpw : w₀ < p)
    (hshort : D < W * (p - w₀)) :
    population p w₀ ν (exhaustion p w₀ ν D W) = w₀ + D / W := by
  have hgap : 0 < W * (p - w₀) := mul_pos hW (by linarith)
  have harg : 0 < 1 - D / (W * (p - w₀)) := by
    rw [sub_pos, div_lt_one hgap]; exact hshort
  unfold population exhaustion
  have : -ν * (-(1 / ν) * Real.log (1 - D / (W * (p - w₀))))
      = Real.log (1 - D / (W * (p - w₀))) := by field_simp
  rw [this, Real.exp_log harg]
  have hp : p - w₀ ≠ 0 := by linarith
  field_simp
  ring

/-- Ledger: the work spent up to activity `s` is `W (w(s) - w₀)`. At the endpoint above,
it equals the full supply `D`. -/
theorem endpoint_spends_supply {p w₀ ν D W : ℝ} (hν : 0 < ν) (hW : 0 < W) (hpw : w₀ < p)
    (hshort : D < W * (p - w₀)) :
    W * (population p w₀ ν (exhaustion p w₀ ν D W) - w₀) = D := by
  rw [endpoint_rate_free hν hW hpw hshort]; field_simp; ring

/-- Attained population with a finite budget. -/
noncomputable def budgetEndpoint (p w₀ D W : ℝ) : ℝ := min p (w₀ + D / W)

theorem budget_endpoint_settles {p w₀ D W : ℝ} (hW : 0 < W) :
    budgetEndpoint p w₀ D W = p ↔ W * (p - w₀) ≤ D := by
  unfold budgetEndpoint
  rw [min_eq_left_iff, ← sub_le_iff_le_add', le_div_iff₀ hW, mul_comm]

/-- Settled fraction `(w_∞ - w₀) / (p - w₀)`. -/
noncomputable def settledFraction (p w₀ D W : ℝ) : ℝ :=
  (budgetEndpoint p w₀ D W - w₀) / (p - w₀)

/-- Threshold dispersion: `σ_c² = d / (κ (p - w₀))`. -/
noncomputable def sigmaC2 (p w₀ d κ : ℝ) : ℝ := d / (κ * (p - w₀))

/-- With work per transition `κ σ²` and supply `d` per unit stock, the settled fraction is
`min 1 (σ_c² / σ²)`. -/
theorem settled_fraction_eq {p w₀ d κ σ : ℝ} (hpw : w₀ < p) (hκ : 0 < κ) (hσ : 0 < σ) :
    settledFraction p w₀ d (κ * σ ^ 2) = min 1 (sigmaC2 p w₀ d κ / σ ^ 2) := by
  have hp : 0 < p - w₀ := by linarith
  have hσ2 : 0 < σ ^ 2 := by positivity
  unfold settledFraction budgetEndpoint sigmaC2
  rw [← min_sub_sub_right, ← min_div_div_right hp.le]
  congr 1
  · rw [div_self hp.ne']
  · field_simp
    ring

theorem settles_iff_below_threshold {p w₀ d κ σ : ℝ} (hpw : w₀ < p) (hκ : 0 < κ)
    (hσ : 0 < σ) :
    settledFraction p w₀ d (κ * σ ^ 2) = 1 ↔ σ ^ 2 ≤ sigmaC2 p w₀ d κ := by
  rw [settled_fraction_eq hpw hκ hσ, min_eq_left_iff, one_le_div (by positivity)]

/-- Above threshold the settled fraction falls as `σ⁻²`. -/
theorem settled_fraction_above {p w₀ d κ σ : ℝ} (hpw : w₀ < p) (hκ : 0 < κ) (hσ : 0 < σ)
    (habove : sigmaC2 p w₀ d κ ≤ σ ^ 2) :
    settledFraction p w₀ d (κ * σ ^ 2) = sigmaC2 p w₀ d κ / σ ^ 2 := by
  rw [settled_fraction_eq hpw hκ hσ, min_eq_right]
  rw [div_le_one (by positivity)]; exact habove

/-- Numerical illustration: a threshold `σ_c ≤ 320 km/s` leaves at most `21%` of a
`700 km/s` system's stock settled, and at most `10.3%` at `1000 km/s`. -/
theorem cluster_fraction_bounds {s2 : ℝ} (hs : s2 ≤ 320 ^ 2) :
    min 1 (s2 / 700 ^ 2) ≤ 0.21 ∧ min 1 (s2 / 1000 ^ 2) ≤ 0.1025 := by
  constructor
  · refine le_trans (min_le_right _ _) ?_
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  · refine le_trans (min_le_right _ _) ?_
    rw [div_le_iff₀ (by norm_num)]; nlinarith

end Budget

end Entropic.StockSettling
