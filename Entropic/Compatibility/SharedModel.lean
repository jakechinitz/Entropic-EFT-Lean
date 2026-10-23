import Entropic.Spine
import Entropic.PositiveReconstruction
import Entropic.RetainedRelaxation
import Entropic.PositiveLedger
import Entropic.Reciprocity
import Entropic.Spherical
import Entropic.Compatibility.History

/-! A joint witness for a stated finite effective subsystem, not the full EFT.
All response lemmas below use the same stock, baryons, eta and epsilon.
No field in the model is an arbitrary proposition. In particular none is True.
The field equations, native interacting geometry, and empirical likelihood
are deliberately not represented by empty placeholders or asserted solved.
-/
noncomputable section
open scoped BigOperators
namespace Entropic.Compatibility
open Entropic.FiniteModel Entropic.ClosureRoot

def epsilon (eta : ℝ) : ℝ := gshare eta / (4 * Real.pi^2)

structure SharedModel where
  eta : ℝ
  stationary : ClosureStationary eta
  baryon : Fin 2 → ℝ
  baryon_pos : ∀ i, 0 < baryon i
  stock : Fin 2 → ℝ
  stock_pos : ∀ i, 0 < stock i
  unreleased : ℝ
  unreleased_pos : 0 < unreleased
  fraction : ℝ
  fraction_pos : 0 < fraction
  fraction_lt_one : fraction < 1
  -- The same partially released, exponentially drained cohort supplies the stock.
  capacity_link : unreleased + ∑ i, stock i =
    ((∑ i, baryon i) / epsilon eta) * Real.exp (-eta*fraction)
  release_link : (∑ i, stock i) = fraction*(unreleased+∑ i, stock i)
  position : Fin 2 → ℝ
  separated : position 0 ≠ position 1
  target : Fin 2 → ℝ
  target_nonneg : ∀ i, 0 ≤ target i
  target_normalized : ∑ i, target i = 1
  -- Require a real redistribution, not a stationary/empty example.
  disequilibrium : stock 0 ≠ target 0 * (∑ i, stock i)

namespace SharedModel

def mass (m : SharedModel) (i : Fin 2) := m.baryon i + m.stock i
def retained (m : SharedModel) := ∑ i, m.stock i
def capacity (m : SharedModel) := m.unreleased + m.retained
def accelerationScale (m : SharedModel) (c H : ℝ) := epsilon m.eta * c * H

theorem epsilon_pos (m : SharedModel) : 0 < epsilon m.eta := by
  have h := (Entropic.Spine.epsilon_bracket m.stationary).1
  change 0.1879 < epsilon m.eta at h
  linarith

theorem retained_pos (m : SharedModel) : 0 < m.retained := by
  simp only [retained, Fin.sum_univ_two]
  exact add_pos (m.stock_pos 0) (m.stock_pos 1)

theorem capacity_pos (m : SharedModel) : 0 < m.capacity := add_pos m.unreleased_pos m.retained_pos

theorem mass_pos (m : SharedModel) (i : Fin 2) : 0 < m.mass i :=
  add_pos (m.baryon_pos i) (m.stock_pos i)

-- Same epsilon in the formation budget and the acceleration scale.
theorem cross_sector_normalization (m : SharedModel) (c H : ℝ) :
    m.accelerationScale c H * (1 / epsilon m.eta) = c * H := by
  unfold accelerationScale
  field_simp [m.epsilon_pos.ne']

def reconstructed (m : SharedModel) (C : Matrix (Fin 2) (Fin 2) ℝ) :=
  Entropic.PositiveReconstruction.reconstruct C m.stock

theorem reconstructed_positive (m : SharedModel) (C : Matrix (Fin 2) (Fin 2) ℝ)
    (hC : ∀ i j, 0 ≤ C i j) : ∀ i, 0 ≤ m.reconstructed C i :=
  Entropic.PositiveReconstruction.nonnegative C m.stock hC (fun i => (m.stock_pos i).le)

theorem reconstructed_mass (m : SharedModel) (C : Matrix (Fin 2) (Fin 2) ℝ)
    (hC : ∀ j, ∑ i, C i j = 1) : ∑ i, m.reconstructed C i = m.retained :=
  Entropic.PositiveReconstruction.total_preserved C m.stock hC

def redistributed (m : SharedModel) (s : ℝ) (i : Fin 2) :=
  (1-s)*m.stock i + s*m.target i*m.retained

theorem redistributed_positive (m : SharedModel) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    ∀ i, 0 ≤ m.redistributed s i := by
  intro i
  exact add_nonneg (mul_nonneg (by linarith) (m.stock_pos i).le)
    (mul_nonneg (mul_nonneg h0 (m.target_nonneg i)) m.retained_pos.le)

theorem redistributed_mass (m : SharedModel) (s : ℝ) :
    (∑ i, m.redistributed s i) = m.retained := by
  simp only [redistributed, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    m.target_normalized, mul_one, retained]
  ring

theorem redistribution_nontrivial (m : SharedModel) : m.redistributed (1/2) 0 ≠ m.stock 0 := by
  intro h
  apply m.disequilibrium
  change (1-1/2)*m.stock 0+(1/2)*m.target 0*m.retained=m.stock 0 at h
  change m.stock 0=m.target 0*m.retained
  linarith

theorem pair_reciprocal (m : SharedModel) (k : Fin 2 → Fin 2 → ℝ)
    (hk : ∀ i j, k i j = k j i) (i j : Fin 2) :
    Entropic.Reciprocity.pairForce m.mass k m.position i j =
      -Entropic.Reciprocity.pairForce m.mass k m.position j i :=
  Entropic.Reciprocity.pair_antisymm m.mass k hk m.position i j

theorem momentum_conserved (m : SharedModel) (k : Fin 2 → Fin 2 → ℝ)
    (hk : ∀ i j, k i j = k j i) :
    ∑ i, Entropic.Reciprocity.force m.mass k m.position i = 0 :=
  Entropic.Reciprocity.total_force_zero m.mass k hk m.position

def newtonKernel (m : SharedModel) (G : ℝ) (i j : Fin 2) :=
  G / |m.position j-m.position i|^3

theorem newton_kernel_symmetric (m : SharedModel) (G : ℝ) (i j : Fin 2) :
    m.newtonKernel G i j=m.newtonKernel G j i := by
  simp only [newtonKernel, abs_sub_comm]

theorem newton_pair_force_nonzero (m : SharedModel) {G : ℝ} (hG : 0 < G) :
    Entropic.Reciprocity.pairForce m.mass (m.newtonKernel G) m.position 0 1 ≠ 0 := by
  have hd : m.position 1-m.position 0 ≠ 0 := sub_ne_zero.mpr m.separated.symm
  have hk : 0 < m.newtonKernel G 0 1 := div_pos hG (pow_pos (abs_pos.mpr hd) _)
  change (m.mass 0*m.mass 1*m.newtonKernel G 0 1)*(m.position 1-m.position 0) ≠ 0
  exact mul_ne_zero (mul_pos (mul_pos (m.mass_pos 0) (m.mass_pos 1)) hk).ne' hd

-- Nonzero release and drain, applied to exactly this model's donor components.
theorem active_release (m : SharedModel) :
    0 < m.eta * m.capacity ∧
    (-m.capacity - m.unreleased/m.capacity*(m.eta*m.capacity)) +
    (m.capacity - m.retained/m.capacity*(m.eta*m.capacity)) + m.eta*m.capacity = 0 := by
  refine ⟨mul_pos m.stationary.1 m.capacity_pos, ?_⟩
  exact Entropic.PositiveLedger.common_drain_conserves m.unreleased m.retained
    m.capacity (m.eta*m.capacity) m.capacity_pos.ne'

theorem native_predictions (m : SharedModel) :
    etaLo < m.eta ∧ m.eta < etaHi ∧
    gLo < gshare m.eta ∧ gshare m.eta < gHi ∧
    20676828023 / 10^8 < Entropic.Spine.muRatio m.eta ∧
    Entropic.Spine.muRatio m.eta < 20676828024 / 10^8 ∧
    347734330 / 10^5 < Entropic.Spine.tauRatio m.eta ∧
    Entropic.Spine.tauRatio m.eta < 347734331 / 10^5 :=
  ⟨(stationary_bracket m.stationary).1, (stationary_bracket m.stationary).2,
    (gshare_bracket m.stationary).1, (gshare_bracket m.stationary).2,
    (Entropic.Spine.muRatio_bracket m.stationary).1,
    (Entropic.Spine.muRatio_bracket m.stationary).2,
    (Entropic.Spine.tauRatio_bracket m.stationary).1,
    (Entropic.Spine.tauRatio_bracket m.stationary).2⟩

end SharedModel

theorem shared_model_exists : Nonempty SharedModel := by
  obtain ⟨eta, hs, _, _⟩ := stationary_exists
  have he : 0 < epsilon eta := by
    have h := (Entropic.Spine.epsilon_bracket hs).1
    change 0.1879 < epsilon eta at h
    linarith
  let C := 2 / epsilon eta * Real.exp (-eta/2)
  have hC : 0 < C := mul_pos (div_pos (by norm_num) he) (Real.exp_pos _)
  refine ⟨{
    eta := eta
    stationary := hs
    baryon := fun _ => 1
    baryon_pos := by intro i; norm_num
    stock := fun _ => C/4
    stock_pos := by intro i; positivity
    unreleased := C/2
    unreleased_pos := by positivity
    fraction := 1/2
    fraction_pos := by norm_num
    fraction_lt_one := by norm_num
    capacity_link := ?_
    release_link := ?_
    position := ![0,1]
    separated := by norm_num
    target := ![1,0]
    target_nonneg := ?_
    target_normalized := ?_
    disequilibrium := ?_ }⟩
  · simp [Fin.sum_univ_two, C]; ring_nf
  · simp [Fin.sum_univ_two]; ring
  · intro i; fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_two]
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, one_mul]
    linarith

/-- This strengthened exact-law bundle is impossible even at a single dense
core point. It is NOT the paper's repaired projected branch. -/
structure ExactDenseCore where
  amplitude : ℝ
  amplitude_pos : 0 < amplitude
  coordinate : ℝ
  dense : 6 ≤ coordinate
  enclosedStock : ℝ → ℝ
  raw_exact : enclosedStock = Entropic.Spherical.coreExcessMass amplitude
  positive_density : 0 ≤ deriv enclosedStock coordinate

theorem exact_dense_core_isEmpty : IsEmpty ExactDenseCore := by
  constructor
  intro m
  exact Entropic.Spherical.no_nonnegative_stock_matching_core
    m.amplitude_pos m.dense m.enclosedStock m.raw_exact m.positive_density

end Entropic.Compatibility
