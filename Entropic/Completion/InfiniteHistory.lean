import Entropic.Compatibility.GibbsHistory
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! A single probability space for all times, at the exact native Gibbs marginal.
The two-sided shift is reversible and measure-preserving. This is a classical
history construction, not a microscopic quantum-gravity or energy-supply proof. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace Entropic.Completion.InfiniteHistory
open Entropic.Compatibility.GibbsHistory

instance : MeasurableSpace Microstate := ⊤
instance : MeasurableSingletonClass Microstate := ⟨fun _ => trivial⟩

def nativePMF (eta : ℝ) : PMF Microstate :=
  PMF.ofFintype (fun s => ENNReal.ofReal (probability eta s)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => (probability_positive eta s).le),
      probability_normalized, ENNReal.ofReal_one])

def nativeMeasure (eta : ℝ) : Measure Microstate := (nativePMF eta).toMeasure
instance (eta : ℝ) : IsProbabilityMeasure (nativeMeasure eta) := inferInstanceAs
  (IsProbabilityMeasure (nativePMF eta).toMeasure)

abbrev History := ℤ → Microstate
def law (eta : ℝ) : Measure History := Measure.infinitePi (fun _ : ℤ => nativeMeasure eta)
instance (eta : ℝ) : IsProbabilityMeasure (law eta) := inferInstanceAs
  (IsProbabilityMeasure (Measure.infinitePi (fun _ : ℤ => nativeMeasure eta)))

theorem native_singleton (eta : ℝ) (s : Microstate) :
    nativeMeasure eta {s} = ENNReal.ofReal (probability eta s) :=
  (nativePMF eta).toMeasure_apply_singleton s (measurableSet_singleton s)

theorem cylinder_law (eta : ℝ) (times : Finset ℤ) (word : ℤ → Microstate) :
    law eta (Set.pi (times : Set ℤ) (fun t => {word t})) =
      ∏ t ∈ times, ENNReal.ofReal (probability eta (word t)) := by
  rw [law, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp only [native_singleton]

theorem cylinder_positive (eta : ℝ) (times : Finset ℤ) (word : ℤ → Microstate) :
    0 < law eta (Set.pi (times : Set ℤ) (fun t => {word t})) := by
  rw [cylinder_law]
  apply pos_iff_ne_zero.mpr
  exact Finset.prod_ne_zero_iff.mpr (fun t _ => (ENNReal.ofReal_pos.mpr (probability_positive eta (word t))).ne')

def tickIndex : ℤ ≃ ℤ where
  toFun := fun t => t-1
  invFun := fun t => t+1
  left_inv := by intro t; dsimp; omega
  right_inv := by intro t; dsimp; omega

def tick : History ≃ History := Equiv.piCongrLeft (fun _ : ℤ => Microstate) tickIndex

theorem tick_read (h : History) (t : ℤ) : tick h t = h (t+1) := by
  simp [tick, Equiv.piCongrLeft_apply, tickIndex]

theorem tick_injective : Function.Injective tick := tick.injective

theorem stationary (eta : ℝ) : (law eta).map tick = law eta := by
  exact Measure.infinitePi_map_piCongrLeft (fun _ : ℤ => nativeMeasure eta) tickIndex

theorem all_finite_marginals (eta : ℝ) (I : Finset ℤ) :
    (law eta).map I.restrict = Measure.pi (fun _ : I => nativeMeasure eta) :=
  Measure.infinitePi_map_restrict _

-- Finite accessible states do not bound the past of an unbounded archive.
theorem integer_time_has_no_first : ¬ ∃ t : ℤ, ∀ s : ℤ, t ≤ s := by
  rintro ⟨t,ht⟩
  have := ht (t-1)
  omega

theorem past_exists_at_every_tick (t : ℤ) : ∃ s : ℤ, s < t := ⟨t-1, by omega⟩

def blank : Microstate := ⟨0,⟨0,by decide⟩⟩
def rootMarginal (eta : ℝ) (t : ℤ) : Measure Microstate :=
  if 0≤t then nativeMeasure eta else Measure.dirac blank
instance (eta : ℝ) (t : ℤ) : IsProbabilityMeasure (rootMarginal eta t) := by
  unfold rootMarginal; split_ifs <;> infer_instance
def rootedLaw (eta : ℝ) : Measure History := Measure.infinitePi (rootMarginal eta)
instance (eta : ℝ) : IsProbabilityMeasure (rootedLaw eta) := inferInstanceAs
  (IsProbabilityMeasure (Measure.infinitePi (rootMarginal eta)))

-- A chosen initial boundary is compatible with exact future renewal.
-- It is an extra initial-state choice, not a consequence of finite accessible capacity.
theorem rooted_future_law (eta : ℝ) (times : Finset ℤ) (ht : ∀ t∈times,0≤t)
    (word : ℤ → Microstate) :
    rootedLaw eta (Set.pi (times : Set ℤ) (fun t => {word t}))=
      ∏ t∈times,ENNReal.ofReal (probability eta (word t)) := by
  rw [rootedLaw,Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  apply Finset.prod_congr rfl
  intro t hmem
  rw [rootMarginal,if_pos (ht t hmem),native_singleton]

theorem rooted_past_blank (eta : ℝ) (t : ℤ) (ht : t<0) : rootMarginal eta t=Measure.dirac blank := by
  simp [rootMarginal,not_le.mpr ht]

end Entropic.Completion.InfiniteHistory
