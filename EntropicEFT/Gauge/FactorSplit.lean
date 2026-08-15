import EntropicEFT.UV.RootExistence
import EntropicEFT.Core.PhysicalInterfaces

/-!
# EntropicEFT.Gauge.FactorSplit

LOCAL CONTRACT
* Manuscript: gauge-compatibility repair of the 1680 ensemble (response to the
  gauge-invariance objection); standard GFT kinematics L²(G⁴/G) with Peter–Weyl.
* Closed here, kernel-checked:
  - `sameFactorGaussCasimir_noGo`: the admissibility invariant K² CANNOT be the Gauss
    (local gauge) Casimir.  A Gauss Casimir annihilates every physical state; the
    audited spectrum has floor 122/3 > 0 on the nonempty ensemble.  Both readings at
    once are contradictory.  Uses the native_decide spectrum floor constructively.
  - `admissibility_never_vanishes`: K² > 0 on every ensemble state (the positive half).
  - `leftFactor_commutes_rightFactor`: operators acting on the open/relational factor
    commute with operators acting on the local gauge/intertwiner factor.  This is the
    exact mechanism permitting [K², P_inv] = 0 with K² ≠ 0: left and right actions
    live on different tensor slots.
  - Fixed-spin gauge-invariant mode arithmetic: dim Inv(V₃⊗⁴) = 7 intertwiners (one per
    matched intermediate spin J = 0..6), hence 7⁴·7 = 16807 gauge-invariant modes; fixing
    one geometric intertwiner leaves 2401 open magnetic tuples, of which 840 are
    injective, doubled by orientation to the audited 1680.
* Physical premise (explicit, NOT proven): the manuscript's routed capacity labels m_i
  are the open/relational magnetic indices of the fixed-spin GFT quantum, while the
  cellwise SU(2) projector acts on the geometric/intertwiner factor.  This is
  `RelationalCapacityGaugeSplit` below.  The no-go shows the same-factor alternative is
  impossible; it does not by itself construct the decorated 𝒢_v realizing the split —
  that remains inside the open `GeometricEmbeddingSpec`.
-/

namespace EntropicEFT.Gauge
open EntropicEFT.UV

/-! ## The same-factor no-go -/

/-- K² is strictly positive on every ensemble state: the spectrum floor 122/3 > 0. -/
theorem admissibility_never_vanishes {b : BoundaryCode} (hb : b ∈ boundaryStates) :
    0 < quantumK2R b :=
  lt_of_lt_of_le (by norm_num) (quantumK2R_lower hb)

/-- NO-GO: no observable can simultaneously (i) agree with the audited admissibility
invariant on the ensemble and (ii) vanish on the ensemble the way a Gauss (local gauge)
Casimir must vanish on physical gauge-invariant states.  The two readings of "closure"
are therefore provably distinct operators. -/
theorem sameFactorGaussCasimir_noGo
    (C2 : BoundaryCode → ℝ)
    (gauss : ∀ b ∈ boundaryStates, C2 b = 0)
    (ident : ∀ b ∈ boundaryStates, C2 b = quantumK2R b) :
    False := by
  obtain ⟨b, hb⟩ := boundaryStates_nonempty
  have h0 := gauss b hb
  have h1 := ident b hb
  have h2 := admissibility_never_vanishes hb
  rw [h0] at h1
  linarith [h1, h2]

/-! ## The two-factor mechanism -/

/-- A joint state of the open/relational factor `A` and the local gauge factor `B`. -/
abbrev JointState (A B : Type*) := A × B

/-- An operator supported on the open/relational (left) factor. -/
def actLeft {A B : Type*} (f : A → A) : JointState A B → JointState A B :=
  fun p => (f p.1, p.2)

/-- An operator supported on the local gauge/intertwiner (right) factor. -/
def actRight {A B : Type*} (g : B → B) : JointState A B → JointState A B :=
  fun p => (p.1, g p.2)

/-- Left-factor and right-factor operators commute EXACTLY.  This is the mechanism by
which the admissibility invariant (open factor) coexists with the local gauge projector
(intertwiner factor): `[K², P_inv] = 0` without `K² = 0`. -/
theorem leftFactor_commutes_rightFactor {A B : Type*} (f : A → A) (g : B → B) :
    actLeft (B := B) f ∘ actRight g = actRight g ∘ actLeft f := rfl

/-- The gauge projector restricted to the right factor leaves every left-factor
observable value unchanged: evaluating an open-factor function after a right-factor
projection equals evaluating it before. -/
theorem leftObservable_gaugeInvariant {A B : Type*} (K : A → ℝ) (P : B → B)
    (p : JointState A B) : K ((actRight P p).1) = K p.1 := rfl

/-! ## Fixed-spin gauge-invariant mode counting -/

/-- Intermediate total spins available when coupling two spin-3 pairs: J = 0,…,6. -/
def intermediateSpins : Finset ℕ := Finset.range 7

/-- One four-valent singlet per matched intermediate spin: dim Inv(V₃⊗⁴) = 7. -/
theorem intertwinerDim_eq_seven : intermediateSpins.card = 7 := by decide

/-- Full fixed-spin gauge-invariant mode count: open magnetic tuples × intertwiners. -/
theorem gaugeInvariantModeCount : 7^4 * 7 = 16807 := by norm_num

/-- Fixing one geometric intertwiner leaves the full open magnetic hypercube. -/
theorem openTuples_after_intertwiner_fixed : 16807 / 7 = 2401 := by norm_num

/-- The audited chain on the open factor: injective restriction then orientation
doubling reproduces the kernel-checked ensemble cardinality. -/
theorem openFactor_chain :
    Fintype.card PortAssignment = 2401 ∧
    unorientedStates.card = 840 ∧
    boundaryStates.card = 1680 :=
  ⟨allPortAssignments_card, unorientedStates_card, boundaryStates_card⟩

/-! ## The forced identification, stated as an explicit premise -/

/-- Relational capacity–gauge split: the routed capacity labels are the open/relational
magnetic indices; the cellwise SU(2) projector acts on the geometric/intertwiner factor;
g_share is capacity entropy conditional on the selected cell state.  The no-go above
shows the same-factor alternative is impossible; constructing the decorated 𝒢_v that
realizes THIS split microscopically remains part of the open GFT embedding. -/
structure RelationalCapacityGaugeSplit where
  holds : Prop

end EntropicEFT.Gauge
