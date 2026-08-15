import EntropicEFT.Gauge.FactorSplit
import EntropicEFT.Gauge.ProjectiveColor
import EntropicEFT.Marked.CorrectedH9

/-!
# EntropicEFT.Gauge.SpinePropagation

LOCAL CONTRACT
* Manuscript: gauge-compatibility propagation across the microscopic numerical spine.
* Tightened criterion (correcting a too-weak earlier phrasing): for self-adjoint O,
  descending to the invariant subspace is equivalent to [O, P_inv] = 0, but that is
  WEAKER than full kinematical gauge invariance U(g) O U(g)† = O.  The separated-factor
  construction yields the STRONG form: with U_gauge(g) = I_open ⊗ U_right(g) and
  O = O_open ⊗ I, one has [O, U_gauge(g)] = 0 for EVERY g, hence [O, P_inv] = 0
  automatically.  This module proves the strong form for the spine.
* Closed here, kernel-checked:
  - `fullGaugeAction_commutes`: an open-factor operator commutes with the ENTIRE gauge
    group action (∀ g), not merely with the projector.
  - `openObservable_fullGauge_invariant`: open-slot observable values are unchanged by
    every gauge transformation.
  - A spine ledger: each m-label operator of the microscopic chain — the closure
    invariants (quantumK3, classicalClosure3, quantumVariance3, K²), the three route
    observables (routeA/B/C), the port sums (sumM, sumSq), the Gibbs weight at every η,
    and the injectivity/admissibility predicate — factors through the open slot, hence
    inherits full gauge invariance by the same one-line mechanism.
  - Parameter-level spine quantities (scalarPassage 2/7, pairContractionU, edge
    amplitude, ζ, Z_e chain) contain NO gauge-factor dependence: they are functions of
    (η, g_share) alone, recorded as gauge scalars.
* Not closed here: that the DECORATED microscopic 𝒢_v realizes these operators on the
  open factor of an actual GFT field — that is `RelationalCapacityGaugeSplit` inside the
  open `GeometricEmbeddingSpec`, unchanged.
-/

namespace EntropicEFT.Gauge
open EntropicEFT.UV EntropicEFT.Marked

universe u v w

variable {A : Type u} {B : Type v} {G : Type w}

/-! ## The strong criterion -/

/-- Full gauge action on the joint space: identity on the open factor, an arbitrary
g-indexed family on the gauge factor. -/
def gaugeAction (U : G → B → B) (g : G) : JointState A B → JointState A B :=
  actRight (U g)

/-- STRONG form: an open-factor operator commutes with the ENTIRE gauge group action,
for every group element — not merely with the invariant projector. -/
theorem fullGaugeAction_commutes (f : A → A) (U : G → B → B) :
    ∀ g : G, actLeft (B := B) f ∘ gaugeAction U g = gaugeAction U g ∘ actLeft f :=
  fun _ => rfl

/-- Open-slot observables are pointwise invariant under every gauge transformation. -/
theorem openObservable_fullGauge_invariant {X : Type*} (K : A → X) (U : G → B → B) :
    ∀ (g : G) (p : JointState A B), K ((gaugeAction U g p).1) = K p.1 :=
  fun _ _ => rfl

/-! ## The spine ledger

Each operator below is a function of the open-slot data alone (`PortAssignment` or
`BoundaryCode`).  Its joint-space lift is therefore invariant under the FULL gauge
action.  Individually each proof is `rfl`; the ledger's value is totality: no m-label
operator of the numerical spine escapes the mechanism. -/

section Ledger
variable (U : G → B → B) (g : G)

theorem sumM_gauge_invariant (p : JointState PortAssignment B) :
    sumM ((gaugeAction U g p).1) = sumM p.1 := rfl

theorem sumSq_gauge_invariant (p : JointState PortAssignment B) :
    sumSq ((gaugeAction U g p).1) = sumSq p.1 := rfl

theorem routeA_gauge_invariant (p : JointState PortAssignment B) :
    routeA ((gaugeAction U g p).1) = routeA p.1 := rfl

theorem routeB_gauge_invariant (p : JointState PortAssignment B) :
    routeB ((gaugeAction U g p).1) = routeB p.1 := rfl

theorem routeC_gauge_invariant (p : JointState PortAssignment B) :
    routeC ((gaugeAction U g p).1) = routeC p.1 := rfl

theorem injectivity_gauge_invariant (p : JointState PortAssignment B) :
    ((gaugeAction U g p).1).injective ↔ p.1.injective := Iff.rfl

theorem quantumK3_gauge_invariant (p : JointState BoundaryCode B) :
    quantumK3 ((gaugeAction U g p).1) = quantumK3 p.1 := rfl

theorem classicalClosure3_gauge_invariant (p : JointState BoundaryCode B) :
    classicalClosure3 ((gaugeAction U g p).1) = classicalClosure3 p.1 := rfl

theorem quantumVariance3_gauge_invariant (p : JointState BoundaryCode B) :
    quantumVariance3 ((gaugeAction U g p).1) = quantumVariance3 p.1 := rfl

theorem quantumK2R_gauge_invariant (p : JointState BoundaryCode B) :
    quantumK2R ((gaugeAction U g p).1) = quantumK2R p.1 := rfl

/-- The Gibbs weight — hence the whole admissibility measure — is gauge invariant at
every η, so meanK2, varK2, and the stationary root η* inherit invariance wholesale. -/
theorem weight_gauge_invariant (η : ℝ) (p : JointState BoundaryCode B) :
    weight η ((gaugeAction U g p).1) = weight η p.1 := rfl

end Ledger

/-! ## Parameter-level spine quantities are gauge scalars -/

/-- The singlet passage, pair contraction, edge amplitude, one-fiber weight, and the
three routing traces are functions of (η, g_share) with NO state argument at all: they
cannot carry gauge-factor dependence.  Recorded as a single scalar-ledger theorem. -/
theorem parameter_spine_gauge_scalar :
    (∀ η : ℝ, pairContractionU η = 2 * η * scalarPassage^2) ∧
    (∀ η : ℝ, edgeAmplitude η = noEventAmplitude η ^ edgeRecordCount) ∧
    (∀ gs η : ℝ, zeta gs η = 9 * Real.exp (-gs) * edgeAmplitude η) ∧
    (∀ ζ : ℝ, Ze ζ = (1 + ζ) * (1 + 7*ζ^2)) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩


/-! ## Compositional sufficiency for the decorated vertex

If every generator of the microscopic dynamics is an open-factor operator, then any
finite composition of generators — hence the entire assembled transfer — commutes with
the full gauge action.  This converts the 𝒢_v requirement list into a sufficiency
theorem: decoration locality alone propagates gauge invariance to the assembled
dynamics. -/

/-- Open-factor operators are closed under composition. -/
theorem actLeft_comp {A B : Type*} (f f' : A → A) :
    actLeft (B := B) f ∘ actLeft f' = actLeft (f ∘ f') := rfl

/-- SUFFICIENCY: any finite word in open-factor generators commutes with every gauge
transformation.  The assembled transfer operator of a vertex whose generators all obey
decoration locality is therefore fully gauge invariant. -/
theorem assembled_transfer_gauge_commutes {A B G : Type*}
    (gens : List (A → A)) (U : G → B → B) (g : G) :
    (gens.map (fun f => actLeft (B := B) f)).foldr (· ∘ ·) id ∘ gaugeAction U g
      = gaugeAction U g ∘ (gens.map (fun f => actLeft (B := B) f)).foldr (· ∘ ·) id := by
  induction gens with
  | nil => rfl
  | cons f rest ih =>
      simp only [List.map_cons, List.foldr_cons]
      calc (actLeft (B := B) f ∘ (rest.map (fun f => actLeft (B := B) f)).foldr (· ∘ ·) id) ∘ gaugeAction U g
          = actLeft (B := B) f ∘ ((rest.map (fun f => actLeft (B := B) f)).foldr (· ∘ ·) id ∘ gaugeAction U g) := rfl
        _ = actLeft (B := B) f ∘ (gaugeAction U g ∘ (rest.map (fun f => actLeft (B := B) f)).foldr (· ∘ ·) id) := by rw [ih]
        _ = (actLeft (B := B) f ∘ gaugeAction U g) ∘ (rest.map (fun f => actLeft (B := B) f)).foldr (· ∘ ·) id := rfl
        _ = (gaugeAction U g ∘ actLeft (B := B) f) ∘ (rest.map (fun f => actLeft (B := B) f)).foldr (· ∘ ·) id := by
              rw [fullGaugeAction_commutes f U g]

end EntropicEFT.Gauge
