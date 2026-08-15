import EntropicEFT.Quantum.Replacement

/-!
# EntropicEFT.Quantum.Histories

LOCAL CONTRACT
* Manuscript: Section 3.3, 22; Appendix G.
* Encodes the operational decoherent-histories layer separately from the Many-Pasts ontology.
* No theorem here derives Hilbert-space quantum kinematics from the substrate.
-/

namespace EntropicEFT.Quantum

/-- Minimal operational inputs imported from standard quantum mechanics. -/
structure QuantumKinematics where
  hilbertSpace : Type
  unitaryDynamics : Prop
  initialState : Prop
  recordProjectors : Prop

/-- Abstract class-operator/decoherence-functional package. -/
structure DecoherentHistoryFamily where
  History : Type
  Record : Type
  decoherenceFunctional : History → History → ℂ
  diagonalNonnegative : Prop
  offDiagonalVanishes : Prop
  probabilitySumRules : Prop
  recordConditioningValid : Prop

/-- Gleason is treated as external mathematics under its own hypotheses. -/
structure GleasonRecordMeasure where
  dimensionGreaterThanTwo : Prop
  normalized : Prop
  noncontextual : Prop
  additive : Prop
  bornForm : Prop

/-- Operational no-signaling theorem interface for local trace-preserving instruments. -/
structure NoSignalingMath where
  localMarginalIndependentOfRemoteSetting : Prop

/-- Ontological Many-Pasts layer; distinct from the operational Born measure. -/
structure ManyPastsReading where
  realizedPresentIncludesRecords : Prop
  compatiblePastsConditionedOnPresent : Prop
  recordErasureCoarseGrainsMeasure : Prop
  noFutureToPastForce : Prop

end EntropicEFT.Quantum
