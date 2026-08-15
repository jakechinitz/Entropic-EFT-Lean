import EntropicEFT.Information.Renewal

/-!
# EntropicEFT.Quantum.Replacement

LOCAL CONTRACT
* Manuscript: Section 3.3, 22; Appendix H.8, H.11.
* Purpose: isolate the exact quantum-channel statements needed by the theory.
* Matrix algebra is explicit; complete positivity/Stinespring uniqueness is packaged as
  an external mathematical theorem interface until fully mechanized.
* Position and retained marked fiber are NOT part of the replaceable register.
-/

namespace EntropicEFT.Quantum

variable {n : ℕ}
abbrev Op (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- Finite matrix trace. -/
noncomputable def tr (X : Op n) : ℂ := Matrix.trace X

/-- Replacement map `X -> Tr(X) rho`. -/
noncomputable def replacement (rho X : Op n) : Op n := (tr X) • rho

theorem replacement_depends_only_on_trace (rho X Y : Op n) (h : tr X = tr Y) :
    replacement rho X = replacement rho Y := by
  simp [replacement, h]

/-- Heisenberg dual identity and CPTP status, to be discharged by generic finite-dimensional
quantum-channel mathematics rather than assumed physically. -/
structure ReplacementChannelMath (rho : Op n) where
  positiveRho : Prop
  traceOne : tr rho = 1
  completelyPositive : Prop
  tracePreserving : Prop
  dualIdentity : Prop
  referenceDecouplingUnique : Prop

/-- Environment-record overlap controls a retained off-diagonal. -/
noncomputable def coherenceFactor (ex ey : Fin n → ℂ) : ℂ :=
  ∑ i, star (ey i) * ex i

/-- Exact abstract form of the complementary-record theorem. -/
structure RecordOverlapTheorem where
  initialOffDiagonal : ℂ
  overlap : ℂ
  finalOffDiagonal : ℂ
  identity : finalOffDiagonal = overlap * initialOffDiagonal

/-- Free transport condition: discarded renewal output may not carry a position address. -/
structure NoWhichPathCondition where
  branchIndependentDiscardedRecord : Prop
  markedFiberRetainedCoherently : Prop

end EntropicEFT.Quantum
