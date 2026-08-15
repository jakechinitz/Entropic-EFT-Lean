import EntropicEFT

/-!
# Axiom footprint audit

This file is not part of the `EntropicEFT` library target. It is run in CI
(`lake env lean Scripts/AxiomAudit.lean`) and its output is checked by
`tools/check_axioms.py`, which fails the build if any headline theorem depends
on an axiom outside the declared trust base:

* `propext`, `Classical.choice`, `Quot.sound` — standard Lean/Mathlib foundations;
* `Lean.ofReduceBool` — the `native_decide` certificate, i.e. compiled evaluation
  of a finite enumeration rather than kernel reduction.

Anything else — in particular `sorryAx`, which a `sorry` would introduce — is a
CI failure. This is the machine-checked form of the trust-base paragraph in the
README: readers do not have to take the claim on anyone's word.
-/

-- Foundations-only results (no enumeration certificate expected).
#print axioms EntropicEFT.Marked.corrected_amplitude_factorization
#print axioms EntropicEFT.Marked.singleStrandZeroPointEnergy_eq_three_halves
#print axioms EntropicEFT.Gauge.frame_realizes_closure
#print axioms EntropicEFT.Gauge.fullGaugeAction_commutes
#print axioms EntropicEFT.Gauge.assembled_transfer_gauge_commutes
#print axioms EntropicEFT.Gauge.leftObservable_gaugeInvariant
#print axioms EntropicEFT.Structure.closureVec_bcc
#print axioms EntropicEFT.Structure.stationarity_bracketing

-- Results that additionally consume the enumerated `native_decide` certificates.
#print axioms EntropicEFT.UV.boundaryStates_card
#print axioms EntropicEFT.UV.boundaryStates_nonempty
#print axioms EntropicEFT.UV.Z_pos
#print axioms EntropicEFT.UV.meanK2_bounds
#print axioms EntropicEFT.UV.stationary_root_exists
#print axioms EntropicEFT.UV.stationary_root_unique
#print axioms EntropicEFT.Gauge.sameFactorGaussCasimir_noGo
#print axioms EntropicEFT.Gauge.spec_jointly_realizable
#print axioms EntropicEFT.Instantiation.premises_jointly_satisfiable
#print axioms EntropicEFT.Structure.universal_channel_sharing
#print axioms EntropicEFT.Structure.johnson_fibration
#print axioms EntropicEFT.Structure.unweighted_mean_exact
#print axioms EntropicEFT.Structure.three_halves_bridge
