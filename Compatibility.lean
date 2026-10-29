import Entropic.Compatibility.All
import Entropic.Completion.All

/-!
# Compatibility: standalone build target

`lake build Compatibility` builds only this module and the part of the `Entropic` library it imports.

* `Entropic.Compatibility.effective_assumptions_compatible : Nonempty EffectiveModel`: one structure carries
  the native closure root η and ε, the 1680-state Gibbs histories, a finite positive stock shared by
  reconstruction, redistribution and reciprocal Newton forces, and an explicit expanding homogeneous Einstein
  solution with positive energy transfer, tied to the finite model through one mass budget.
* `Entropic.Completion.spatial_history_assumptions_compatible`, `Entropic.Completion.global_effective_assumptions_compatible`:
  a common inhomogeneous clock/stock spacetime with positive baryons, donor and retained stock, one source clock,
  the native η and ε, unbounded future proper time, and (`Entropic.Completion.InfiniteHistory`) one probability
  space for all integer times with the native Gibbs marginals.

Scope: an effective subsystem. It is not compatibility of the full theory: the finite force system is not embedded
in the expanding metric, and the microscopic history-to-spacetime map, physical G matching and empirical
validation are not part of it. The Einstein tensor of the inhomogeneous metric is checked outside Lean.
`scripts/CompatibilityAudit.lean` audits every theorem in these modules.
-/
