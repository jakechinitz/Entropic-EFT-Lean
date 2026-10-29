import Compatibility
open Lean Elab Command

/-- Audit every theorem declared in modules under the given prefix: report the count and any theorem
that depends on an axiom outside {propext, Classical.choice, Quot.sound}. -/
elab "#audit_axioms " pre:ident : command => do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut total := 0
  let mut bad : Array (Name × List Name) := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless pre.getId.isPrefixOf mod do continue
    unless ci matches .thmInfo _ do continue
    if n.isInternal then continue
    total := total + 1
    let axs ← liftCoreM (collectAxioms n)
    let extra := axs.toList.filter (fun a => !std.contains a)
    unless extra.isEmpty do bad := bad.push (n, extra)
  logInfo m!"{pre.getId}: {total} theorems; {bad.size} with nonstandard axioms"
  for (n, e) in bad.toList.take 60 do
    logInfo m!"  {n}: {e}"

/-- Count the `Entropic` modules in the import closure of the standalone target. -/
elab "#closure_size" : command => do
  let env ← getEnv
  let mods := env.header.moduleNames.filter (fun m => (`Entropic).isPrefixOf m)
  logInfo m!"Compatibility target imports {mods.size} Entropic modules"

#closure_size
#audit_axioms Entropic.Compatibility
#audit_axioms Entropic.Completion
#print axioms Entropic.Compatibility.effective_assumptions_compatible
#print axioms Entropic.Completion.spatial_history_assumptions_compatible
#print axioms Entropic.Completion.global_effective_assumptions_compatible
#print axioms Entropic.Completion.GlobalModel.positive_fields
#print axioms Entropic.Completion.GlobalModel.selected_depletion_initial_interval
#print axioms Entropic.Completion.InfiniteHistory.cylinder_law
#print axioms Entropic.Completion.Entropy.seven_channel_determinant
