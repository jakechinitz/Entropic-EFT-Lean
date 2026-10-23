import Entropic
import Entropic.EFT
open Lean Elab Command

/-- Audit every theorem declared in modules under the given prefixes: report the count and
any theorem that depends on an axiom outside {propext, Classical.choice, Quot.sound}. -/
elab "#audit_axioms " pre:ident : command => do
  let env ← getEnv
  let some _ := env.header.moduleNames.find? (fun _ => true) | pure ()
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

#audit_axioms Entropic
#audit_axioms Entropic.EFT
