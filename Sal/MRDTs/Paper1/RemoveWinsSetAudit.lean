import Sal.MRDTs.Paper1.RemoveWinsSetCertificate
import Sal.MRDTs.Instances.RemoveWinsSetSPOT

/-! Verify that the execution certificate actually consumes this source
algorithm's five VCs and the finite merge induction. Audit every declaration
in this port for nonstandard axioms, including private auxiliary lemmas. -/
open Lean Elab Command in
elab "audit_remove_wins_set" : command => do
  let env ← getEnv
  let roots := [``Sal.MRDTs.Paper1.RemoveWinsSet.certifiedV,
    ``Sal.MRDTs.Paper1.RemoveWinsSet.executions,
    ``Sal.MRDTs.Paper1.RemoveWinsSet.executionsV]
  for root in roots do
    let mut seen : NameSet := {}
    let mut pending := [root]
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      unless seen.contains name do
        seen := seen.insert name
        if name.toString.startsWith "Sal." || name.toString.startsWith "_private.Sal." then
          if let some info := env.find? name then
            pending := info.getUsedConstantsAsSet.toList ++ pending
    unless seen.contains ``Sal.MRDTs.Paper1.RemoveWinsSet.fiveVC &&
        seen.contains ``Sal.MRDTs.Paper1.ConcreteMRDT.Raw.join_at_sizes do
      throwError "{root} does not consume removal-tag five VCs and merge induction"
  let prefixes := ["Sal.MRDTs.Instances.RemoveWinsSet.",
    "Sal.MRDTs.Instances.RemoveWinsSetSPOT.","Sal.MRDTs.Paper1.RemoveWinsSet."]
  let mut count := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (fun p => p.isPrefixOf name.toString ||
        (name.toString.startsWith "_private.Sal." && (name.toString.splitOn p).length > 1)) then
      let axioms ← liftCoreM <| Lean.collectAxioms name
      for ax in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unexpected axiom in {name}: {ax}"
      count := count + 1
  logInfo m!"Remove-wins set audit passed: stored-version and both execution roots consume source five VCs and finite merge induction; {count} declarations use standard logical axioms only."

audit_remove_wins_set
