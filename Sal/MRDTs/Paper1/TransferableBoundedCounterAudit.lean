import Sal.MRDTs.Paper1.TransferableBoundedCounterCorrectedBudget
import Sal.MRDTs.Paper1.TransferableBoundedCounterEvent
import Sal.MRDTs.Instances.TransferableBoundedCounterCorrectedSPOT

/-! Audit the additional candidate separately from the original 23 cases.
Its public correctness and budget roots must consume the five merge VCs.
Source-model obstructions are not claims about every transferable counter. -/
open Lean Elab Command in
elab "audit_transferable_counter" : command => do
  let env ← getEnv
  let roots := [
    ``Sal.MRDTs.Paper1.TransferableBoundedCounterCorrectedEvent.certifiedV,
    ``Sal.MRDTs.Paper1.TransferableBoundedCounterCorrectedEvent.versions_budgetV,
    ``Sal.MRDTs.Paper1.TransferableBoundedCounterCorrectedEvent.versions_allocations_nonnegativeV]
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
    unless seen.contains ``Sal.MRDTs.Instances.TransferableBoundedCounter.Corrected.fiveVC &&
        seen.contains ``Sal.MRDTs.Paper1.ConcreteMRDT.Raw.join_at_sizes do
      throwError "{root} does not consume the candidate five VCs and merge induction"
  let prefixes := ["Sal.MRDTs.Instances.TransferableBoundedCounter.",
    "Sal.MRDTs.Paper1.TransferableBoundedCounterEvent.",
    "Sal.MRDTs.Paper1.TransferableBoundedCounterCorrectedEvent."]
  let mut count := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (fun p => p.isPrefixOf name.toString) then
      let axioms ← liftCoreM <| Lean.collectAxioms name
      for ax in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unexpected axiom in {name}: {ax}"
      count := count + 1
  logInfo m!"Transferable-counter candidate audit passed: correctness and budget roots consume five VCs; {count} declarations use standard logical axioms only."

audit_transferable_counter
