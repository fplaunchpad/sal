import Sal.MRDTs.Paper1.PriorityQueueSameRecordCertificate
import Sal.MRDTs.Instances.PriorityQueueSameRecordSPOT

/-! Verify the public certificate's actual five-VC and independent-history
ancestry, and reject any nonstandard axiom in the repaired queue modules. -/
open Lean Elab Command in
elab "audit_same_record_priority_queue" : command => do
  let env ← getEnv
  for root in [``Sal.MRDTs.Paper1.PriorityQueueSameRecord.certified,
      ``Sal.MRDTs.Paper1.PriorityQueueSameRecord.certifiedV,
      ``Sal.MRDTs.Paper1.PriorityQueueSameRecord.executions,
      ``Sal.MRDTs.Paper1.PriorityQueueSameRecord.executionsV] do
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
    for needed in [``Sal.MRDTs.Paper1.PriorityQueueSameRecord.fiveVC,
        ``Sal.MRDTs.Paper1.ConcreteMRDT.Raw.join_at_sizes,
        ``Sal.MRDTs.Paper1.PriorityQueueSameRecord.historyAdequacy,
        ``Sal.MRDTs.Paper1.PriorityQueueSameRecord.present_replay,
        ``Sal.MRDTs.Paper1.PriorityQueueSameRecord.absent_replay,
        ``Sal.MRDTs.Paper1.PriorityQueueSameRecord.honest_increment_birth,
        ``Sal.MRDTs.Paper1.PriorityQueueSameRecord.honest_remove_birth,
        ``Sal.MRDTs.Paper1.PriorityQueueSameRecord.acquired_fold,
        ``Sal.MRDTs.Paper1.PriorityQueueSameRecord.assemble_key_histories] do
      unless seen.contains needed do
        throwError "{root} must consume {needed}"
  let prefixes := ["Sal.MRDTs.Instances.PriorityQueueSameRecord.",
    "Sal.MRDTs.Paper1.PriorityQueueSameRecord.",
    "Sal.MRDTs.Instances.PublishedAddWinsPriorityQueue."]
  let mut count := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (fun p => p.isPrefixOf name.toString ||
        (name.toString.startsWith "_private.Sal." && (name.toString.splitOn p).length > 1)) then
      let axioms ← liftCoreM <| Lean.collectAxioms name
      for ax in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unexpected axiom in {name}: {ax}"
      count := count + 1
  logInfo m!"Same-record priority queue audit passed: five VCs, shared finite Join induction, exact issuance provenance, ordinary present/absent replay and all-key query composition; {count} declarations use standard logical axioms only."

audit_same_record_priority_queue
