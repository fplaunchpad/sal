import Sal.MRDTs.Paper1.AddWinsPriorityQueueFullCertificate
import Sal.MRDTs.Instances.AddWinsPriorityQueueFullSPOT
import Sal.MRDTs.Instances.AddWinsPriorityQueueReadSide

/-! Gate both certificate ancestry and every new declaration's logical axioms. -/
open Lean Elab Command in
elab "audit_add_wins_priority_queue" : command => do
  let env ← getEnv
  for root in [``Sal.MRDTs.Paper1.AddWinsPriorityQueue.certifiedV,
      ``Sal.MRDTs.Paper1.AddWinsPriorityQueue.executionsV,
      ``Sal.MRDTs.Paper1.AddWinsPriorityQueue.Full.certifiedV,
      ``Sal.MRDTs.Paper1.AddWinsPriorityQueue.Full.executionsV] do
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
    let bridge := if root.toString.startsWith "Sal.MRDTs.Paper1.AddWinsPriorityQueue.Full." then
      ``Sal.MRDTs.Paper1.AddWinsPriorityQueue.Full.historySound
      else ``Sal.MRDTs.Paper1.AddWinsPriorityQueue.historySound
    unless seen.contains ``Sal.MRDTs.Paper1.AddWinsPriorityQueue.fiveVC &&
        seen.contains ``Sal.MRDTs.Paper1.ConcreteMRDT.Raw.join_at_sizes &&
        seen.contains bridge do
      throwError "{root} must consume source five VCs, finite merge induction and independent priority bridge"
    if root.toString.startsWith "Sal.MRDTs.Paper1.AddWinsPriorityQueue.Full." then
      unless seen.contains ``Sal.MRDTs.Paper1.AddWinsPriorityQueue.Full.fiveVC &&
          seen.contains ``Sal.MRDTs.Paper1.Automation.QueryLift.transport do
        throwError "{root} must transport the same operational five VCs through the complete query interface"
  let prefixes := ["Sal.MRDTs.Instances.AddWinsPriorityQueue.",
    "Sal.MRDTs.Instances.AddWinsPriorityQueueSPOT.", "Sal.MRDTs.Paper1.AddWinsPriorityQueue."]
  let mut count := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (fun p => p.isPrefixOf name.toString ||
        (name.toString.startsWith "_private.Sal." && (name.toString.splitOn p).length > 1)) then
      let axioms ← liftCoreM <| Lean.collectAxioms name
      for ax in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unexpected axiom in {name}: {ax}"
      count := count + 1
  logInfo m!"Priority queue audit passed: certificates consume five VCs, merge induction and independent full query/client bridge; {count} declarations use standard logical axioms only."

audit_add_wins_priority_queue
