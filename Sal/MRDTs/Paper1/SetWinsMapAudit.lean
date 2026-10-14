import Sal.MRDTs.Paper1.SetWinsMapCertificate
import Sal.MRDTs.Instances.SetWinsMapSPOT
import Sal.MRDTs.Paper1.SetWinsMapReadSide

/-! Gate both certificate ancestry and every new declaration's logical axioms. -/
open Lean Elab Command in
elab "audit_set_wins_map" : command => do
  let env ← getEnv
  for root in [``Sal.MRDTs.Paper1.SetWinsMap.certifiedV,
      ``Sal.MRDTs.Paper1.SetWinsMap.executionsV] do
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
    unless seen.contains ``Sal.MRDTs.Paper1.SetWinsMap.fiveVC &&
        seen.contains ``Sal.MRDTs.Paper1.ConcreteMRDT.Raw.join_at_sizes &&
        seen.contains ``Sal.MRDTs.Paper1.SetWinsMap.historySound do
      throwError "{root} must consume source five VCs, finite merge induction and natural bridge"
  let prefixes := ["Sal.MRDTs.Instances.SetWinsMap.",
    "Sal.MRDTs.Instances.SetWinsMapSPOT.", "Sal.MRDTs.Paper1.SetWinsMap."]
  let mut count := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (fun p => p.isPrefixOf name.toString ||
        (name.toString.startsWith "_private.Sal." && (name.toString.splitOn p).length > 1)) then
      let axioms ← liftCoreM <| Lean.collectAxioms name
      for ax in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unexpected axiom in {name}: {ax}"
      count := count + 1
  logInfo m!"Set-wins map audit passed: certificates consume five VCs, merge induction and natural multimap bridge; {count} declarations use standard logical axioms only."

audit_set_wins_map
