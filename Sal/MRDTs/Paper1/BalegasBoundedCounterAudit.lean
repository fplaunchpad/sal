import Sal.MRDTs.Paper1.BalegasBoundedCounterGlobal
import Sal.MRDTs.Instances.BalegasBoundedCounterSPOT

/-! Audit the source-faithful bounded counter independently of the rival
candidate. Client correctness, every stored version's safety, and safety of
the global event union must all consume the five merge VCs and their finite
metadata induction. The global theorem must also derive event finiteness
from execution rather than expose it as a premise.
-/
open Lean Elab Command in
elab "audit_balegas_counter" : command => do
  let env ← getEnv
  let roots := [
    ``Sal.MRDTs.Paper1.BalegasBoundedCounterEvent.certifiedV,
    ``Sal.MRDTs.Paper1.BalegasBoundedCounterEvent.versions_safeV,
    ``Sal.MRDTs.Paper1.BalegasBoundedCounterEvent.global_boundV]
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
    unless seen.contains ``Sal.MRDTs.Paper1.BalegasBoundedCounterVC.fiveVC &&
        seen.contains ``Sal.MRDTs.Paper1.ConcreteMRDT.Raw.join_at_sizes do
      throwError "{root} does not consume the published counter's five VCs and merge induction"
    if root == ``Sal.MRDTs.Paper1.BalegasBoundedCounterEvent.global_boundV then
      unless seen.contains ``Sal.MRDTs.MintCertifiedReachV.events_finite do
        throwError "Global bounded-counter safety does not derive event finiteness from execution"
  let prefixes := ["Sal.MRDTs.Instances.BalegasBoundedCounter.",
    "Sal.MRDTs.Paper1.BalegasBoundedCounterEvent.",
    "Sal.MRDTs.Paper1.BalegasBoundedCounterVC."]
  let mut count := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (fun p => p.isPrefixOf name.toString) then
      let axioms ← liftCoreM <| Lean.collectAxioms name
      for ax in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unexpected axiom in {name}: {ax}"
      count := count + 1
  let finiteAxioms ← liftCoreM <| Lean.collectAxioms
    ``Sal.MRDTs.MintCertifiedReachV.events_finite
  for ax in finiteAxioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom in global event finiteness: {ax}"
  logInfo m!"Balegas counter audit passed: client correctness, local-version safety and global-union bound consume five VCs and merge induction; {count} declarations use standard logical axioms only."

audit_balegas_counter
