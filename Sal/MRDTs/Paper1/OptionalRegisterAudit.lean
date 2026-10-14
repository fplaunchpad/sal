import Sal.MRDTs.Paper1.OptionalRegisterCertificate
import Sal.MRDTs.Paper1.OptionalRegisterSourceValidity
import Sal.MRDTs.Paper1.OptionalRegisterSPOT

/-! Gate the optional-register execution roots on the supplied source's five
VCs, finite merge induction, repaired split policy and independent scalar
history bridge. Audit every new declaration, including private auxiliaries. -/
open Lean Elab Command in
elab "audit_optional_register" : command => do
  let env ← getEnv
  let roots := [``Sal.MRDTs.Paper1.OptionalRegister.certifiedV,
    ``Sal.MRDTs.Paper1.OptionalRegister.executions,
    ``Sal.MRDTs.Paper1.OptionalRegister.executionsV]
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
    unless seen.contains ``Sal.MRDTs.Paper1.OptionalRegister.fiveVC &&
        seen.contains ``Sal.MRDTs.Paper1.ConcreteMRDT.Raw.join_at_sizes &&
        seen.contains ``Sal.MRDTs.Paper1.OptionalRegister.splitLaws &&
        seen.contains ``Sal.MRDTs.Paper1.OptionalRegister.history_from_representation do
      throwError "{root} must consume source five VCs, finite merge induction, split laws and scalar history bridge"
  for root in [``Sal.MRDTs.Paper1.OptionalRegister.sourceWellFormed,
      ``Sal.MRDTs.Paper1.OptionalRegister.sourceWellFormedV] do
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
    unless seen.contains ``Sal.MRDTs.Paper1.OptionalRegister.fiveVC &&
        seen.contains ``Sal.MRDTs.Paper1.ConcreteMRDT.Raw.join_at_sizes &&
        seen.contains ``Sal.MRDTs.Paper1.OptionalRegister.positive_events do
      throwError "{root} must derive source refinement from five VCs and certified issuance"
  let prefixes := ["Sal.MRDTs.Instances.OptionalRegister.",
    "Sal.MRDTs.Paper1.OptionalRegister.","Sal.MRDTs.Paper1.OptionalRegisterCounts.",
    "Sal.MRDTs.Paper1.OptionalRegisterSPOT."]
  let mut count := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (fun p => p.isPrefixOf name.toString ||
        (name.toString.startsWith "_private.Sal." && (name.toString.splitOn p).length > 1)) then
      let axioms ← liftCoreM <| Lean.collectAxioms name
      for ax in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unexpected axiom in {name}: {ax}"
      count := count + 1
  logInfo m!"Optional-register audit passed: stored-version and both execution roots consume source five VCs, finite merge induction, split policy and independent scalar history bridge; source refinement derives from certified issuance; {count} declarations use standard logical axioms only."

audit_optional_register
