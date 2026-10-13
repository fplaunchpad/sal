import Sal.MRDTs.Paper1.EnableWinsFlagCertificate
import Sal.MRDTs.Paper1.DisableWinsFlagCertificate
import Sal.MRDTs.Instances.EnableWinsFlagSPOT
import Sal.MRDTs.Paper1.DisableWinsFlagSPOT

/-! The two Neem flag certificates must depend on the corrected row
algorithm's five VCs and the common finite metadata induction. Counterfactual
scalar controls remain separate from the implementation under certification.
-/
open Lean Elab Command in
elab "audit_neem_flags" : command => do
  let env ← getEnv
  let roots := [``Sal.MRDTs.Paper1.EnableWinsFlagEvent.certifiedV,
    ``Sal.MRDTs.Paper1.DisableWinsFlagEvent.certifiedV]
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
    unless seen.contains ``Sal.MRDTs.Paper1.NeemFlagVC.fiveVC &&
        seen.contains ``Sal.MRDTs.Paper1.ConcreteMRDT.Raw.join_at_sizes do
      throwError "{root} does not consume the corrected flag's five VCs and merge induction"
  let prefixes := ["Sal.MRDTs.Instances.NeemFlag.",
    "Sal.MRDTs.Instances.EnableWinsFlag.", "Sal.MRDTs.Instances.EnableWinsFlagSPOT.", "Sal.MRDTs.Instances.DisableWinsFlag.",
    "Sal.MRDTs.Paper1.EnableWinsFlagEvent.", "Sal.MRDTs.Paper1.DisableWinsFlagEvent.",
    "Sal.MRDTs.Paper1.DisableWinsFlagSPOT.", "Sal.MRDTs.Paper1.NeemFlagEvent.",
    "Sal.MRDTs.Paper1.NeemFlagReplay.", "Sal.MRDTs.Paper1.NeemFlagAlgebra.",
    "Sal.MRDTs.Paper1.NeemFlagCounts.", "Sal.MRDTs.Paper1.NeemFlagCausal.",
    "Sal.MRDTs.Paper1.NeemFlagVC."]
  let mut count := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (fun p => p.isPrefixOf name.toString ||
        (name.toString.startsWith "_private.Sal." && (name.toString.splitOn p).length > 1)) then
      let axioms ← liftCoreM <| Lean.collectAxioms name
      for ax in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unexpected axiom in {name}: {ax}"
      count := count + 1
  logInfo m!"Neem flag audit passed: both certificates consume shared five VCs and merge induction; {count} declarations use standard logical axioms only."

audit_neem_flags
