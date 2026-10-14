import Sal.MRDTs.Paper1.SplitCertificates

/-! Production dependency audit for the split metatheory and all 21 named
cases in the automation inventory. The last case is FugueMax's scoped algebraic
certificate; the audit does not promote it to a sequential/RA certificate. -/
open Lean Elab Command in
elab "audit_split_policy" : command => do
  let env ← getEnv
  let roots := [
    ``Sal.MRDTs.Paper1.SplitCertificates.gsetExecutionsV,
    ``Sal.MRDTs.Paper1.SplitCertificates.finiteAddExecutionsV,
    ``Sal.MRDTs.Paper1.SplitCertificates.counterExecutionsV,
    ``Sal.MRDTs.Paper1.SplitCertificates.iocExecutionsV,
    ``Sal.MRDTs.Paper1.SplitCertificates.pnExecutionsV,
    ``Sal.MRDTs.Paper1.SplitCertificates.booleanSetExecutionsV,
    ``Sal.MRDTs.Paper1.SplitCertificates.booleanMapExecutionsV,
    ``Sal.MRDTs.Paper1.SplitCertificates.lwwExecutionsV,
    ``Sal.MRDTs.Paper1.SplitCertificates.rgaExecutionsV,
    ``Sal.MRDTs.Paper1.SplitCertificates.treeExecutionsV,
    ``Sal.MRDTs.Paper1.SplitCertificates.aegisExecutionsV,
    ``Sal.MRDTs.Paper1.SplitCertificates.ordinaryORSetExecutionsV,
    ``Sal.MRDTs.Paper1.SplitCertificates.efficientORSetExecutionsV,
    ``Sal.MRDTs.Paper1.SplitCertificates.mvr,
    ``Sal.MRDTs.Paper1.SplitCertificates.embedded,
    ``Sal.MRDTs.Paper1.SplitCertificates.sided,
    ``Sal.MRDTs.Paper1.SplitCertificates.peritext,
    ``Sal.MRDTs.Paper1.SplitCertificates.core,
    ``Sal.MRDTs.Paper1.SplitCertificates.rich,
    ``Sal.MRDTs.Paper1.SplitCertificates.anchoredQueue,
    ``Sal.MRDTs.Paper1.SplitCertificates.fugue]
  unless roots.length == 21 do
    throwError "Incomplete split-policy case inventory"
  for root in roots do
    unless env.contains root do
      throwError "Missing split-policy certificate: {root}"
    let axioms ← liftCoreM <| Lean.collectAxioms root
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  -- Inspect proof dependencies, not only imported declarations. Each root
  -- must retain actual VC verification, the strict-size merge induction, and
  -- a split-policy conversion/constructor in its proof or certificate type.
  for root in roots do
    let mut seen : NameSet := {}
    let mut pending := [root]
    while !pending.isEmpty do
      let current := pending.head!
      pending := pending.tail!
      unless seen.contains current do
        seen := seen.insert current
        if current.toString.startsWith "Sal." || current.toString.startsWith "_private.Sal." then
          if let some info := env.find? current then
            pending := info.getUsedConstantsAsSet.toList ++ pending
    unless seen.contains ``Sal.MRDTs.Paper1.Automation.CommonVerification.verify do
      throwError "{root} lost actual five-VC verification"
    unless seen.contains ``Sal.MRDTs.Paper1.ConcreteMRDT.Raw.join_at_sizes do
      throwError "{root} lost the five-VC merge induction"
    unless seen.toList.any (fun n => n.toString.startsWith "Sal.MRDTs.Paper1.SplitPolicy.") do
      throwError "{root} lost its split-law dependency"
  let prefixes := ["Sal.MRDTs.Paper1.SplitPolicy.",
    "Sal.MRDTs.Paper1.SplitCertificates.",
    "Sal.MRDTs.Paper1.SelfCommutationInstances."]
  let mut count := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (fun p => p.isPrefixOf name.toString) then
      let axioms ← liftCoreM <| Lean.collectAxioms name
      for ax in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unexpected axiom in {name}: {ax}"
      count := count + 1
  unless count > 100 do
    throwError "Incomplete split-policy metatheory audit: {count} declarations"
  logInfo m!"Split-policy dependency audit passed: all 21 cases retain five-VC verification, merge induction and split laws; {count} declarations use standard logical axioms only."

audit_split_policy
