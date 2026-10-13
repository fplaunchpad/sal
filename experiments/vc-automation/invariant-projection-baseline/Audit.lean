import Sal.MRDTs.Paper1.Ledger

open Lean in
partial def auditVerifierApps (verifier : Name) : Expr → List Expr
  | e@(.app f a) =>
    if e.getAppFn.isConstOf verifier then
      e :: e.getAppArgs.toList.flatMap (auditVerifierApps verifier)
    else auditVerifierApps verifier f ++ auditVerifierApps verifier a
  | .lam _ t b _ | .forallE _ t b _ => auditVerifierApps verifier t ++ auditVerifierApps verifier b
  | .letE _ t v b _ => auditVerifierApps verifier t ++ auditVerifierApps verifier v ++ auditVerifierApps verifier b
  | .mdata _ e | .proj _ _ e => auditVerifierApps verifier e
  | _ => []

open Lean Elab Command in
elab "audit_verifier_traversal_control" : command => do
  let verifier := ``Sal.MRDTs.Paper1.Automation.CommonVerification.verify
  let first := mkApp (mkConst verifier) (mkConst `FIRST_VC_INPUT)
  let second := mkApp (mkConst verifier) (mkConst `SECOND_VC_INPUT)
  let tree := mkApp2 (mkConst ``And.intro) first second
  let apps := auditVerifierApps verifier tree
  unless apps.length == 2 && apps[0]!.getUsedConstants.contains `FIRST_VC_INPUT &&
      apps[1]!.getUsedConstants.contains `SECOND_VC_INPUT do
    throwError "VC traversal dropped one of two submitted verification applications"
  unless (auditVerifierApps verifier (mkConst ``True.intro)).isEmpty do
    throwError "VC traversal invented an absent verification application"
  logInfo "PROD_VC_TRAVERSAL_CONTROL pass: both applications retained; absent application excluded"

open Lean Elab Command in
elab "audit_production " n:ident : command => do
  let root ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let env ← getEnv
  let axioms ← liftCoreM <| Lean.collectAxioms root
  logInfo m!"PROD_AXIOMS {root} {axioms}"
  let mut seen : NameSet := {}
  let mut pending := [root]
  while !pending.isEmpty do
    let current := pending.head!
    pending := pending.tail!
    unless seen.contains current do
      seen := seen.insert current
      if let some info := env.find? current then
        if current.toString.startsWith "Sal." || current.toString.startsWith "_private.Sal." || current.toString.startsWith "NeemExpansion." ||
            current.toString.startsWith "EfficientReplayAdapter." || current.toString.startsWith "CausalEventClassification." then
          logInfo m!"PROD_DEP {root} {current}"
          if let some moduleIdx := env.getModuleIdxFor? current then
            if let some ranges ← findDeclarationRanges? current then
              let kind := match info with | .thmInfo _ => "theorem" | _ => "definition"
              logInfo m!"PROD_SOURCE {current} {env.header.moduleNames[moduleIdx.toNat]!} {ranges.range.pos.line} {ranges.range.endPos.line} {kind}"
        pending := info.getUsedConstantsAsSet.toList ++ pending

  logInfo m!"PROD_COMPLETE {root}"

open Lean Elab Command in
elab "audit_production_vc_evidence " n:ident : command => do
  let root ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let env ← getEnv
  let verifier := ``Sal.MRDTs.Paper1.Automation.CommonVerification.verify
  let mut visited : NameSet := {}
  let mut pending := [root]
  let mut evidence : NameSet := {}
  while !pending.isEmpty do
    let current := pending.head!
    pending := pending.tail!
    unless visited.contains current do
      visited := visited.insert current
      if let some info := env.find? current then
        let value := match info with
          | .thmInfo i => some i.value
          | .defnInfo i => some i.value
          | _ => none
        let applications := value.toList.flatMap (auditVerifierApps verifier)
        if !applications.isEmpty then
          logInfo m!"PROD_VC_APP {root} {current}"
          for proof in applications do
            for dependency in proof.getUsedConstants do
              evidence := evidence.insert dependency
        else
          pending := info.getUsedConstantsAsSet.toList ++ pending
  if evidence.isEmpty then
    throwError "{root} has no actual CommonVerification.verify application"
  visited := {}
  pending := evidence.toList
  while !pending.isEmpty do
    let current := pending.head!
    pending := pending.tail!
    unless visited.contains current do
      visited := visited.insert current
      if let some info := env.find? current then
        if current.toString.startsWith "Sal." || current.toString.startsWith "_private.Sal." then
          logInfo m!"PROD_VC_DEP {root} {current}"
        pending := info.getUsedConstantsAsSet.toList ++ pending
  logInfo m!"PROD_VC_COMPLETE {root}"

audit_production Sal.MRDTs.Paper1.ConcreteMRDT.GuardedPorts.Tree.originLegal
audit_production Sal.MRDTs.Paper1.ConcreteMRDT.GuardedPorts.Tree.history
audit_production Sal.MRDTs.Paper1.ConcreteMRDT.GuardedPorts.Tree.conditions
audit_production Sal.MRDTs.Paper1.ConcreteMRDT.GuardedPorts.Tree.executions
audit_production Sal.MRDTs.Paper1.ConcreteMRDT.GuardedPorts.Tree.executionsV
audit_production Sal.MRDTs.Paper1.ConcreteMRDT.GuardedPorts.Sheet.originLegal
audit_production Sal.MRDTs.Paper1.ConcreteMRDT.GuardedPorts.Sheet.history
audit_production Sal.MRDTs.Paper1.ConcreteMRDT.GuardedPorts.Sheet.conditions
audit_production Sal.MRDTs.Paper1.ConcreteMRDT.GuardedPorts.Sheet.executions
audit_production Sal.MRDTs.Paper1.ConcreteMRDT.GuardedPorts.Sheet.executionsV
audit_production Sal.MRDTs.Instances.TreeMove.sequentialSound
audit_production Sal.MRDTs.Instances.AegisSheet.Sequential.causalOriginSequentialSound
audit_production Sal.MRDTs.Paper1.TreeMoveEvent.legal_prefix
audit_production Sal.MRDTs.Paper1.AegisSheetEvent.legal_prefix
audit_production Sal.MRDTs.Paper1.ORSet.EventSpec.foldHistorySound
audit_production Sal.MRDTs.Paper1.ORSet.EventSpec.commutationCompatibility
