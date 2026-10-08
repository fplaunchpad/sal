-- Appended to each generated trial, after its imports and case definitions.
open Lean Elab Command in
elab "audit_vc " n:ident : command => do
  let root ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let env ← getEnv
  let axioms ← liftCoreM <| Lean.collectAxioms root
  logInfo m!"VC_AXIOMS {axioms}"
  -- Direct proof references distinguish supplied hints from theorem constants
  -- reached only through proposition definitions and generated instances.
  if let some (.thmInfo info) := env.find? root then
    for dependency in info.value.getUsedConstants.toList do
      if dependency.toString.startsWith "Sal." then
        logInfo m!"VC_DIRECT {dependency}"
  let mut seen : NameSet := {}
  let mut pending := [root]
  while !pending.isEmpty do
    let current := pending.head!
    pending := pending.tail!
    unless seen.contains current do
      seen := seen.insert current
      if let some info := env.find? current then
        if current.toString.startsWith "Sal." && (match info with | .thmInfo _ => true | _ => false) then
          logInfo m!"VC_DEP {current}"
        if (current.toString.startsWith "NeemExpansion." ||
            current.toString.startsWith "EfficientReplayAdapter." ||
            current.toString.startsWith "CausalEventClassification.") && (match info with | .thmInfo _ => true | _ => false) then
          logInfo m!"VC_EXP_DEP {current}"
        pending := info.getUsedConstantsAsSet.toList ++ pending
  logInfo "VC_AUDIT_COMPLETE"
