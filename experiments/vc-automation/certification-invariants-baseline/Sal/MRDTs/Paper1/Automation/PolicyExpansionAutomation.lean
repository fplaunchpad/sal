import Sal.MRDTs.Paper1.Automation.InductivePolicy
import Sal.MRDTs.Paper1.Automation.PolicyExpansionRules
import Sal.MRDTs.Paper1.Automation.CausalCoverage
import Sal.MRDTs.Paper1.Automation.SharedExpansion

/-! Only generic equation definitions belong to this registry. Instances
register raw implementation definitions locally; no datatype proof is selected. -/
open Sal.MRDTs.Paper1.Automation
attribute [policy_expansion_simps]
  Signature.distinct Signature.comm Signature.CausalEquation
  Signature.LocalEquation Signature.FreshEquation Signature.Commutes
  Signature.commutes Signature.KernelStable Signature.ConditionalBase

/-- Convert finite-set equality assumptions into membership formulas before
solving the finite Boolean equations. Constructor splitting stays explicit. -/
macro "policy_finite" : tactic => `(tactic| (
  try simp only [policy_expansion_simps] at *
  all_goals ext p
  all_goals try simp only [Finset.ext_iff] at *
  all_goals try simp_all [policy_expansion_simps]
  all_goals grind (splits := 20) only))

namespace Sal.MRDTs.Paper1.Automation.PolicyFinite
open Lean Meta Elab Tactic

/-- Discover event payload types from the framework's `Nat × Nat × AppOp`
carrier, rather than from datatype or theorem names. -/
private def eventTypes (goal : MVarId) : MetaM (Array Expr) := goal.withContext do
  let mut result := #[]
  for decl in (← getLCtx) do
    unless decl.isImplementationDetail do
      let type ← whnf decl.type
      if type.isAppOfArity ``Prod 2 then
        let args := type.getAppArgs
        if (← whnf args[0]!).isConstOf ``Nat then
          let rest ← whnf args[1]!
          if rest.isAppOfArity ``Prod 2 && (← whnf rest.getAppArgs[0]!).isConstOf ``Nat then
            result := result.push (← whnf rest.getAppArgs[1]!)
  return result

private partial def splitEvents (goal : MVarId) (payloads : Array Expr) : MetaM (Array MVarId) :=
  goal.withContext do
    for decl in (← getLCtx) do
      unless decl.isImplementationDetail do
        let type ← whnf decl.type
        let product := type.isAppOfArity ``Prod 2
        let mut payload := false
        for candidate in payloads do
          if ← isDefEq type candidate then payload := true
        if product || payload then
          let .const head _ := type.getAppFn | continue
          let some (.inductInfo info) := (← getEnv).find? head | continue
          if info.numIndices != 0 then continue
          let branches ← goal.cases decl.fvarId
          let mut result := #[]
          for branch in branches do
            result := result ++ (← splitEvents branch.mvarId payloads)
          return result
    return #[goal]

/-- Add empty-state instances of universally quantified equation IHs. This is
finite proof preprocessing, not a supplied history invariant. -/
private partial def scalarInstances (value : Expr) (locals : Array LocalDecl)
    (fuel : Nat) : MetaM (Array Expr) := do
  if fuel == 0 then return #[value]
  let type ← whnf (← inferType value)
  if let .forallE _ domain _ _ := type then
    let domain ← whnf domain
    if domain.isAppOfArity ``Finset 1 || domain.isForall || (← isProp domain) then
      return #[value]
    let mut result := #[value]
    for decl in locals do
      unless decl.isImplementationDetail do
        if ← isDefEq decl.type domain then
          result := result ++ (← scalarInstances (mkApp value (mkFVar decl.fvarId)) locals (fuel - 1))
    return result
  return #[value]

private partial def finiteInstances (value : Expr) (locals : Array LocalDecl)
    (scalar : Bool) (fuel : Nat) : MetaM (Array Expr) := do
  if fuel == 0 then return #[]
  let type ← whnf (← inferType value)
  if let .forallE name domain _ _ := type then
    let domain ← whnf domain
    if domain.isAppOfArity ``Finset 1 then
      let empty ← mkAppOptM ``Finset.empty #[some domain.getAppArgs[0]!]
      let value := mkApp value empty
      if scalar then return ← scalarInstances value locals 4
      return #[value]
    if ← isProp domain then
      return ← withLocalDeclD name domain fun premise => do
        let instances ← finiteInstances (mkApp value premise) locals scalar (fuel - 1)
        instances.mapM fun instanceProof => mkLambdaFVars #[premise] instanceProof
  return #[]

private def specializeEmpty (goal : MVarId) : MetaM MVarId := goal.withContext do
  let hypotheses := (← getLCtx).foldl (init := #[]) fun hs decl =>
    if decl.isImplementationDetail then hs else hs.push decl
  let scalar := (← whnf (← goal.getType)).isConstOf ``False
  let mut result := goal
  let mut known := hypotheses.map (·.type)
  for decl in hypotheses do
    for witness in (← finiteInstances (mkFVar decl.fvarId) hypotheses scalar 4) do
      let proposition ← inferType witness
      if ← isProp proposition then
        if known.contains proposition then continue
        known := known.push proposition
        let next ← result.assert (← mkFreshUserName `finiteEmpty) proposition witness
        let (_, next) ← next.intro1
        result := next
  return result

elab "policy_split_logic" : tactic => do
  let mut result := []
  for goal in (← getGoals) do
    setGoals [goal]
    let target ← goal.withContext <| whnf (← goal.getType)
    if target.isAppOfArity ``Iff 2 || target.isAppOfArity ``And 2 then
      evalTactic (← `(tactic| constructor))
    result := result ++ (← getGoals)
  setGoals result

elab "policy_contradiction" : tactic => do
  let mut result := []
  for goal in (← getGoals) do
    setGoals [goal]
    let target ← goal.withContext <| whnf (← goal.getType)
    unless target.isConstOf ``False do
      evalTactic (← `(tactic| by_contra!))
    result := result ++ (← getGoals)
  setGoals result

elab "policy_preprocess" : tactic => do
  if (← getGoals).isEmpty then return
  evalTactic (← `(tactic| repeat' intro))
  let mut goals := #[]
  for goal in (← getGoals) do
    let types ← eventTypes goal
    for branch in (← splitEvents goal types) do
      goals := goals.push (← specializeEmpty branch)
  setGoals goals.toList

end Sal.MRDTs.Paper1.Automation.PolicyFinite

attribute [policy_expansion_simps] Sal.MRDTs.Foundation.UpdateSig.commutes

/- Goal-directed finite schema discharge. All operation constructors and
state-equation IH instances are discovered from types and formulas. -/
attribute [policy_expansion_simps]
  Signature.fresh_base Signature.fresh_step Signature.local_common_opposite
  Signature.local_opposite_fresh Signature.local_empty_past Signature.local_past_singleton
  Signature.causal_common_kernel Signature.causal_commuting_kernel
  Signature.causal_strict_kernel Signature.causal_absorber_kernel
  Signature.local_empty_sides CausalCoverage.signatureOf

macro "policy_witness" : tactic => `(tactic| (
  classical
  try simp only [policy_expansion_simps] at *
  policy_preprocess
  policy_split_logic
  policy_preprocess
  policy_contradiction
  policy_preprocess
  all_goals try intros
  policy_preprocess
  all_goals try simp_all [policy_expansion_simps, ite_eq_iff, Finset.ext_iff]
  all_goals try intros
  policy_preprocess
  all_goals try simp_all [policy_expansion_simps]
  all_goals grind (splits := 40) only))

macro "policy_auto" : tactic => `(tactic| (
  first
  | (solve |
      classical
      try simp only [policy_expansion_simps] at *
      policy_preprocess
      all_goals try simp_all [policy_expansion_simps, ite_eq_iff, Finset.ext_iff]
      all_goals try intros
      all_goals grind (splits := 20) only)
  | policy_witness))
