import Sal.MRDTs.Paper1.Automation.CommonVerification
import Sal.MRDTs.Paper1.Automation.PolicyKitAutomation
import Sal.MRDTs.Paper1.Automation.MaskKitAutomation

/-! Construct the policy input from data annotations. The annotations contain
no laws: selecting a template creates its proof obligations, which must be
discharged from implementation definitions by the shared tactics. -/
namespace Sal.MRDTs.Paper1.Automation.InputDerivation
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1

/-- The event comparison used by the finite policy expansion. -/
class PolicyData (D : MRDTSig) where
  order : Op D.AppOp → Op D.AppOp → RcRes

/-- Optional birth/kill description. Its presence selects semantic mask replay;
without it, the frontend attempts to project an existing replay witness. -/
class MaskData (D : MRDTSig) (P : OperationPolicy D.AppOp) where
  Record : Type
  recordDecidableEq : DecidableEq Record
  description : @MaskKitAutomation.Description D P Record recordDecidableEq

open Lean Elab Tactic Meta in
/-- Build the finite kit and the appropriate replay contract. Missing data
annotations and failed finite laws remain errors; no completed VC is searched. -/
elab "derive_mrdt_input" : tactic => do
  let target ← whnf (← getMainTarget)
  unless target.getAppFn.isConstOf ``CommonVerification.Input do
    throwError "derive_mrdt_input expects CommonVerification.Input"
  let args := target.getAppArgs
  let d := args[0]!
  let p := args[1]!
  let policyType ← mkAppM ``PolicyData #[d]
  let some policy ← synthInstance? policyType |
    throwError "derive_mrdt_input needs a PolicyData annotation for the event comparison"
  let order ← whnf (← mkAppOptM ``PolicyData.order #[some d, some policy])
  let orderSyntax ← Lean.Elab.Term.exprToSyntax order
  evalTactic (← `(tactic|
    refine CommonVerification.Input.policy (order := $orderSyntax) ?_ ?_))
  evalTactic (← `(tactic| · derive_policy_kit))
  let maskType ← mkAppM ``MaskData #[d, p]
  if let some mask ← synthInstance? maskType then
    let record ← whnf (← mkAppOptM ``MaskData.Record #[some d, some p, some mask])
    let decEq ← whnf (← mkAppOptM ``MaskData.recordDecidableEq #[some d, some p, some mask])
    let description ← whnf (← mkAppOptM ``MaskData.description #[some d, some p, some mask])
    let recordSyntax ← Lean.Elab.Term.exprToSyntax record
    let decEqSyntax ← Lean.Elab.Term.exprToSyntax decEq
    let descriptionSyntax ← Lean.Elab.Term.exprToSyntax description
    let dSyntax ← Lean.Elab.Term.exprToSyntax d
    let pSyntax ← Lean.Elab.Term.exprToSyntax p
    evalTactic (← `(tactic| (
      letI := $decEqSyntax
      let kit : MaskCanonical.Kit $dSyntax $pSyntax $recordSyntax := by
        derive_mask_kit using $descriptionSyntax
      exact CommonVerification.ReplayContract.mask kit (by mask_shape))))
  else
    evalTactic (← `(tactic| (
      apply CommonVerification.ReplayContract.witness
      · policy_auto
      · intros
        simp only [mrdt_implementation] at *
        aesop (rule_sets := [-default]) (config := { terminal := true }))))

end Sal.MRDTs.Paper1.Automation.InputDerivation
