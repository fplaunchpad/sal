import Sal.MRDTs.Paper1.Automation.CommonVerificationRules
import Sal.MRDTs.Paper1.Automation.CommonAlgebraAutomation
import Sal.MRDTs.Paper1.Automation.TransferSimple
import Sal.MRDTs.Paper1.Automation.GenericPolicyExpansion
import Sal.MRDTs.Paper1.Automation.GenericMaskCanonical
import Sal.MRDTs.Paper1.Automation.GenericCertifiedRecords
import Sal.MRDTs.Paper1.Automation.GenericOrderedRecords
import Sal.MRDTs.Paper1.Automation.GenericMonotoneProduct
import Sal.MRDTs.Paper1.Automation.GenericArchivedOrderedRecords
import Sal.MRDTs.Paper1.Automation.GenericQueryLift
import Sal.MRDTs.Paper1.Automation.PolicyExpansionAutomation
import Sal.MRDTs.Paper1.Automation.OrderedRecordAutomation

/-! One checked interface for implementation, policy, existing representation
and metadata scheme. Inputs contain finite kits and projections of execution
contracts. Every route invokes a generic proof, never a datatype VC theorem. -/
namespace Sal.MRDTs.Paper1.Automation.CommonVerification
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 ConcreteMRDT

/-- Policy replay evidence is exposed in its existing witness/semantic shape;
there is no arbitrary canonicality or correctness theorem field. -/
inductive ReplayContract (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (R : Representation D) : Prop where
  | witness
      (noncomm : ∀a b:Op D.AppOp,¬D.toUpdateSig.commutes a b ↔
        P.before a.op b.op ∨ P.before b.op a.op)
      (project : ∀C H s,R C H s → ∃xs,listPermOf xs H ∧
        respects xs (@loOn D.toUpdateSig P.lift C H) ∧
        applySeq D.toUpdateSig D.init xs=s)
  | mask {Record : Type} [DecidableEq Record]
      (kit : MaskCanonical.Kit D P Record)
      (project : ∀C H s,R C H s → MaskCanonical.Shape kit C H s)

theorem ReplayContract.canonical {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {R : Representation D} (contract : ReplayContract D P R)
    (laws : GuardedReplay.Laws D.toUpdateSig P) :
    ∀C H s,R C H s → Canonical P C H s := by
  cases contract with
  | witness noncomm project =>
    exact fun C H s rep => PolicyExpansion.canonical_of_loWitness noncomm C H s (project C H s rep)
  | mask kit project =>
    exact fun C H s rep => MaskCanonical.canonical kit laws C H s (project C H s rep)

/-- Declarative finite input. Exact contract equalities and evidence projections
preserve the supplied representation, policy and scheme. -/
inductive Input : (D : MRDTSig) → OperationPolicy D.AppOp → Representation D →
    (∀C : ReplayContext D.toUpdateSig,MetadataDependencies C) → Prop where
  | commuting {D : MRDTSig} {P : OperationPolicy D.AppOp} {R : Representation D}
      {M : ∀C : ReplayContext D.toUpdateSig,MetadataDependencies C}
      (commute : ∀a b,D.toUpdateSig.commutes a b)
      (kit : TransferSimple.EmptyPastKernels D)
      (policy : P=commutingPolicy D.AppOp)
      (representation : R=CommutingPort.representation D)
      (metadata : M=CommutingPort.scheme commute) : Input D P R M
  | policy {D : MRDTSig} {P : OperationPolicy D.AppOp} {R : Representation D}
      {M : ∀C : ReplayContext D.toUpdateSig,MetadataDependencies C}
      {order : Op D.AppOp → Op D.AppOp → RcRes}
      (kit : PolicyExpansion.Kit D P order)
      (contract : ReplayContract D P R) : Input D P R M
  | immutable {D : MRDTSig} {P : OperationPolicy D.AppOp} {R : Representation D}
      {M : ∀C : ReplayContext D.toUpdateSig,MetadataDependencies C}
      {Record : Type} [DecidableEq Record] {I : Issuance D}
      (model : GenericCertifiedRecords.Model D I Record)
      (representation : R=model.Representation)
      (metadata : ∀C a b,(M C).before a b ↔ C.vis a b) : Input D P R M
  | ordered {D : MRDTSig} {P : OperationPolicy D.AppOp} {R : Representation D}
      {M : ∀C : ReplayContext D.toUpdateSig,MetadataDependencies C}
      {Record : Type} [DecidableEq Record]
      (kit : OrderedRecords.Kit D Record)
      (metadata : ∀C a b,(M C).before a b ↔ C.vis a b)
      (project : ∀C H s,R C H s →
        OrderedRecords.IssuerEvidence kit C ∧ OrderedRecords.ReplayEvidence C H s) : Input D P R M
  | product {Text : MRDTSig} {Record A B : Type}
      [DecidableEq Record] [DecidableEq A] [DecidableEq B]
      {P : OperationPolicy (MonotoneProduct.product Text A B).AppOp}
      {R : Representation (MonotoneProduct.product Text A B)}
      {M : ∀C : ReplayContext (MonotoneProduct.product Text A B).toUpdateSig,MetadataDependencies C}
      (kit : OrderedRecords.Kit Text Record)
      (project : ∀C H s,R C H s → MonotoneProduct.Evidence kit C H s) :
      Input (MonotoneProduct.product Text A B) P R M
  | archived {D : MRDTSig} {P : OperationPolicy D.AppOp} {R : Representation D}
      {M : ∀C : ReplayContext D.toUpdateSig,MetadataDependencies C}
      {Record Archive : Type} [DecidableEq Record] [DecidableEq Archive]
      (kit : ArchivedOrderedRecords.Kit D Record Archive)
      (metadata : ∀C a b,(M C).before a b ↔ C.vis a b)
      (project : ∀C H s,R C H s →
        ArchivedOrderedRecords.IssuerEvidence kit C ∧ ArchivedOrderedRecords.ReplayEvidence C H s) :
      Input D P R M
  | queryLift {D : MRDTSig} {P : OperationPolicy D.AppOp} {R : Representation D}
      {M : ∀C : ReplayContext D.toUpdateSig,MetadataDependencies C}
      (Q V : Type) (query : D.State → Q → V) (base : Input D P R M) :
      Input (QueryLift.withQuery D Q V query) P R (QueryLift.scheme D Q V query M)

/-- The common soundness theorem; input constructors expose finite/evidence
fields rather than a completed VC. -/
theorem verify {D : MRDTSig} {P : OperationPolicy D.AppOp} {R : Representation D}
    {M : ∀C : ReplayContext D.toUpdateSig,MetadataDependencies C}
    (input : Input D P R M) : Raw.MergeVCs P R M := by
  induction input with
  | commuting commute kit policy representation metadata =>
    cases policy; cases representation; cases metadata
    exact TransferSimple.assemble _ commute kit
  | policy kit contract =>
    exact PolicyExpansion.assemble kit _ (contract.canonical (PolicyExpansion.laws kit)) _
  | immutable model representation metadata =>
    cases representation
    exact model.five_vcs _ _ metadata
  | ordered kit metadata project =>
    exact OrderedRecords.assemble kit _ _ _ metadata project
  | product kit project =>
    exact MonotoneProduct.assemble kit _ _ _ project
  | archived kit metadata project =>
    exact ArchivedOrderedRecords.assemble kit _ _ _ metadata project
  | queryLift Q V query base ih =>
    exact QueryLift.transport _ Q V query _ _ _ ih

end Sal.MRDTs.Paper1.Automation.CommonVerification

/-- Search only registered declarative inputs. Missing annotations or finite
premises remain ordinary typed goals; no legacy VC fallback is available. -/
macro "mrdt_verify" : tactic => `(tactic| (
  apply Sal.MRDTs.Paper1.Automation.CommonVerification.verify
  aesop (rule_sets := [MRDTVerification, -default]) (config := { terminal := true })))

macro "mrdt_verify" " using " input:term : tactic =>
  `(tactic| exact Sal.MRDTs.Paper1.Automation.CommonVerification.verify $input)

open Lean Elab Command Meta in
/-- Register only an `Input` declaration. Completed VC theorems are rejected
before they can enter the common search registry. -/
elab "register_mrdt_input " declaration:ident : command => do
  let name ← resolveGlobalConstNoOverload declaration
  let info ← getConstInfo name
  liftTermElabM do
    forallTelescopeReducing info.type fun parameters target => do
      for parameter in parameters do
        let type ← inferType parameter
        let reduced ← whnf type
        let forbidden := fun expression : Expr => expression.find? fun subexpression =>
          match subexpression with
          | .const name _ =>
            ["Sal.MRDTs.Paper1.ConcreteMRDT.Raw.MergeVCs",
             "Sal.MRDTs.Paper1.ConcreteMRDT.Raw.JoinAtSize",
             "Sal.MRDTs.Join", "Sal.MRDTs.JoinOn", "Sal.MRDTs.JoinAt",
             "Sal.MRDTs.MergeLaws", "Sal.MRDTs.DeltaLaws",
             "Sal.MRDTs.Paper1.ConcreteMRDT.VCReplayConditions",
             "Sal.MRDTs.Paper1.ConcreteMRDT.VCConditions"].contains name.toString
          | _ => false
        if (forbidden type).isSome || (forbidden reduced).isSome then
          throwError "register_mrdt_input rejects a completed correctness premise"
      unless target.getAppFn.isConstOf ``Sal.MRDTs.Paper1.Automation.CommonVerification.Input do
        throwError "register_mrdt_input requires CommonVerification.Input; completed VC theorems cannot be registered"
  elabCommand (← `(command| attribute [aesop (rule_sets := [MRDTVerification]) safe apply] $declaration:ident))

/-- Expose the exact unsolved annotation/finite goals without a legacy fallback. -/
macro "mrdt_obligations" : tactic => `(tactic| (
  apply Sal.MRDTs.Paper1.Automation.CommonVerification.verify
  aesop (rule_sets := [MRDTVerification, -default])
    (config := { warnOnNonterminal := false })))
