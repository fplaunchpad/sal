import Sal.MRDTs.Instances.NotionTransactionSet
import Sal.MRDTs.Instances.NotionCoreMachineCommands
import Sal.MRDTs.Instances.NotionCoreReconstruction
import Sal.MRDTs.Instances.NotionCoreHistory
import Sal.MRDTs.Instances.NotionCoreMachineBootstrap
import Sal.MRDTs.Paper1.Automation.GenericQueryLift

/-! Concrete whole-transaction finite-store MRDT with the actual typed core
renderer. The five VCs and represented execution supply concern its carrier;
source issuance/archive validity and independent history soundness are separate.
Source IDs order replay but are not the Sal event labels. -/
namespace Sal.MRDTs.Instances.NotionCoreMRDT
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open NotionCorePayload (Transaction)
open NotionCoreHistory (View)

/-- Literal source-key order. Outside a valid single archive, conflicting
transactions with equal IDs need not have a canonical payload order. -/
noncomputable def transactions (state : Finset Transaction) : List Transaction :=
  state.toList.mergeSort (fun a b => decide (NotionCoreReconstruction.Ascending a b))

/-- Actual checked replay and renderer, retaining errors at the query type. -/
noncomputable def observe (state : Finset Transaction) : Option View :=
  NotionCoreMachine.replay {} (transactions state) >>= NotionCoreMachine.render

noncomputable abbrev D : MRDTSig :=
  Automation.QueryLift.withQuery (FinsetStore.D Transaction) Unit (Option View) (fun state _ => observe state)

def issuance : Issuance D where
  CanIssue := fun _ _ => True

abbrev representation : Representation D := CommutingPort.representation D

theorem all_comm (a b : Op D.AppOp) : D.toUpdateSig.commutes a b :=
  FinsetStore.all_comm a b

abbrev scheme (C : ReplayContext D.toUpdateSig) : @MetadataDependencies D C :=
  @CommutingPort.scheme D all_comm C

/-- The unchanged finite carrier's five-VC bundle survives the real query
boundary; this theorem says nothing about correctness of rendered text. -/
theorem fiveVCs : @Raw.MergeVCs D (commutingPolicy Transaction) representation scheme := by
  exact Automation.QueryLift.transport (FinsetStore.D Transaction) Unit (Option View)
    (fun state _ => observe state) (commutingPolicy Transaction)
    (CommutingPort.representation (FinsetStore.D Transaction))
    (CommutingPort.scheme (FinsetStore.all_comm (α := Transaction)))
    (NotionTransactionSet.fiveVCs (Tx := Transaction))

noncomputable def replayConditions (I : Issuance D) : VCReplayConditions (commutingPolicy Transaction) I :=
  CommutingPort.automatedReplayConditions (D := D) all_comm fiveVCs I

theorem carrierJoin : RepresentationJoin representation := (replayConditions issuance).join

/-- Registered state representation is obtained through the VC induction,
including canonical recursive virtual merge bases, with the real query type. -/
theorem represented_versions {I : Issuance D} {C : Configuration D}
    (reachable : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C)
    (version : Version) (state : Finset Transaction) (events : Set (Op Transaction))
    (registered : C.ver version = some (state,events)) :
    representation C.replayContext events state :=
  (replayConditions I).representedVersions C reachable version state events registered

@[simp] theorem update_payload (state : Finset Transaction) (event : Op Transaction) :
    D.update state event = insert event.2.2 state := rfl

@[simp] theorem merge_union (base left right : Finset Transaction) :
    D.merge base left right = left ∪ right := rfl

@[simp] theorem query_observe (state : Finset Transaction) : D.query state () = observe state := rfl

/-- Equal carrier states imply equal actual document observations, including
explicit failures. Independent document semantics do not follow from this. -/
theorem observe_equal {left right : Finset Transaction} (same : left = right) :
    observe left = observe right := congrArg observe same

/-- Translate the application payload while retaining Sal event labels as
external inputs. Source IDs are carried inside the payload, not inferred from
the external event's timestamp or replica label. -/
def semanticLabel : SeqLabel (Op Transaction) Unit View →
    SeqLabel NotionCoreHistory.Update Unit View
  | .update event => .update ((NotionCoreMachineCommands.commands event.2.2).map
      NotionCoreSourceDocument.Command.semantic)
  | .query query answer => .query query answer

/-- The honest output embedding retains successful values and never turns
an actual error into an independently accepted empty document. -/
def someLabel : SeqLabel (Op Transaction) Unit View → SeqLabel (Op Transaction) Unit (Option View)
  | .update event => .update event
  | .query query answer => .query query (some answer)

/-- Alphabet/output lift of the existing independent history machine. All
update transitions delegate to CoreHistory; no transaction replay or clock
ordering is introduced into its document state. -/
def historyMachine : HistoryMachine (Op Transaction) Unit (Option View) where
  State := NotionCoreHistory.machine.State
  initial := NotionCoreHistory.machine.initial
  transition before label after := match label with
    | .update event => NotionCoreHistory.machine.transition before
        (.update ((NotionCoreMachineCommands.commands event.2.2).map
          NotionCoreSourceDocument.Command.semantic)) after
    | .query query (some answer) => NotionCoreHistory.machine.transition before (.query query answer) after
    | .query _ none => False

def spec : HistorySpec (Op Transaction) Unit (Option View) := historyMachine.toSpec

/-- Full finite-run transport, not just an endpoint rendering statement. -/
theorem runs_some_iff (history : List (SeqLabel (Op Transaction) Unit View))
    (before after : NotionCoreSpec.Document) :
    Runs historyMachine.transition before (history.map someLabel) after ↔
      Runs NotionCoreHistory.machine.transition before (history.map semanticLabel) after := by
  induction history generalizing before with
  | nil => constructor <;> intro run <;> cases run <;> exact .nil _
  | cons label rest ih =>
    have transition : ∀ start finish, historyMachine.transition start (someLabel label) finish ↔
        NotionCoreHistory.machine.transition start (semanticLabel label) finish := by
      intro start finish
      cases label <;> rfl
    constructor
    · intro run
      cases run with
      | cons step tail => exact .cons ((transition _ _).mp step) ((ih _).mp tail)
    · intro run
      cases run with
      | cons step tail => exact .cons ((transition _ _).mpr step) ((ih _).mpr tail)

/-- Some-valued query histories are admitted exactly when the original
independent core specification admits their payload-translated labels. -/
theorem some_admission_iff (history : List (SeqLabel (Op Transaction) Unit View)) :
    spec.admits (history.map someLabel) ↔
      NotionCoreHistory.spec.admits (history.map semanticLabel) := by
  constructor
  · rintro ⟨after,run⟩
    exact ⟨after,(runs_some_iff history _ after).mp run⟩
  · rintro ⟨after,run⟩
    exact ⟨after,(runs_some_iff history _ after).mpr run⟩

/-- Read-side failure rejection; inversion belongs in the theorem layer. -/
theorem none_query_rejected (pre suffix : List (SeqLabel (Op Transaction) Unit (Option View))) :
    ¬ spec.admits (pre ++ .query () none :: suffix) := by
  rintro ⟨after,run⟩
  obtain ⟨middle,_,tail⟩ := run.split pre (.query () none :: suffix)
  cases tail with
  | cons impossible _ => exact impossible

#print axioms some_admission_iff
#print axioms none_query_rejected

namespace SPOT
private def seed : Transaction := NotionCorePayload.bootstrap [97,98]
/-- The signature stores whole transactions once and merge retains both
branches; taking either branch alone is the wrong carrier behavior. -/
private def other : Transaction := ⟨⟨3,[66]⟩,.create none⟩
theorem carrier_control :
    D.merge ({seed} : Finset Transaction) ({seed} : Finset Transaction) ({other} : Finset Transaction) =
      ({seed,other} : Finset Transaction) ∧
    D.merge ({seed} : Finset Transaction) ({seed} : Finset Transaction) ({other} : Finset Transaction) ≠
      ({seed} : Finset Transaction) := by decide +kernel
/-- The real query renders the inserted seed text, and rejects both failure
and a constant empty-block observation. The expected ab is hand derived. -/
theorem render_control :
    observe ({seed} : Finset Transaction) = some [(0,[97,98])] ∧
    observe ({seed} : Finset Transaction) ≠ none ∧
    observe ({seed} : Finset Transaction) ≠ some [(0,[])] := by
  have sorted : transactions ({seed} : Finset Transaction) = [seed] := by
    simp [transactions]
  have replayed : NotionCoreMachine.replay {} [seed] =
      some (NotionCoreMachineBootstrap.seeded [97,98]) := by
    simpa only [NotionCoreMachine.replay,seed] using NotionCoreMachineBootstrap.bootstrap_executes [97,98]
  have rendered : NotionCoreMachine.render (NotionCoreMachineBootstrap.seeded [97,98]) =
      some [(0,[97,98])] := by decide +kernel
  simp [observe,sorted,replayed,rendered]

end SPOT

#print axioms fiveVCs
#print axioms carrierJoin
#print axioms represented_versions
#print axioms SPOT.carrier_control
#print axioms SPOT.render_control
end Sal.MRDTs.Instances.NotionCoreMRDT
