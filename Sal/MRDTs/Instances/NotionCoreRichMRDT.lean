import Sal.MRDTs.Instances.NotionCoreRichNetwork
import Sal.MRDTs.Instances.NotionTransactionSet
import Sal.MRDTs.Paper1.Automation.GenericQueryLift

/-! Whole atomic rich transactions as actual finite-store MRDT elements.
The carrier's five VCs and ordinary/canonical recursive convergence remain
valid with the actual rich query. They do not supply the false atomic rich
selection-history bridge, refuted in RichAtomicCounterexample.
-/
namespace Sal.MRDTs.Instances.NotionCoreRichMRDT
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open NotionCoreRichPayload (Transaction)

abbrev View := List (Nat × List NotionCoreFormattingMachine.RichAtom)

noncomputable def transactions (state : Finset Transaction) : List Transaction :=
  NotionCoreRichPayload.sort state.toList

noncomputable def observe (state : Finset Transaction) : Option View :=
  NotionCoreFormattingMachine.replay {} ((transactions state).map Transaction.request) >>=
    NotionCoreFormattingMachine.render

noncomputable abbrev D : MRDTSig :=
  Automation.QueryLift.withQuery (FinsetStore.D Transaction) Unit (Option View) (fun state _ => observe state)

def issuance : Issuance D where
  CanIssue := fun _ _ => True

abbrev representation : Representation D := CommutingPort.representation D

theorem all_comm (a b : Op D.AppOp) : D.toUpdateSig.commutes a b := FinsetStore.all_comm a b

abbrev scheme (C : ReplayContext D.toUpdateSig) : @MetadataDependencies D C :=
  @CommutingPort.scheme D all_comm C

theorem fiveVCs : @Raw.MergeVCs D (commutingPolicy Transaction) representation scheme := by
  exact Automation.QueryLift.transport (FinsetStore.D Transaction) Unit (Option View)
    (fun state _ => observe state) (commutingPolicy Transaction)
    (CommutingPort.representation (FinsetStore.D Transaction))
    (CommutingPort.scheme (FinsetStore.all_comm (α := Transaction)))
    (NotionTransactionSet.fiveVCs (Tx := Transaction))

noncomputable def replayConditions (I : Issuance D) : VCReplayConditions (commutingPolicy Transaction) I :=
  CommutingPort.automatedReplayConditions (D := D) all_comm fiveVCs I

theorem carrierJoin : RepresentationJoin representation := (replayConditions issuance).join

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

noncomputable def carrierFor (network : NotionCoreRichNetwork.State) (session : NotionRunAllocation.Session) :
    Finset Transaction := (NotionCoreRichNetwork.receivedTransactions network session).toFinset

theorem transactions_carrierFor (network : NotionCoreRichNetwork.State)
    (reachable : NotionCoreRichNetwork.Reach network) (session : NotionRunAllocation.Session) :
    transactions (carrierFor network session) =
      NotionCoreRichPayload.sort (NotionCoreRichNetwork.receivedTransactions network session) := by
  let received := NotionCoreRichNetwork.receivedTransactions network session
  have ids := NotionCoreRichNetwork.received_keys_unique reachable session
  have unique : received.Nodup := by
    apply (List.pairwise_map.mp ids).imp
    intro a b apart same
    exact apart (congrArg Transaction.id same)
  have enumeration : (carrierFor network session).toList.Perm received := List.toFinset_toList unique
  have actualPerm : (transactions (carrierFor network session)).Perm received :=
    (NotionCoreRichPayload.sort_perm _).trans enumeration
  have enumerationIds := (enumeration.map Transaction.id).nodup_iff.mpr ids
  have ordered := NotionCoreRichPayload.sort_ordered _ enumerationIds
  have canonicalOrdered := NotionCoreRichPayload.sort_ordered received ids
  have permutation := actualPerm.trans (NotionCoreRichPayload.sort_perm received).symm
  exact permutation.eq_of_pairwise (fun _ _ _ _ forward reverse =>
    False.elim (NotionCoreSourceInvariant.before_asymm forward reverse)) ordered canonicalOrdered

/-- Finset enumeration and transaction-list receipt reconstruction agree on
all reachable callers. Whole format batches are never split into store items. -/
theorem observe_carrierFor (network : NotionCoreRichNetwork.State)
    (reachable : NotionCoreRichNetwork.Reach network) (session : NotionRunAllocation.Session) :
    observe (carrierFor network session) =
      (NotionCoreRichNetwork.reconstruct network session >>= NotionCoreFormattingMachine.render) := by
  rw [observe,transactions_carrierFor network reachable session]
  rfl

/-- The ordinary five-VC specialization proves actual rich-query convergence
for equal event sets. It intentionally states no sequential-spec agreement. -/
theorem convergence_ordinary {C : Configuration D}
    (reachable : MintCertifiedReach D issuance C) {v w : Version}
    {left right : Finset Transaction} {events : Set (Op Transaction)}
    (leftVersion : C.ver v = some (left,events)) (rightVersion : C.ver w = some (right,events)) :
    observe left = observe right := by
  have equal := (replayConditions issuance).unique C.replayContext events left right
    ((replayConditions issuance).representedVersions C reachable.toV v left events leftVersion)
    ((replayConditions issuance).representedVersions C reachable.toV w right events rightVersion)
  exact congrArg observe equal

theorem convergence_recursive {C : Configuration D}
    (reachable : MintCertifiedReachV D (canonicalVirtualMergeBase D) issuance C) {v w : Version}
    {left right : Finset Transaction} {events : Set (Op Transaction)}
    (leftVersion : C.ver v = some (left,events)) (rightVersion : C.ver w = some (right,events)) :
    observe left = observe right := by
  have equal := (replayConditions issuance).unique C.replayContext events left right
    ((replayConditions issuance).representedVersions C reachable v left events leftVersion)
    ((replayConditions issuance).representedVersions C reachable w right events rightVersion)
  exact congrArg observe equal

#print axioms fiveVCs
#print axioms observe_carrierFor
#print axioms convergence_ordinary
#print axioms convergence_recursive
end Sal.MRDTs.Instances.NotionCoreRichMRDT
