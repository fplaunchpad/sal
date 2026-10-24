import Sal.MRDTs.Instances.NotionCoreRichProtocolNetwork
import Sal.MRDTs.Instances.NotionCoreFormattingSpec
import Sal.MRDTs.Instances.NotionTransactionSet
import Sal.MRDTs.Paper1.Automation.GenericQueryLift

/-! Whole atomic rich transactions as actual finite-store MRDT elements.
The carrier's five VCs and ordinary/canonical recursive convergence use the
repaired rich query. Sequential agreement is established separately over the
explicit source/framework protocol, not inferred from storage convergence.
-/
namespace Sal.MRDTs.Instances.NotionCoreRichProtocolCarrier
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open NotionCoreRichPayload (Transaction)

abbrev RawView := List (Nat × List NotionCoreAtomicFormattingMachine.RichAtom)
abbrev View := List (Nat × List NotionCoreFormattingSpec.RichChar)

/-- Pure record relabelling aligns the actual renderer with the independent
specification's neutral query type. Every identity, value and mark is retained. -/
def neutral (view : RawView) : View :=
  view.map fun (block,atoms) => (block,atoms.map fun atom => ⟨atom.address,atom.value,atom.bold⟩)

def restore (view : View) : RawView :=
  view.map fun (block,atoms) => (block,atoms.map fun atom => ⟨atom.address,atom.value,atom.bold⟩)

@[simp] theorem restore_neutral (view : RawView) : restore (neutral view) = view := by
  induction view with
  | nil => rfl
  | cons block rest ih =>
    rcases block with ⟨block,atoms⟩
    simp only [neutral,restore,List.map_cons,List.map_map] at ih ⊢
    rw [ih]
    congr 2
    induction atoms with
    | nil => rfl
    | cons atom atoms ih => cases atom; simp only [List.map_cons,ih]; rfl

theorem neutral_injective : Function.Injective neutral := by
  intro left right equal
  simpa only [restore_neutral] using congrArg restore equal

theorem neutral_forget (view : RawView) :
    NotionCoreFormattingSpec.forget (neutral view) = NotionCoreAtomicFormattingMachine.forget view := by
  simp [NotionCoreFormattingSpec.forget,neutral,NotionCoreAtomicFormattingMachine.forget,
    NotionCoreFormattingMachine.forget,List.map_map]

noncomputable def transactions (state : Finset Transaction) : List Transaction :=
  NotionCoreRichPayload.sort state.toList

noncomputable def observe (state : Finset Transaction) : Option View :=
  (NotionCoreAtomicFormattingMachine.replay {} (transactions state) >>=
    NotionCoreAtomicFormattingMachine.render).map neutral

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

theorem fold_payloads (state : Finset Transaction) (events : List (Op Transaction)) :
    applySeq D.toUpdateSig state events = state ∪ (events.map Op.op).toFinset := by
  induction events generalizing state with
  | nil => simp [applySeq]
  | cons event rest ih =>
    change applySeq D.toUpdateSig ((insert event.op state) : Finset Transaction) rest = _
    rw [ih]
    apply Finset.ext
    intro tx
    simp [or_left_comm]

theorem transactions_of_sorted (txs : List Transaction)
    (ordered : txs.Pairwise (fun a b => NotionRunAllocation.Before a.id b.id)) :
    transactions txs.toFinset = txs := by
  have ids : (txs.map Transaction.id).Nodup := by
    apply List.pairwise_map.mpr
    apply ordered.imp
    intro a b h same
    exact NotionCoreSourceInvariant.before_irrefl b.id (same ▸ h)
  have unique : txs.Nodup := List.Nodup.of_map Transaction.id ids
  have enumeration : txs.toFinset.toList.Perm txs := List.toFinset_toList unique
  have actualPerm : (transactions txs.toFinset).Perm txs :=
    (NotionCoreRichPayload.sort_perm _).trans enumeration
  have enumerationIds := (enumeration.map Transaction.id).nodup_iff.mpr ids
  have actualOrdered := NotionCoreRichPayload.sort_ordered _ enumerationIds
  exact actualPerm.eq_of_pairwise (fun _ _ _ _ forward reverse =>
    False.elim (NotionCoreSourceInvariant.before_asymm forward reverse)) actualOrdered ordered

noncomputable def carrierFor (network : NotionCoreRichProtocolNetwork.State) (session : NotionRunAllocation.Session) :
    Finset Transaction := (NotionCoreRichProtocolNetwork.receivedTransactions network session).toFinset

theorem transactions_carrierFor (network : NotionCoreRichProtocolNetwork.State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network) (session : NotionRunAllocation.Session) :
    transactions (carrierFor network session) =
      NotionCoreRichPayload.sort (NotionCoreRichProtocolNetwork.receivedTransactions network session) := by
  let received := NotionCoreRichProtocolNetwork.receivedTransactions network session
  have ids := NotionCoreRichProtocolNetwork.received_keys_unique reachable session
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
theorem observe_carrierFor (network : NotionCoreRichProtocolNetwork.State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network) (session : NotionRunAllocation.Session) :
    observe (carrierFor network session) =
      (NotionCoreRichProtocolNetwork.reconstruct network session >>= NotionCoreAtomicFormattingMachine.render).map neutral := by
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
end Sal.MRDTs.Instances.NotionCoreRichProtocolCarrier
