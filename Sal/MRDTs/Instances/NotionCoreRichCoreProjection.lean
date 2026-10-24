import Sal.MRDTs.Instances.NotionCoreRichPayload
import Sal.MRDTs.Instances.NotionCoreReconstruction

/-!
Erasing formatting preserves the actual plain transaction sequence.

The projection keeps complete edit transactions and their original source IDs.
It removes formatting transactions; it never substitutes empty edits or
renumbers an insertion. These list facts support the later reachable-network
projection, where formatting reservations become source clock gaps.
-/
namespace Sal.MRDTs.Instances.NotionCoreRichCoreProjection
open NotionRunAllocation (Id)
open NotionCoreRichPayload (Transaction)

def project (transaction : Transaction) : Option NotionCorePayload.Transaction :=
  match transaction.payload with
  | .edit payload => some ⟨transaction.id,payload⟩
  | .format _ _ => none

def edits (transactions : List Transaction) : List NotionCorePayload.Transaction :=
  transactions.filterMap project

@[simp] theorem edits_append (left right : List Transaction) :
    edits (left ++ right) = edits left ++ edits right := by simp [edits]

@[simp] theorem edits_cons_edit (id : Id) (payload : NotionCorePayload.Payload)
    (rest : List Transaction) : edits (⟨id,.edit payload⟩ :: rest) =
      ⟨id,payload⟩ :: edits rest := rfl

@[simp] theorem edits_cons_format (id : Id) (parts : List NotionCoreRichPayload.Part) (value : Bool)
    (rest : List Transaction) : edits (⟨id,.format parts value⟩ :: rest) = edits rest := rfl

theorem project_id {transaction : Transaction} {plain : NotionCorePayload.Transaction}
    (projected : project transaction = some plain) : plain.id = transaction.id := by
  cases transaction with
  | mk id payload =>
    cases payload with
    | edit payload => exact (congrArg NotionCorePayload.Transaction.id
        (Option.some.inj projected)).symm
    | format parts value => cases projected

theorem edits_member (transactions : List Transaction) (plain : NotionCorePayload.Transaction) :
    plain ∈ edits transactions ↔ ∃ transaction ∈ transactions, project transaction = some plain := by
  simp [edits]

theorem edits_perm {left right : List Transaction} (permutation : left.Perm right) :
    (edits left).Perm (edits right) := permutation.filterMap project

/-- Any relation on source IDs is preserved when whole formatting requests
are removed. In particular, no new order or identity premise is introduced. -/
theorem edits_pairwise (relation : Id → Id → Prop) (transactions : List Transaction)
    (ordered : transactions.Pairwise (fun a b => relation a.id b.id)) :
    (edits transactions).Pairwise (fun a b => relation a.id b.id) := by
  induction transactions with
  | nil => exact .nil
  | cons first rest ih =>
    obtain ⟨before,tail⟩ := List.pairwise_cons.mp ordered
    cases first with
    | mk id payload =>
      cases payload with
      | format parts value => simpa [edits,project] using ih tail
      | edit payload =>
        apply List.pairwise_cons.mpr
        refine ⟨?_,ih tail⟩
        intro plain member
        obtain ⟨transaction,present,projected⟩ := (edits_member rest plain).mp member
        simpa only [project_id projected] using before transaction present

theorem edits_ordered (transactions : List Transaction)
    (unique : (transactions.map Transaction.id).Nodup) :
    (edits (NotionCoreRichPayload.sort transactions)).Pairwise
      (fun a b => NotionRunAllocation.Before a.id b.id) :=
  edits_pairwise NotionRunAllocation.Before _ (NotionCoreRichPayload.sort_ordered transactions unique)

theorem erase_requests (transactions : List Transaction) :
    NotionCoreFormattingMachine.eraseFormats (transactions.map Transaction.request) = edits transactions := by
  induction transactions with
  | nil => rfl
  | cons first rest ih =>
    cases first with
    | mk id payload => cases payload <;> simp [Transaction.request,
        NotionCoreFormattingMachine.eraseFormats,edits,project,ih]

/-- The original interval interpreter and the plain machine have identical
edit effects, including failures. The repaired interpreter proves the same
projection separately; this lemma does not transfer its formatting semantics. -/
theorem original_reconstruct_core (transactions : List Transaction) :
    (NotionCoreRichPayload.reconstruct transactions).map NotionCoreFormattingMachine.State.core =
      NotionCoreMachine.replay {} (edits (NotionCoreRichPayload.sort transactions)) := by
  rw [NotionCoreRichPayload.reconstruct,NotionCoreFormattingMachine.replay_core_projection,
    erase_requests]

end Sal.MRDTs.Instances.NotionCoreRichCoreProjection
