import Sal.MRDTs.Instances.NotionCoreMachineBirths

/-! Per-peer reconstruction from the typed published archive and actual whole
run receipts. Source Replica stores immutable transactions by key; reachable
archive uniqueness supplies that map discipline. This is not a wire decoder or
JSON equality implementation. Reconstruction may fail on unsupported/malformed
states; no progress or observation theorem is assumed. -/
namespace Sal.MRDTs.Instances.NotionCoreReconstruction
open NotionCorePayload (Transaction reservation)
open NotionCorePayloadNetwork (State Entry forget)
open NotionRunAllocation (Session Run)

def Ascending (a b : Transaction) : Prop := NotionCoreSourceInvariant.Desc b.id a.id
instance : DecidableRel Ascending := fun _ _ => inferInstanceAs (Decidable (NotionCoreSourceInvariant.Desc _ _))

/-- The document constructor's sorted transaction sequence. Replica.transactions
returns Map insertion order; that intermediate order is erased by source sorting. -/
def transactions (network : State) (session : Session) : List Transaction :=
  ((network.entries.map Entry.tx).filter
    (fun tx => reservation tx ∈ (network.allocation.peers session).received)).mergeSort
      (fun a b => decide (Ascending a b))

def reconstruct (network : State) (session : Session) : Option NotionCoreMachine.State :=
  NotionCoreMachine.replay {} (transactions network session)

theorem transactions_membership (network : State) (session : Session) (tx : Transaction) :
    tx ∈ transactions network session ↔
      (∃ entry ∈ network.entries, entry.tx = tx) ∧
        reservation tx ∈ (network.allocation.peers session).received := by
  unfold transactions
  rw [(List.mergeSort_perm _ _).mem_iff]
  simp

theorem transactions_received (network : State) (session : Session) :
    ∀ tx ∈ transactions network session, ∃ entry ∈ network.entries, entry.tx = tx ∧
      reservation tx ∈ (network.allocation.peers session).received := by
  intro tx member
  obtain ⟨⟨entry,present,same⟩,received⟩ := (transactions_membership network session tx).mp member
  exact ⟨entry,present,same,received⟩

/-- Canonical transaction replay projects to exactly the previously proved
canonical run replay, not an arbitrary permutation or externally supplied list. -/
theorem transactions_runs (network : State) (session : Session) :
    (transactions network session).map reservation =
      NotionCoreIssuance.replay (forget network) (network.allocation.peers session).received := by
  unfold transactions
  rw [List.map_mergeSort (s := fun a b => decide (NotionCoreIssuance.Ascending a b))
    (by intros; rfl)]
  unfold NotionCoreIssuance.replay forget
  simp only [List.map_map, Function.comp_def]
  have filtered :
      (((network.entries.map Entry.tx).filter
        (fun tx => reservation tx ∈ (network.allocation.peers session).received)).map reservation) =
      ((network.entries.map (fun e => e.record.run)).filter
        (fun run => run ∈ (network.allocation.peers session).received)) := by
    induction network.entries with
    | nil => rfl
    | cons entry rest ih =>
      by_cases receipt : reservation entry.tx ∈ (network.allocation.peers session).received
      · simp only [List.map_cons, List.filter_cons, Entry.record, NotionCorePayload.record,
          receipt, decide_true, if_true, List.map_cons]
        exact congrArg (List.cons (reservation entry.tx)) ih
      · simp only [List.map_cons, List.filter_cons, Entry.record, NotionCorePayload.record,
          receipt, decide_false, Bool.false_eq_true, if_false]
        exact ih

  rw [filtered]

theorem transactions_ordered (network : State)
    (reachable : NotionCorePayloadNetwork.Reach network) (session : Session) :
    (transactions network session).Pairwise (fun a b => NotionRunAllocation.Before a.id b.id) := by
  have ordered := NotionCoreIssuance.replay_ordered
    (NotionCorePayloadNetwork.forget_reachable reachable)
    (network.allocation.peers session).received
  rw [← transactions_runs] at ordered
  have lifted : (transactions network session).Pairwise
      (fun a b => NotionRunAllocation.Before (reservation a).first (reservation b).first) :=
    (List.pairwise_map (f := reservation)
      (R := fun a b : Run => NotionRunAllocation.Before a.first b.first)).mp ordered
  simpa only [reservation] using lifted

/-- Actual stored/traversed item knowledge now needs no free receipt-map
premise: the reconstruction itself fixes its archived received transactions. -/
theorem reconstruct_known_item (network : State) (session : Session)
    (result : NotionCoreMachine.State) (accepted : reconstruct network session = some result)
    (inst : NotionCorePayload.BlockKey) (id : NotionRunAllocation.Id)
    (member : id ∈ (NotionCoreMachine.getInstance result (NotionCoreMachine.blockName inst)).rows.map
      (fun row => row.item.id)) :
    NotionCorePayloadNetwork.Known network session (inst,id) := by
  exact NotionCoreMachineBirths.replay_known_item network session _ result
    (transactions_received network session) accepted inst id member

private def seed := NotionCorePayloadNetwork.seeded [97,98]
private def next : Transaction := ⟨⟨3,[65]⟩,.create (some .initial)⟩
private def published := NotionCorePayloadNetwork.emit seed [65] next.payload next

/-- Source reconstructs transaction-key order rather than newest-first archive
order; a peer without receipts does not acquire the globally published list. -/
theorem reconstruction_control :
    transactions published [65] = [NotionCorePayload.bootstrap [97,98],next] ∧
    transactions published [65] ≠ [next,NotionCorePayload.bootstrap [97,98]] ∧
    transactions published [66] = [] := by
  simp [transactions, published, seed, next, NotionCorePayloadNetwork.emit,
    NotionCorePayloadNetwork.seeded, NotionCorePayloadNetwork.initial,
    NotionCorePayload.bootstrap, reservation, NotionCorePayload.Payload.width,
    NotionCorePayload.Payload.itemCount, NotionRunAllocation.issue,
    NotionRunAllocation.initial, NotionRunAllocation.receive, NotionRunAllocation.reserve,
    NotionRunAllocation.emptyPeer, NotionRunAllocation.Run.last, List.mergeSort, Ascending,
    NotionCoreSourceInvariant.Desc, NotionRunAllocation.Before]

#print axioms transactions_runs
#print axioms reconstruct_known_item
end Sal.MRDTs.Instances.NotionCoreReconstruction
