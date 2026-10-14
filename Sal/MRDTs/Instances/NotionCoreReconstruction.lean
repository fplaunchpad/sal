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

/-- The same source sorting applied to an explicit version of one archive.
Closure and issuance obligations belong to the replay theorems, not this filter. -/
def transactionsFor (network : State) (version : List Run) : List Transaction :=
  ((network.entries.map Entry.tx).filter
    (fun tx => reservation tx ∈ version)).mergeSort (fun a b => decide (Ascending a b))

theorem transactions_eq_for (network : State) (session : Session) :
    transactions network session = transactionsFor network (network.allocation.peers session).received := rfl

def reconstruct (network : State) (session : Session) : Option NotionCoreMachine.State :=
  NotionCoreMachine.replay {} (transactions network session)

theorem transactionsFor_membership (network : State) (version : List Run) (tx : Transaction) :
    tx ∈ transactionsFor network version ↔
      (∃ entry ∈ network.entries, entry.tx = tx) ∧
        reservation tx ∈ version := by
  unfold transactionsFor
  rw [(List.mergeSort_perm _ _).mem_iff]
  simp

theorem transactionsFor_received (network : State) (version : List Run) :
    ∀ tx ∈ transactionsFor network version, ∃ entry ∈ network.entries, entry.tx = tx ∧
      reservation tx ∈ version := by
  intro tx member
  obtain ⟨⟨entry,present,same⟩,received⟩ := (transactionsFor_membership network version tx).mp member
  exact ⟨entry,present,same,received⟩

/-- Canonical transaction replay projects to exactly the previously proved
canonical run replay, not an arbitrary permutation or externally supplied list. -/
theorem transactionsFor_runs (network : State) (version : List Run) :
    (transactionsFor network version).map reservation =
      NotionCoreIssuance.replay (forget network) version := by
  unfold transactionsFor
  rw [List.map_mergeSort (s := fun a b => decide (NotionCoreIssuance.Ascending a b))
    (by intros; rfl)]
  unfold NotionCoreIssuance.replay forget
  simp only [List.map_map, Function.comp_def]
  have filtered :
      (((network.entries.map Entry.tx).filter
        (fun tx => reservation tx ∈ version)).map reservation) =
      ((network.entries.map (fun e => e.record.run)).filter
        (fun run => run ∈ version)) := by
    induction network.entries with
    | nil => rfl
    | cons entry rest ih =>
      by_cases receipt : reservation entry.tx ∈ version
      · simp only [List.map_cons, List.filter_cons, Entry.record, NotionCorePayload.record,
          receipt, decide_true, if_true, List.map_cons]
        exact congrArg (List.cons (reservation entry.tx)) ih
      · simp only [List.map_cons, List.filter_cons, Entry.record, NotionCorePayload.record,
          receipt, decide_false, Bool.false_eq_true, if_false]
        exact ih

  rw [filtered]

theorem transactionsFor_ordered (network : State)
    (reachable : NotionCorePayloadNetwork.Reach network) (version : List Run) :
    (transactionsFor network version).Pairwise (fun a b => NotionRunAllocation.Before a.id b.id) := by
  have ordered := NotionCoreIssuance.replay_ordered
    (NotionCorePayloadNetwork.forget_reachable reachable)
    version
  rw [← transactionsFor_runs] at ordered
  have lifted : (transactionsFor network version).Pairwise
      (fun a b => NotionRunAllocation.Before (reservation a).first (reservation b).first) :=
    (List.pairwise_map (f := reservation)
      (R := fun a b : Run => NotionRunAllocation.Before a.first b.first)).mp ordered
  simpa only [reservation] using lifted

/-- Receipt order and multiplicity do not affect the selected canonical list. -/
theorem transactionsFor_ext (network : State) (left right : List Run)
    (same : ∀ run, run ∈ left ↔ run ∈ right) :
    transactionsFor network left = transactionsFor network right := by
  unfold transactionsFor
  congr 1
  apply List.filter_congr
  intro tx _
  simp only [decide_eq_decide]
  exact same (reservation tx)

/-- A supported version with no duplicates is enumerated exactly once by the
canonical transaction replay, including versions not held by a live peer. -/
theorem transactionsFor_enumerates (network : State)
    (reachable : NotionCorePayloadNetwork.Reach network) (version : List Run)
    (unique : version.Nodup)
    (supported : ∀ run ∈ version, run ∈ (forget network).records.map NotionCoreIssuance.Record.run) :
    ((transactionsFor network version).map reservation).Perm version := by
  rw [transactionsFor_runs]
  have ordered := NotionCoreIssuance.replay_ordered
    (NotionCorePayloadNetwork.forget_reachable reachable) version
  have replayUnique : (NotionCoreIssuance.replay (forget network) version).Nodup := by
    apply ordered.imp
    intro a b before equal
    subst b
    exact NotionCoreSourceInvariant.before_irrefl _ before
  apply (List.perm_ext_iff_of_nodup replayUnique unique).mpr
  intro run
  rw [NotionCoreIssuance.replay_membership]
  exact ⟨And.right,fun member => ⟨supported run member,member⟩⟩

theorem transactions_membership (network : State) (session : Session) (tx : Transaction) :
    tx ∈ transactions network session ↔
      (∃ entry ∈ network.entries, entry.tx = tx) ∧
        reservation tx ∈ (network.allocation.peers session).received :=
  transactionsFor_membership network _ tx

theorem transactions_received (network : State) (session : Session) :
    ∀ tx ∈ transactions network session, ∃ entry ∈ network.entries, entry.tx = tx ∧
      reservation tx ∈ (network.allocation.peers session).received :=
  transactionsFor_received network _

theorem transactions_runs (network : State) (session : Session) :
    (transactions network session).map reservation =
      NotionCoreIssuance.replay (forget network) (network.allocation.peers session).received :=
  transactionsFor_runs network _

theorem transactions_ordered (network : State)
    (reachable : NotionCorePayloadNetwork.Reach network) (session : Session) :
    (transactions network session).Pairwise (fun a b => NotionRunAllocation.Before a.id b.id) :=
  transactionsFor_ordered network reachable _

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

#print axioms transactionsFor_enumerates
#print axioms transactionsFor_runs
#print axioms transactionsFor_ordered
#print axioms transactions_runs
#print axioms reconstruct_known_item
end Sal.MRDTs.Instances.NotionCoreReconstruction
