import Sal.MRDTs.Instances.NotionCoreMachineVersionTables

/-! Honest canonical next text births cannot have prior pending tombstones.
Raw future-target deletion is supported by the interpreter, but excluded here
by issued-reference causality. No desired fresh flags or output are premises. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineFreshText
open NotionCorePayload (BlockKey Transaction reservation)
open NotionCorePayloadNetwork (Reach)
open NotionRunAllocation (Id Session Run)
open NotionCoreMachine

private theorem target_reference (tx : Transaction) (inst : BlockKey) (id : Id)
    (target : id ∈ NotionCoreTableView.transactionTargets tx inst) :
    id ∈ tx.payload.references := by
  cases tx with
  | mk first payload =>
    cases payload <;> simp [NotionCoreTableView.transactionTargets] at target
    simpa [NotionCorePayload.Payload.references] using target.2

/-- All actual old pending targets have counters below the next transaction,
including targets of earlier deletions from other sessions. -/
theorem version_pending_counter_before (network : NotionCorePayloadNetwork.State) (reachable : Reach network)
    (version : List Run) (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : NotionCoreMachine.State) (accepted : replay {} pre = some state)
    (inst : BlockKey) (id : Id)
    (pending : id ∈ (getInstance state (blockName inst)).pending) :
    id.counter < tx.id.counter := by
  rw [(NotionCoreMachineVersionTables.version_tables network reachable version pre (tx :: suffix)
    position state accepted inst).2] at pending
  obtain ⟨previous, inPre, target⟩ := List.mem_flatMap.mp pending
  obtain ⟨entry, member, same, _⟩ := NotionCoreReconstruction.transactionsFor_received network version previous
    (position ▸ List.mem_append_left _ inPre)
  have reference : id ∈ entry.record.references := by
    change id ∈ entry.tx.payload.references
    rw [same]
    exact target_reference previous inst id target
  have earlier := NotionCoreIssuance.reference_counter_before
    (NotionCorePayloadNetwork.forget_reachable reachable)
    (List.mem_map.mpr ⟨entry,member,rfl⟩) reference
  have strict := position ▸ NotionCoreReconstruction.transactionsFor_ordered network reachable version
  have before := (List.pairwise_append.mp strict).2.2 previous inPre tx (by simp)
  have bound : previous.id.counter ≤ tx.id.counter := by
    rcases before with less | ⟨equal,_⟩ <;> omega
  change id.counter < entry.tx.id.counter at earlier
  rw [same] at earlier
  omega

theorem version_offset_not_pending (network : NotionCorePayloadNetwork.State) (reachable : Reach network)
    (version : List Run) (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : NotionCoreMachine.State) (accepted : replay {} pre = some state)
    (inst : BlockKey) (offset : Nat) :
    NotionCorePayload.offsetId tx.id offset ∉ (getInstance state (blockName inst)).pending := by
  intro pending
  have before := version_pending_counter_before network reachable version pre suffix tx position
    state accepted inst _ pending
  simp only [NotionCorePayload.offsetId] at before
  omega

/-- Literal allocated text decoding agrees with static fresh text flags for
any next canonical transaction, without assuming insertion already succeeds. -/
theorem version_textItems_pending_false (network : NotionCorePayloadNetwork.State) (reachable : Reach network)
    (version : List Run) (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : NotionCoreMachine.State) (accepted : replay {} pre = some state)
    (inst : BlockKey) (atoms : List Nat) :
    NotionCorePayload.textItems tx.id atoms
      (fun id => decide (id ∈ (getInstance state (blockName inst)).pending)) =
    NotionCorePayload.textItems tx.id atoms (fun _ => false) := by
  unfold NotionCorePayload.textItems
  apply List.map_congr_left
  intro offset _
  simp [version_offset_not_pending network reachable version pre suffix tx position state accepted inst offset]

theorem canonical_pending_counter_before (network : NotionCorePayloadNetwork.State) (reachable : Reach network)
    (peer : Session) (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : NotionCoreMachine.State) (accepted : replay {} pre = some state)
    (inst : BlockKey) (id : Id)
    (pending : id ∈ (getInstance state (blockName inst)).pending) :
    id.counter < tx.id.counter :=
  version_pending_counter_before network reachable _ pre suffix tx position state accepted inst id pending

theorem canonical_offset_not_pending (network : NotionCorePayloadNetwork.State) (reachable : Reach network)
    (peer : Session) (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : NotionCoreMachine.State) (accepted : replay {} pre = some state)
    (inst : BlockKey) (offset : Nat) :
    NotionCorePayload.offsetId tx.id offset ∉ (getInstance state (blockName inst)).pending :=
  version_offset_not_pending network reachable _ pre suffix tx position state accepted inst offset

theorem canonical_textItems_pending_false (network : NotionCorePayloadNetwork.State) (reachable : Reach network)
    (peer : Session) (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : NotionCoreMachine.State) (accepted : replay {} pre = some state)
    (inst : BlockKey) (atoms : List Nat) :
    NotionCorePayload.textItems tx.id atoms
      (fun id => decide (id ∈ (getInstance state (blockName inst)).pending)) =
    NotionCorePayload.textItems tx.id atoms (fun _ => false) :=
  version_textItems_pending_false network reachable _ pre suffix tx position state accepted inst atoms

#print axioms version_pending_counter_before
#print axioms version_textItems_pending_false
#print axioms canonical_pending_counter_before
#print axioms canonical_textItems_pending_false
end Sal.MRDTs.Instances.NotionCoreMachineFreshText
