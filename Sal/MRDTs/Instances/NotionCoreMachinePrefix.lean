import Sal.MRDTs.Instances.NotionCoreMachineRows
import Sal.MRDTs.Instances.NotionCoreReplayGraph

/-! Typed canonical-prefix provenance discharges the combined interpreter's
checked row-integration guards. The table view is deletion-aware; deriving
that view for a whole Machine.State remains a separate execution invariant. -/
namespace Sal.MRDTs.Instances.NotionCoreMachinePrefix
open NotionRunAllocation (Id Run Session)
open NotionCorePayload
open NotionCorePayloadNetwork
open NotionCorePayloadParents
open NotionCoreParentMap (Row Table)

def transactionRows (tx : Transaction) (inst : BlockKey)
    (deleted : BlockKey → Id → Bool) : Table :=
  (births tx deleted).filterMap fun birth => if birth.1 = inst then some birth.2 else none

theorem transaction_row_member (tx : Transaction) (inst : BlockKey)
    (deleted : BlockKey → Id → Bool) (row : Row) :
    row ∈ transactionRows tx inst deleted ↔ (inst, row) ∈ births tx deleted := by
  simp only [transactionRows, List.mem_filterMap]
  constructor
  · rintro ⟨birth, member, selected⟩
    split at selected
    · rename_i same
      have equal : birth = (inst, row) := Prod.ext same (Option.some.inj selected)
      exact equal ▸ member
    · contradiction
  · intro member
    exact ⟨(inst, row), member, by simp⟩

private theorem rowIds_sublist (values : List Birth) (inst : BlockKey) :
    ((values.filterMap fun birth => if birth.1 = inst then some birth.2 else none).map
      (fun row => row.item.id)).Sublist (values.map birthId) := by
  induction values with
  | nil => exact .slnil
  | cons value rest ih =>
      by_cases same : value.1 = inst
      · simpa [same, birthId] using List.Sublist.cons₂ value.2.item.id ih
      · simpa [same] using List.Sublist.cons (birthId value) ih

theorem transaction_rows_unique (tx : Transaction) (inst : BlockKey)
    (deleted : BlockKey → Id → Bool) :
    NotionCoreParentMap.Unique (transactionRows tx inst deleted) :=
  (rowIds_sublist (births tx deleted) inst).nodup (birth_ids_unique tx deleted)

theorem transaction_rows_increasing {state : State} (reachable : Reach state)
    {entry : Entry} (member : entry ∈ state.entries) (inst : BlockKey)
    (deleted : BlockKey → Id → Bool) :
    NotionCoreParentMap.Increasing (transactionRows entry.tx inst deleted) := by
  intro row present
  apply NotionCoreReplayGraph.prefix_increasing reachable [reservation entry.tx] inst deleted row
  apply (prefix_row_member _ _ _ _ _).mpr
  exact ⟨entry, member, by simp, (transaction_row_member _ _ _ _).mp present⟩

/-- Whole-reservation provenance makes every next birth fresh against the
actual prefix births, even when prefix rows have already been tombstoned. -/
theorem prefix_transaction_apart {state : State} (reachable : Reach state) (peer : Session)
    {entry : Entry} (member : entry ∈ state.entries) (pre suffix : List Run)
    (position : NotionCoreIssuance.replay (forget state) (state.allocation.peers peer).received =
      pre ++ reservation entry.tx :: suffix)
    (inst : BlockKey) (oldDeleted freshDeleted : BlockKey → Id → Bool) :
    List.Disjoint ((prefixRows state.entries pre inst oldDeleted).map (fun row => row.item.id))
      ((transactionRows entry.tx inst freshDeleted).map (fun row => row.item.id)) := by
  apply List.disjoint_left.mpr
  intro id oldBirth newBirth
  obtain ⟨oldRow, oldPresent, oldId⟩ := List.mem_map.mp oldBirth
  obtain ⟨newRow, newPresent, newId⟩ := List.mem_map.mp newBirth
  obtain ⟨old, oldMember, earlier, oldBorn⟩ := (prefix_row_member _ _ _ _ _).mp oldPresent
  have newBorn := (transaction_row_member _ _ _ _).mp newPresent
  have oldContains := ((born_iff_record old.tx old.past oldDeleted id).mp
    (List.mem_map.mpr ⟨(inst, oldRow), oldBorn, oldId⟩)).2
  have newContains := ((born_iff_record entry.tx entry.past freshDeleted id).mp
    (List.mem_map.mpr ⟨(inst, newRow), newBorn, newId⟩)).2
  have reachable' := forget_reachable reachable
  have oldPublished := NotionCoreIssuance.record_published reachable'
    (List.mem_map.mpr ⟨old, oldMember, rfl⟩)
  have newPublished := NotionCoreIssuance.record_published reachable'
    (List.mem_map.mpr ⟨entry, member, rfl⟩)
  have equal := NotionRunAllocation.reachable_unique_owner
    (NotionCoreIssuance.allocation_reachable reachable')
    (reservation old.tx) oldPublished (reservation entry.tx) newPublished id oldContains newContains
  have ordered := position ▸ NotionCoreIssuance.replay_ordered reachable' (state.allocation.peers peer).received
  have before := (List.pairwise_append.mp ordered).2.2 (reservation old.tx) earlier (reservation entry.tx) (by simp)
  rw [equal] at before
  exact NotionCoreSourceInvariant.before_irrefl _ before

/-- The actual interpreter's duplicate and self-origin checks accept the next
payload's rows. No accepted-step or desired update equation is a premise. -/
theorem integrate_canonical_prefix {state : State} (reachable : Reach state) (peer : Session)
    {entry : Entry} (member : entry ∈ state.entries) (pre suffix : List Run)
    (position : NotionCoreIssuance.replay (forget state) (state.allocation.peers peer).received =
      pre ++ reservation entry.tx :: suffix)
    (inst : BlockKey) (oldDeleted freshDeleted : BlockKey → Id → Bool) :
    NotionCoreMachine.integrateRows (prefixRows state.entries pre inst oldDeleted)
      (transactionRows entry.tx inst freshDeleted) =
    some (prefixRows state.entries pre inst oldDeleted ++ transactionRows entry.tx inst freshDeleted) :=
  NotionCoreMachineRows.integrateRows_increasing _ _
    (transaction_rows_unique entry.tx inst freshDeleted)
    (prefix_transaction_apart reachable peer member pre suffix position inst oldDeleted freshDeleted)
    (transaction_rows_increasing reachable member inst freshDeleted)


/-- Table enumeration is immaterial to checked acceptance. A combined-state
invariant can supply this structural row permutation without assuming a view. -/
theorem integrate_prefix_permutation {state : State} (reachable : Reach state) (peer : Session)
    {entry : Entry} (member : entry ∈ state.entries) (pre suffix : List Run)
    (position : NotionCoreIssuance.replay (forget state) (state.allocation.peers peer).received =
      pre ++ reservation entry.tx :: suffix)
    (inst : BlockKey) (oldDeleted freshDeleted : BlockKey → Id → Bool) (rows : Table)
    (represented : rows.Perm (prefixRows state.entries pre inst oldDeleted)) :
    NotionCoreMachine.integrateRows rows (transactionRows entry.tx inst freshDeleted) =
      some (rows ++ transactionRows entry.tx inst freshDeleted) := by
  apply NotionCoreMachineRows.integrateRows_increasing
  · exact transaction_rows_unique entry.tx inst freshDeleted
  · have apart := prefix_transaction_apart reachable peer member pre suffix position inst oldDeleted freshDeleted
    apply List.disjoint_left.mpr
    intro id memberOld memberNew
    exact List.disjoint_left.mp apart ((represented.map (fun row => row.item.id)).mem_iff.mp memberOld) memberNew
  · exact transaction_rows_increasing reachable member inst freshDeleted

private def a : Id := ⟨1,[65]⟩
private def b : Id := ⟨2,[65]⟩
private def x : Id := ⟨3,[66]⟩
private def y : Id := ⟨4,[66]⟩
private def seed : Transaction := bootstrap [97,98]
private def insertion : Transaction := ⟨x, .insert .initial .initial (.item b) [88,89]⟩
private def archive : List Entry := [⟨insertion,[reservation seed]⟩, ⟨seed,[]⟩]
private def prefixTable : Table := prefixRows archive [reservation seed] .initial
  (fun _ id => decide (id = b))

/-- PASS+FAIL: the checked loop appends two decoded births after a tombstoned
origin. The internal run child points to its predecessor rather than b. -/
theorem hidden_origin_append_control :
    NotionCoreMachine.integrateRows prefixTable
      (transactionRows insertion .initial (fun _ id => decide (id = y))) =
    some [⟨⟨a,.text 97 false⟩,.start⟩, ⟨⟨b,.text 98 true⟩,.item a⟩,
      ⟨⟨x,.text 88 false⟩,.item b⟩, ⟨⟨y,.text 89 true⟩,.item x⟩] ∧
    NotionCoreMachine.integrateRows prefixTable
      (transactionRows insertion .initial (fun _ id => decide (id = y))) ≠ some prefixTable := by decide

/-- PASS+FAIL: bootstrap's metadata creation allocates no RGA row. Its text
rows begin at the shared transaction key and occupy only the initial instance. -/
theorem bootstrap_births_control :
    transactionRows seed .initial (fun _ _ => false) =
      [⟨⟨a,.text 97 false⟩,.start⟩,⟨⟨b,.text 98 false⟩,.item a⟩] ∧
    transactionRows seed (.issued a) (fun _ _ => false) ≠
      [⟨⟨a,.text 97 false⟩,.start⟩] := by decide

#print axioms integrate_canonical_prefix
#print axioms integrate_prefix_permutation
end Sal.MRDTs.Instances.NotionCoreMachinePrefix
