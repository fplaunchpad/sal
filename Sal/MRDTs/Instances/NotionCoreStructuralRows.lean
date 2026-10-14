import Sal.MRDTs.Instances.NotionCoreStructuralFacts
import Sal.MRDTs.Instances.NotionCoreMachineTables
import Sal.MRDTs.Instances.NotionCoreMachineHonestReplay
import Sal.MRDTs.Instances.NotionCoreMachineVersionTables
import Sal.MRDTs.Instances.NotionCoreMachineClient

/-! Direct extraction of rows and tombstones from maintained immutable facts.
No transaction replay or query-answer premise occurs in this reconstruction. -/
namespace Sal.MRDTs.Instances.NotionCoreStructuralRows
open NotionCoreStructuralFacts
open NotionCorePayload (BlockKey Transaction)
open NotionCoreParentMap (Row Table)
open NotionRunAllocation (Id)

 def births (state : State) (inst : BlockKey) : Finset Row :=
  state.biUnion fun fact => match fact with
    | .birth key row => if key = inst then {row} else ∅
    | _ => ∅

def targets (state : State) (inst : BlockKey) : Finset Id :=
  state.biUnion fun fact => match fact with
    | .erased key id => if key = inst then {id} else ∅
    | _ => ∅

@[simp] theorem mem_births (state : State) (inst : BlockKey) (row : Row) :
    row ∈ births state inst ↔ Fact.birth inst row ∈ state := by
  simp only [births, Finset.mem_biUnion]
  constructor
  · rintro ⟨fact, member, selected⟩
    cases fact <;> simp_all
    split at selected <;> simp_all
  · intro member
    exact ⟨.birth inst row, member, by simp⟩

@[simp] theorem mem_targets (state : State) (inst : BlockKey) (id : Id) :
    id ∈ targets state inst ↔ Fact.erased inst id ∈ state := by
  simp only [targets, Finset.mem_biUnion]
  constructor
  · rintro ⟨fact, member, selected⟩
    cases fact <;> simp_all
    split at selected <;> simp_all
  · intro member
    exact ⟨.erased inst id, member, by simp⟩

theorem births_correspondence (txs : List Transaction) (inst : BlockKey) :
    births (ofTransactions txs) inst = (NotionCoreTableView.birthsRows txs inst).toFinset := by
  ext row
  simp [birth_correspondence]

theorem targets_correspondence (txs : List Transaction) (inst : BlockKey) :
    targets (ofTransactions txs) inst = (NotionCoreTableView.targets txs inst).toFinset := by
  ext id
  simp [erased_correspondence]

noncomputable def rows (state : State) (inst : BlockKey) : Finset Row :=
  (births state inst).image (NotionCoreParentErase.eraseRow (targets state inst).toList)

private theorem eraseRow_same_members (a b : List Id) (same : ∀ id, id ∈ a ↔ id ∈ b)
    (row : Row) : NotionCoreParentErase.eraseRow a row = NotionCoreParentErase.eraseRow b row := by
  cases row with
  | mk item origin => cases item with
    | mk id kind => cases kind <;> simp [NotionCoreParentErase.eraseRow, NotionCoreParentErase.eraseItem, same]

/-- The complete direct row set equals the actual interpreter's retrospective
row invariant. Only the storage enumeration order is erased. -/
theorem rows_correspondence (txs : List Transaction) (inst : BlockKey) :
    rows (ofTransactions txs) inst = (NotionCoreTableView.rows txs inst).toFinset := by
  unfold rows
  rw [births_correspondence, targets_correspondence]
  have changeTargets : NotionCoreParentErase.eraseRow
      (NotionCoreTableView.targets txs inst).toFinset.toList =
      NotionCoreParentErase.eraseRow (NotionCoreTableView.targets txs inst) := by
    funext row
    exact eraseRow_same_members _ _ (by intro id; simp) row
  rw [changeTargets]
  ext row
  simp [NotionCoreTableView.rows, NotionCoreParentErase.erase]

/-- Connection to the unchanged checked interpreter, under its established
birth uniqueness and successful execution premises. -/
theorem actual_rows (txs : List Transaction) (state : NotionCoreMachine.State)
    (accepted : NotionCoreMachine.replay {} txs = some state)
    (unique : (NotionCoreMachineTables.birthIds txs).Nodup) (inst : BlockKey) :
    rows (ofTransactions txs) inst =
      (NotionCoreMachine.getInstance state (NotionCoreMachine.blockName inst)).rows.toFinset := by
  rw [(NotionCoreMachineTables.replay_tables txs state accepted unique inst).1]
  exact rows_correspondence txs inst

theorem lookup_permutation (left right : Table) (permutation : left.Perm right)
    (unique : NotionCoreParentMap.Unique right) (id : Id) :
    NotionCoreParentMap.lookup left id = NotionCoreParentMap.lookup right id := by
  cases found : NotionCoreParentMap.lookup left id with
  | none =>
    symm
    apply List.find?_eq_none.mpr
    intro row member
    exact List.find?_eq_none.mp found row (permutation.mem_iff.mpr member)
  | some row =>
    have named : row.item.id = id := by simpa [NotionCoreParentMap.lookup] using List.find?_some found
    have member : row ∈ right := permutation.mem_iff.mp (List.mem_of_find?_eq_some found)
    simpa [named] using (NotionCoreParentMap.lookup_member right row unique member).symm

theorem traverse_permutation (left right : Table) (permutation : left.Perm right)
    (unique : NotionCoreParentMap.Unique right) (fuel : Nat)
    (origin : NotionCoreOriginTree.Origin) :
    NotionCoreParentMap.traverse fuel left origin = NotionCoreParentMap.traverse fuel right origin := by
  induction fuel generalizing origin with
  | zero => rfl
  | succ fuel ih =>
    have children : NotionCoreParentMap.sortedChildren left origin =
        NotionCoreParentMap.sortedChildren right origin :=
      NotionCoreSourceInvariant.sort_permutation (permutation.filterMap _)
    simp only [NotionCoreParentMap.traverse, children]
    apply congrArg (fun f => (NotionCoreParentMap.sortedChildren right origin).flatMap f)
    funext id
    rw [lookup_permutation left right permutation unique id]
    cases NotionCoreParentMap.lookup right id <;> simp [ih]

/-- Sorting and traversing immutable rows is independent of receipt order.
The physical tree is recomputed from structure, never from transaction replay. -/
noncomputable def physical (state : State) (inst : BlockKey) : List NotionCoreSource.Atom :=
  let table := (rows state inst).toList
  NotionCorePhysicalReplay.physical (NotionCoreMachine.blockName inst)
    (NotionCoreParentMap.traverse table.length table .start)

theorem actual_physical (txs : List Transaction) (state : NotionCoreMachine.State)
    (accepted : NotionCoreMachine.replay {} txs = some state)
    (unique : (NotionCoreMachineTables.birthIds txs).Nodup) (inst : BlockKey)
    (rowUnique : NotionCoreParentMap.Unique
      (NotionCoreMachine.getInstance state (NotionCoreMachine.blockName inst)).rows) :
    physical (ofTransactions txs) inst = NotionCoreMachine.physical state (NotionCoreMachine.blockName inst) := by
  unfold physical
  rw [actual_rows txs state accepted unique inst]
  have nd := List.Nodup.of_map (fun row : Row => row.item.id) rowUnique
  have permutation := List.toFinset_toList nd
  dsimp only
  rw [permutation.length_eq]
  unfold NotionCoreMachine.physical
  rw [NotionCoreMachine.traversal_correct]
  exact congrArg _ (traverse_permutation _ _ permutation rowUnique _ _)

/-- Every honest closed archive has the same physical traversal as its direct
structural facts; acceptance and uniqueness are derived from issuance. -/
theorem honest_physical (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network)
    (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version) :
    ∃ state, NotionCoreMachine.replay {} (NotionCoreReconstruction.transactionsFor network version) = some state ∧
      ∀ inst, physical (ofTransactions (NotionCoreReconstruction.transactionsFor network version)) inst =
        NotionCoreMachine.physical state (NotionCoreMachine.blockName inst) := by
  obtain ⟨state, accepted, _⟩ :=
    NotionCoreMachineHonestReplay.honest_reconstruct_version network reachable version closed
  have payloadReach := NotionCoreCreatorNetwork.payload_reachable
    (NotionCoreMachineNetwork.creator_reachable reachable)
  refine ⟨state, accepted, fun inst => ?_⟩
  apply actual_physical _ state accepted
  · exact NotionCoreArchiveOrder.version_prefix_birth_ids_unique network payloadReach version _ []
      (by simp) _
  · exact (NotionCoreMachineVersionTables.version_table_graph network payloadReach version closed _ []
      (by simp) state accepted inst).1

/-- Decode numeric physical addresses without reconstructing transactions. -/
noncomputable def physicalName (facts : State) (name : Nat) : Option (List NotionCoreSource.Atom) :=
  (NotionCoreMachineClient.decodeBlock name).map (physical facts)

@[simp] theorem physicalName_blockName (facts : State) (inst : BlockKey) :
    physicalName facts (NotionCoreMachine.blockName inst) = some (physical facts inst) := by
  simp [physicalName]

/-- Existing numeric instances have a typed creator identity. -/
theorem physicalName_existing (txs : List Transaction) (state : NotionCoreMachine.State)
    (accepted : NotionCoreMachine.replay {} txs = some state)
    (facts : State)
    (correspondence : ∀ inst, physical facts inst =
      NotionCoreMachine.physical state (NotionCoreMachine.blockName inst))
    (name : Nat) (existing : ∃ entry ∈ state.instances, entry.1 = name) :
    physicalName facts name = some (NotionCoreMachine.physical state name) := by
  obtain ⟨entry, member, equal⟩ := existing
  have stored : name ∈ NotionCoreMachineCreators.instanceKeys state :=
    List.mem_map.mpr ⟨entry, member, equal⟩
  obtain ⟨_, _, inst, _, encoded⟩ :=
    NotionCoreMachineCreators.replay_instance_used txs state accepted name stored
  rw [encoded, physicalName_blockName, correspondence]

#print axioms physicalName_existing
#print axioms honest_physical
#print axioms rows_correspondence
#print axioms actual_rows
#print axioms actual_physical
end Sal.MRDTs.Instances.NotionCoreStructuralRows
