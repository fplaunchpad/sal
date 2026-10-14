import Sal.MRDTs.Instances.NotionCoreTableView
import Sal.MRDTs.Instances.NotionCoreMachineTables
import Sal.MRDTs.Instances.NotionCoreArchiveOrder
import Sal.MRDTs.Instances.NotionCoreExtractionEdges

/-! Canonical full-prefix table contents inherit the graph invariants proved
from issuance. Deletion predicates come from actual prefix targets rather than
being selected to fit a desired traversal. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineTableGraph
open NotionRunAllocation (Session Id)
open NotionCorePayload (Transaction BlockKey reservation)
open NotionCorePayloadNetwork (State Reach)
open NotionCoreParentMap (Table Unique Increasing Closed)
open NotionCoreReconstruction (transactions)

theorem prefix_view_perm (network : State) (reachable : Reach network)
    (peer : Session) (pre suffix : List Transaction)
    (position : transactions network peer = pre ++ suffix) (inst : BlockKey) :
    (NotionCoreTableView.rows pre inst).Perm
      (NotionCorePayloadParents.prefixRows network.entries (pre.map reservation) inst
        (fun _ id => decide (id ∈ NotionCoreTableView.targets pre inst))) := by
  rw [NotionCoreTableView.rows_flatMap]
  exact NotionCoreArchiveOrder.canonical_prefix_rows_perm network reachable peer pre suffix position inst _

theorem graph_of_perm (a b : Table) (permutation : a.Perm b)
    (unique : Unique b) (increasing : Increasing b) (closed : Closed b) :
    Unique a ∧ Increasing a ∧ Closed a := by
  refine ⟨(permutation.map (fun row : NotionCoreParentMap.Row => row.item.id)).nodup_iff.mpr unique, ?_, ?_⟩
  · intro row member
    exact increasing row (permutation.mem_iff.mp member)
  · intro row member
    have known := closed row (permutation.mem_iff.mp member)
    cases parent : row.origin with
    | start => trivial
    | item id =>
        simp only [parent] at known ⊢
        exact (permutation.map (fun row : NotionCoreParentMap.Row => row.item.id)).mem_iff.mpr known

theorem prefix_view_graph (network : State) (reachable : Reach network)
    (peer : Session) (pre suffix : List Transaction)
    (position : transactions network peer = pre ++ suffix) (inst : BlockKey) :
    Unique (NotionCoreTableView.rows pre inst) ∧
      Increasing (NotionCoreTableView.rows pre inst) ∧
      Closed (NotionCoreTableView.rows pre inst) := by
  have runPosition : NotionCoreIssuance.replay (NotionCorePayloadNetwork.forget network)
      (network.allocation.peers peer).received = pre.map reservation ++ suffix.map reservation := by
    rw [← NotionCoreReconstruction.transactions_runs, position, List.map_append]
  obtain ⟨unique, increasing, closed⟩ := NotionCoreReplayGraph.prefix_graph reachable peer
    (pre.map reservation) (suffix.map reservation) runPosition inst
    (fun _ id => decide (id ∈ NotionCoreTableView.targets pre inst))
  exact graph_of_perm _ _ (prefix_view_perm network reachable peer pre suffix position inst)
    unique increasing closed

/-- The machine's actual finite traversal has no repeated item IDs once its
table is a closed increasing graph. The fuel is the table length, not an
externally supplied sufficient-fuel assertion. -/
theorem traversal_ids_unique (table : Table) (unique : Unique table)
    (increasing : Increasing table) (closed : Closed table) :
    ((NotionCoreMachine.traversal table.length table .start).map
      NotionCoreOriginTree.Item.id).Nodup := by
  let forest := NotionCoreParentMap.extract (NotionCoreParentMap.maximumCounter table) table .start
  have model := NotionCoreParentMap.extract_raw_model table unique increasing
  have ids := NotionCoreExtractionEdges.model_ids_unique table unique increasing closed forest model
  rw [NotionCoreMachine.traversal_correct, NotionCoreParentMap.traversal_model table .start forest model ids]
  exact ids

theorem physical_ids_unique (state : NotionCoreMachine.State) (inst : Nat)
    (unique : Unique (NotionCoreMachine.getInstance state inst).rows)
    (increasing : Increasing (NotionCoreMachine.getInstance state inst).rows)
    (closed : Closed (NotionCoreMachine.getInstance state inst).rows) :
    ((NotionCoreMachine.physical state inst).map NotionCoreSource.Atom.address).Nodup := by
  have ids := traversal_ids_unique _ unique increasing closed
  simp only [NotionCoreMachine.physical, NotionCorePhysicalReplay.physical,
    List.map_cons, List.map_map, NotionCorePhysicalReplay.start_address,
    Function.comp_def, NotionCorePhysicalReplay.atom_address]
  change ((inst, NotionCoreSpec.LocalId.start) ::
    (NotionCoreMachine.traversal (NotionCoreMachine.getInstance state inst).rows.length
      (NotionCoreMachine.getInstance state inst).rows .start).map
        (fun item => NotionCorePhysicalReplay.address inst item.id)).Nodup
  refine List.nodup_cons.mpr ⟨?_, ?_⟩
  · simp [List.mem_map, NotionCorePhysicalReplay.address, NotionCorePhysicalReplay.localId]
  · have mapped := ids.map (NotionCorePhysicalReplay.address_injective inst)
    simpa only [List.map_map, Function.comp_def] using mapped

/-- Full fields of actual canonical-prefix tables, including pending deletes.
The only execution premise is acceptance of this prefix, not a claimed table
view, row permutation, provider witness, or acceptance of the next edit. -/
theorem canonical_tables (network : State) (reachable : Reach network)
    (peer : Session) (pre suffix : List Transaction)
    (position : transactions network peer = pre ++ suffix) (state : NotionCoreMachine.State)
    (accepted : NotionCoreMachine.replay {} pre = some state) :
    ∀ inst, (NotionCoreMachine.getInstance state (NotionCoreMachine.blockName inst)).rows =
        NotionCoreTableView.rows pre inst ∧
      (NotionCoreMachine.getInstance state (NotionCoreMachine.blockName inst)).pending =
        NotionCoreTableView.targets pre inst :=
  NotionCoreMachineTables.replay_tables pre state accepted
    (NotionCoreArchiveOrder.canonical_prefix_birth_ids_unique network reachable peer pre suffix position _)

theorem canonical_prefix_rows_perm (network : State) (reachable : Reach network)
    (peer : Session) (pre suffix : List Transaction)
    (position : transactions network peer = pre ++ suffix) (state : NotionCoreMachine.State)
    (accepted : NotionCoreMachine.replay {} pre = some state) (inst : BlockKey) :
    ((NotionCoreMachine.getInstance state (NotionCoreMachine.blockName inst)).rows).Perm
      (NotionCorePayloadParents.prefixRows network.entries (pre.map reservation) inst
        (fun _ id => decide (id ∈ NotionCoreTableView.targets pre inst))) := by
  rw [(canonical_tables network reachable peer pre suffix position state accepted inst).1]
  exact prefix_view_perm network reachable peer pre suffix position inst

theorem canonical_prefix_graph (network : State) (reachable : Reach network)
    (peer : Session) (pre suffix : List Transaction)
    (position : transactions network peer = pre ++ suffix) (state : NotionCoreMachine.State)
    (accepted : NotionCoreMachine.replay {} pre = some state) (inst : BlockKey) :
    let table := (NotionCoreMachine.getInstance state (NotionCoreMachine.blockName inst)).rows
    Unique table ∧ Increasing table ∧ Closed table := by
  dsimp only
  rw [(canonical_tables network reachable peer pre suffix position state accepted inst).1]
  exact prefix_view_graph network reachable peer pre suffix position inst

theorem canonical_physical_unique (network : State) (reachable : Reach network)
    (peer : Session) (pre suffix : List Transaction)
    (position : transactions network peer = pre ++ suffix) (state : NotionCoreMachine.State)
    (accepted : NotionCoreMachine.replay {} pre = some state) (inst : BlockKey) :
    ((NotionCoreMachine.physical state (NotionCoreMachine.blockName inst)).map
      NotionCoreSource.Atom.address).Nodup := by
  obtain ⟨unique, increasing, closed⟩ := canonical_prefix_graph network reachable peer pre suffix position state accepted inst
  exact physical_ids_unique state _ unique increasing closed

/-- Checked row integration of the next decoded transaction succeeds on the
actual machine table. Future slice routing and complete transaction success
are separate; acceptance of the next transaction is not assumed here. -/
theorem canonical_next_integrates (network : State) (reachable : Reach network)
    (peer : Session) (pre suffix : List Transaction) (tx : Transaction)
    (position : transactions network peer = pre ++ tx :: suffix) (state : NotionCoreMachine.State)
    (accepted : NotionCoreMachine.replay {} pre = some state) (inst : BlockKey)
    (freshDeleted : BlockKey → Id → Bool) :
    let table := (NotionCoreMachine.getInstance state (NotionCoreMachine.blockName inst)).rows
    let fresh := NotionCoreMachinePrefix.transactionRows tx inst freshDeleted
    NotionCoreMachine.integrateRows table fresh = some (table ++ fresh) := by
  obtain ⟨entry, member, same, _⟩ := NotionCoreReconstruction.transactions_received network peer tx
    (position ▸ List.mem_append_right pre (by simp))
  have runPosition : NotionCoreIssuance.replay (NotionCorePayloadNetwork.forget network)
      (network.allocation.peers peer).received = pre.map reservation ++ reservation entry.tx :: suffix.map reservation := by
    rw [← NotionCoreReconstruction.transactions_runs, position, List.map_append, List.map_cons, same]
  have integrated := NotionCoreMachinePrefix.integrate_prefix_permutation reachable peer member
    (pre.map reservation) (suffix.map reservation) runPosition inst
    (fun _ id => decide (id ∈ NotionCoreTableView.targets pre inst)) freshDeleted _
    (canonical_prefix_rows_perm network reachable peer pre (tx::suffix) position state accepted inst)
  simpa only [same] using integrated

/-- Every next located reference is present in the actual replayed table,
not merely in a reservation or an abstract archive view. -/
theorem canonical_next_reference_present (network : State) (reachable : Reach network)
    (peer : Session) (pre suffix : List Transaction) (tx : Transaction)
    (position : transactions network peer = pre ++ tx :: suffix) (state : NotionCoreMachine.State)
    (accepted : NotionCoreMachine.replay {} pre = some state) (inst : BlockKey) (id : Id)
    (reference : (inst,id) ∈ NotionCorePayloadNetwork.locatedReferences tx.payload) :
    id ∈ (NotionCoreMachine.getInstance state (NotionCoreMachine.blockName inst)).rows.map
      (fun row => row.item.id) := by
  obtain ⟨entry, member, same, _⟩ := NotionCoreReconstruction.transactions_received network peer tx
    (position ▸ List.mem_append_right pre (by simp))
  have runPosition : NotionCoreIssuance.replay (NotionCorePayloadNetwork.forget network)
      (network.allocation.peers peer).received = pre.map reservation ++ reservation entry.tx :: suffix.map reservation := by
    rw [← NotionCoreReconstruction.transactions_runs, position, List.map_append, List.map_cons, same]
  obtain ⟨provider, published, earlier, born, _⟩ :=
    NotionCorePayloadNetwork.replay_located_provider reachable peer member
      (pre.map reservation) (suffix.map reservation) runPosition (same ▸ reference)
  let deleted : BlockKey → Id → Bool := fun _ id => decide (id ∈ NotionCoreTableView.targets pre inst)
  rw [← NotionCorePayloadNetwork.birthAddresses_deleted provider.tx deleted] at born
  obtain ⟨birth, present, equal⟩ := List.mem_map.mp born
  have instanceEq := congrArg Prod.fst equal
  have idEq := congrArg Prod.snd equal
  have present' : (inst,birth.2) ∈ NotionCorePayload.births provider.tx deleted := by
    have pairEq : birth = (inst,birth.2) := Prod.ext instanceEq rfl
    exact pairEq ▸ present
  have prefixMember := (NotionCorePayloadParents.prefix_row_member network.entries (pre.map reservation)
    inst deleted birth.2).mpr ⟨provider, published, earlier, present'⟩
  have actual := (canonical_prefix_rows_perm network reachable peer pre (tx::suffix)
    position state accepted inst).mem_iff.mpr prefixMember
  exact List.mem_map.mpr ⟨birth.2, actual, idEq⟩

#print axioms canonical_next_reference_present
#print axioms canonical_tables
#print axioms canonical_prefix_graph
#print axioms canonical_physical_unique
#print axioms canonical_next_integrates
#print axioms prefix_view_graph
#print axioms physical_ids_unique
end Sal.MRDTs.Instances.NotionCoreMachineTableGraph
