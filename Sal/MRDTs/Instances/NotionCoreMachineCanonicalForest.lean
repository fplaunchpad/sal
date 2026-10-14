import Sal.MRDTs.Instances.NotionCoreMachineSplice
import Sal.MRDTs.Instances.NotionCoreMachineTableGraph
import Sal.MRDTs.Instances.NotionCoreMachineVersionTables

/-! Derive the actual prefix's ordered origin forest, next-origin presence and
sibling readiness from canonical issuance. No caller supplies a forest model,
parent-edge permutation, item provider or sibling-order guard. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineCanonicalForest
open NotionRunAllocation (Session Id)
open NotionCorePayload (Transaction BlockKey reservation)
open NotionCorePayloadNetwork (Reach)
open NotionCoreOriginTree (Tree Forest Origin)
open NotionCoreParentMap (ParentEdges)
open NotionCoreMachine
open NotionCoreReconstruction (transactions transactionsFor)

def originForest (state : State) (inst : BlockKey) : Forest :=
  let rows := (getInstance state (blockName inst)).rows
  NotionCoreParentMap.extract (NotionCoreParentMap.maximumCounter rows) rows .start

theorem canonical_forest_version (network : NotionCorePayloadNetwork.State) (reachable : Reach network)
    (version : List NotionRunAllocation.Run)
    (closedVersion : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version) (pre suffix : List Transaction)
    (position : transactionsFor network version = pre ++ suffix) (state : State)
    (accepted : replay {} pre = some state) (inst : BlockKey) :
    ParentEdges (getInstance state (blockName inst)).rows (originForest state inst) ∧
      NotionCoreParentCoupling.OrderedForest (originForest state inst) := by
  obtain ⟨unique, increasing, closed⟩ :=
    NotionCoreMachineVersionTables.version_table_graph network reachable version closedVersion pre suffix position state accepted inst
  exact ⟨NotionCoreExtractionEdges.extraction_edges _ unique increasing closed,
    NotionCoreMachineSplice.extraction_ordered _ unique increasing⟩

private theorem next_entry_version (network : NotionCorePayloadNetwork.State) (version : List NotionRunAllocation.Run)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : transactionsFor network version = pre ++ tx :: suffix) :
    ∃ entry ∈ network.entries, entry.tx = tx ∧
      NotionCoreIssuance.replay (NotionCorePayloadNetwork.forget network)
        version =
        pre.map reservation ++ reservation entry.tx :: suffix.map reservation := by
  obtain ⟨entry, member, same, _⟩ := NotionCoreReconstruction.transactionsFor_received network version tx
    (position ▸ List.mem_append_right pre (by simp))
  refine ⟨entry, member, same, ?_⟩
  rw [← NotionCoreReconstruction.transactionsFor_runs, position, List.map_append, List.map_cons, same]

theorem canonical_ready_version (network : NotionCorePayloadNetwork.State) (reachable : Reach network)
    (version : List NotionRunAllocation.Run)
    (closedVersion : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version) (pre suffix : List Transaction) (tx : Transaction)
    (position : transactionsFor network version = pre ++ tx :: suffix) (state : State)
    (accepted : replay {} pre = some state) (inst : BlockKey) (fresh : Tree)
    (first : fresh.item.id = tx.id) :
    NotionCoreOriginTree.Ready (NotionCorePayloadParents.payloadOrigin tx.payload) fresh
      (originForest state inst) := by
  obtain ⟨entry, member, same, runPosition⟩ := next_entry_version network version pre suffix tx position
  have edges := (canonical_forest_version network reachable version closedVersion pre (tx :: suffix) position state accepted inst).1
  have permutation := NotionCoreMachineVersionTables.version_prefix_rows_perm
    network reachable version pre (tx :: suffix) position state accepted inst
  have ready := NotionCorePayloadParents.prefix_ready_version reachable version member
    (pre.map reservation) (suffix.map reservation) runPosition inst
    (fun _ id => decide (id ∈ NotionCoreTableView.targets pre inst)) (originForest state inst) fresh
    (by simpa [same] using first) (permutation.symm.trans edges)
  simpa only [same] using ready

theorem canonical_reference_in_forest_version (network : NotionCorePayloadNetwork.State) (reachable : Reach network)
    (version : List NotionRunAllocation.Run)
    (closedVersion : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version) (pre suffix : List Transaction) (tx : Transaction)
    (position : transactionsFor network version = pre ++ tx :: suffix) (state : State)
    (accepted : replay {} pre = some state) (inst : BlockKey) (id : Id)
    (reference : (inst,id) ∈ NotionCorePayloadNetwork.locatedReferences tx.payload) :
    NotionCorePhysicalReplay.Present (.item id) (originForest state inst) := by
  have present := NotionCoreMachineVersionTables.version_next_reference_present
    network reachable version closedVersion pre suffix tx position state accepted inst id reference
  have edges := (canonical_forest_version network reachable version closedVersion pre (tx :: suffix) position state accepted inst).1
  have member := (edges.map (fun row => row.item.id)).mem_iff.mp present
  simpa only [NotionCoreParentCoupling.forestRows_ids] using member

theorem canonical_physical_forest_version (network : NotionCorePayloadNetwork.State) (reachable : Reach network)
    (version : List NotionRunAllocation.Run)
    (closedVersion : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version) (pre suffix : List Transaction)
    (position : transactionsFor network version = pre ++ suffix) (state : State)
    (accepted : replay {} pre = some state) (inst : BlockKey) :
    physical state (blockName inst) =
      NotionCorePhysicalReplay.augmented (blockName inst) (originForest state inst) := by
  have forest := canonical_forest_version network reachable version closedVersion pre suffix position state accepted inst
  have graph := NotionCoreMachineVersionTables.version_table_graph
    network reachable version closedVersion pre suffix position state accepted inst
  have traversalEq := NotionCoreParentCoupling.edges_traversal _ _ forest.1 graph.1 forest.2
  simp only [physical, traversal_correct, traversalEq, NotionCorePhysicalReplay.augmented]

theorem canonical_insert_origin_present_version (network : NotionCorePayloadNetwork.State) (reachable : Reach network)
    (version : List NotionRunAllocation.Run)
    (closedVersion : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version) (pre suffix : List Transaction) (tx : Transaction)
    (position : transactionsFor network version = pre ++ tx :: suffix) (state : State)
    (accepted : replay {} pre = some state) (block inst : BlockKey) (origin : Origin)
    (atoms : List Nat) (payload : tx.payload = .insert block inst origin atoms) :
    NotionCorePhysicalReplay.originAddress (blockName inst) origin ∈
      (physical state (blockName inst)).map NotionCoreSource.Atom.address := by
  rw [canonical_physical_forest_version network reachable version closedVersion pre (tx :: suffix) position state accepted inst]
  apply NotionCorePhysicalReplay.origin_present_physical
  cases origin with
  | start => trivial
  | item id =>
      apply canonical_reference_in_forest_version network reachable version closedVersion pre suffix tx position state accepted inst id
      simp [payload, NotionCorePayloadNetwork.locatedReferences, NotionCorePayload.originReference]

theorem canonical_births_apart_version (network : NotionCorePayloadNetwork.State) (reachable : Reach network)
    (version : List NotionRunAllocation.Run)
    (_closedVersion : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version) (pre suffix : List Transaction) (tx : Transaction)
    (position : transactionsFor network version = pre ++ tx :: suffix) (state : State)
    (accepted : replay {} pre = some state) (inst : BlockKey)
    (deleted : BlockKey → Id → Bool) :
    List.Disjoint ((getInstance state (blockName inst)).rows.map (fun row => row.item.id))
      ((NotionCoreMachinePrefix.transactionRows tx inst deleted).map (fun row => row.item.id)) := by
  obtain ⟨entry, member, same, runPosition⟩ := next_entry_version network version pre suffix tx position
  have apart := NotionCoreMachinePrefix.prefix_transaction_apart_version reachable version member
    (pre.map reservation) (suffix.map reservation) runPosition inst
    (fun _ id => decide (id ∈ NotionCoreTableView.targets pre inst)) deleted
  have permutation := NotionCoreMachineVersionTables.version_prefix_rows_perm
    network reachable version pre (tx :: suffix) position state accepted inst
  apply List.disjoint_left.mpr
  intro id old fresh
  exact List.disjoint_left.mp apart ((permutation.map (fun row => row.item.id)).mem_iff.mp old)
    (by simpa [same] using fresh)

/-- Canonical nonempty text insertion executes with the literal source splice.
Fresh IDs, sibling dominance, exact edges and origin presence are all derived
from the actual accepted prefix and issuance, not supplied by a caller. -/
theorem canonical_insert_physical_version (network : NotionCorePayloadNetwork.State) (reachable : Reach network)
    (version : List NotionRunAllocation.Run)
    (closedVersion : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version) (pre suffix : List Transaction) (tx : Transaction)
    (position : transactionsFor network version = pre ++ tx :: suffix) (state : State)
    (accepted : replay {} pre = some state) (block inst : BlockKey) (origin : Origin)
    (atoms : List Nat) (payload : tx.payload = .insert block inst origin atoms)
    (nonempty : atoms ≠ []) :
    ∃ next, applyOperation state (.insert block inst tx.id origin atoms) = some next ∧
      physical next (blockName inst) = NotionCorePartition.spliceAfterBy NotionCoreSource.Atom.address
        (NotionCorePhysicalReplay.originAddress (blockName inst) origin)
        ((NotionCorePayload.textItems tx.id atoms
          (fun id => decide (id ∈ (getInstance state (blockName inst)).pending))).map
          (NotionCorePhysicalReplay.atom (blockName inst))) (physical state (blockName inst)) := by
  let deleted : BlockKey → Id → Bool := fun _ id =>
    decide (id ∈ (getInstance state (blockName inst)).pending)
  have notNil := NotionCoreMachineSplice.textItems_nonempty tx.id atoms (deleted inst) nonempty
  cases decoded : NotionCorePayload.textItems tx.id atoms (deleted inst) with
  | nil => exact False.elim (notNil decoded)
  | cons first rest =>
    have birthRows : NotionCoreMachinePrefix.transactionRows tx inst deleted =
        NotionCoreParentMap.runRows origin (first :: rest) := by
      simp [NotionCoreMachinePrefix.transactionRows, NotionCorePayload.births,
        NotionCorePayload.operations, payload, NotionCorePayload.Operation.births,
        List.filterMap_map, Function.comp_def, decoded]
    have freshUnique := NotionCoreMachinePrefix.transaction_rows_unique tx inst deleted
    rw [birthRows] at freshUnique
    have freshUnique' : ((first :: rest).map NotionCoreOriginTree.Item.id).Nodup := by
      simpa only [NotionCoreParentMap.Unique, NotionCoreParentCoupling.runRows_ids] using freshUnique
    have apart := canonical_births_apart_version network reachable version closedVersion pre suffix tx position state accepted inst deleted
    rw [birthRows, NotionCoreParentCoupling.runRows_ids] at apart
    have forest := canonical_forest_version network reachable version closedVersion pre (tx :: suffix) position state accepted inst
    have graph := NotionCoreMachineVersionTables.version_table_graph
      network reachable version closedVersion pre (tx :: suffix) position state accepted inst
    have firstId := NotionCoreMachineSplice.textItems_head_id tx.id atoms (deleted inst) first rest decoded
    have ready := canonical_ready_version network reachable version closedVersion pre suffix tx position state accepted inst
      (NotionCoreOriginTree.runTree first rest) (by
        cases rest <;> simpa [NotionCoreOriginTree.runTree, NotionCoreOriginTree.Tree.item] using firstId)
    have ready' : NotionCoreOriginTree.Ready origin (NotionCoreOriginTree.runTree first rest)
        (originForest state inst) := by simpa [payload, NotionCorePayloadParents.payloadOrigin] using ready
    have present : NotionCorePhysicalReplay.Present origin (originForest state inst) := by
      cases origin with
      | start => trivial
      | item id =>
          apply canonical_reference_in_forest_version network reachable version closedVersion pre suffix tx position state accepted inst id
          simp [payload, NotionCorePayloadNetwork.locatedReferences, NotionCorePayload.originReference]
    obtain ⟨next, executed, physicalEq⟩ := NotionCoreMachineSplice.insert_text_physical
      state block inst tx.id origin atoms first rest decoded (originForest state inst)
      forest.1 graph.1 forest.2 freshUnique' apart ready' present
    refine ⟨next, executed, ?_⟩
    simpa only [show (fun id => decide (id ∈ (getInstance state (blockName inst)).pending)) = deleted inst from rfl,
      decoded] using physicalEq

theorem canonical_forest (network : NotionCorePayloadNetwork.State) (reachable : Reach network)
    (peer : Session) (pre suffix : List Transaction)
    (position : transactions network peer = pre ++ suffix) (state : State)
    (accepted : replay {} pre = some state) (inst : BlockKey) :
    ParentEdges (getInstance state (blockName inst)).rows (originForest state inst) ∧
      NotionCoreParentCoupling.OrderedForest (originForest state inst) :=
  canonical_forest_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed (NotionCorePayloadNetwork.forget_reachable reachable) peer)
    pre suffix position state accepted inst

theorem canonical_ready (network : NotionCorePayloadNetwork.State) (reachable : Reach network)
    (peer : Session) (pre suffix : List Transaction) (tx : Transaction)
    (position : transactions network peer = pre ++ tx :: suffix) (state : State)
    (accepted : replay {} pre = some state) (inst : BlockKey) (fresh : Tree)
    (first : fresh.item.id = tx.id) :
    NotionCoreOriginTree.Ready (NotionCorePayloadParents.payloadOrigin tx.payload) fresh
      (originForest state inst) :=
  canonical_ready_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed (NotionCorePayloadNetwork.forget_reachable reachable) peer)
    pre suffix tx position state accepted inst fresh first

theorem canonical_reference_in_forest (network : NotionCorePayloadNetwork.State) (reachable : Reach network)
    (peer : Session) (pre suffix : List Transaction) (tx : Transaction)
    (position : transactions network peer = pre ++ tx :: suffix) (state : State)
    (accepted : replay {} pre = some state) (inst : BlockKey) (id : Id)
    (reference : (inst,id) ∈ NotionCorePayloadNetwork.locatedReferences tx.payload) :
    NotionCorePhysicalReplay.Present (.item id) (originForest state inst) :=
  canonical_reference_in_forest_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed (NotionCorePayloadNetwork.forget_reachable reachable) peer)
    pre suffix tx position state accepted inst id reference

theorem canonical_physical_forest (network : NotionCorePayloadNetwork.State) (reachable : Reach network)
    (peer : Session) (pre suffix : List Transaction)
    (position : transactions network peer = pre ++ suffix) (state : State)
    (accepted : replay {} pre = some state) (inst : BlockKey) :
    physical state (blockName inst) =
      NotionCorePhysicalReplay.augmented (blockName inst) (originForest state inst) :=
  canonical_physical_forest_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed (NotionCorePayloadNetwork.forget_reachable reachable) peer)
    pre suffix position state accepted inst

theorem canonical_insert_origin_present (network : NotionCorePayloadNetwork.State) (reachable : Reach network)
    (peer : Session) (pre suffix : List Transaction) (tx : Transaction)
    (position : transactions network peer = pre ++ tx :: suffix) (state : State)
    (accepted : replay {} pre = some state) (block inst : BlockKey) (origin : Origin)
    (atoms : List Nat) (payload : tx.payload = .insert block inst origin atoms) :
    NotionCorePhysicalReplay.originAddress (blockName inst) origin ∈
      (physical state (blockName inst)).map NotionCoreSource.Atom.address :=
  canonical_insert_origin_present_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed (NotionCorePayloadNetwork.forget_reachable reachable) peer)
    pre suffix tx position state accepted block inst origin atoms payload

theorem canonical_births_apart (network : NotionCorePayloadNetwork.State) (reachable : Reach network)
    (peer : Session) (pre suffix : List Transaction) (tx : Transaction)
    (position : transactions network peer = pre ++ tx :: suffix) (state : State)
    (accepted : replay {} pre = some state) (inst : BlockKey)
    (deleted : BlockKey → Id → Bool) :
    List.Disjoint ((getInstance state (blockName inst)).rows.map (fun row => row.item.id))
      ((NotionCoreMachinePrefix.transactionRows tx inst deleted).map (fun row => row.item.id)) :=
  canonical_births_apart_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed (NotionCorePayloadNetwork.forget_reachable reachable) peer)
    pre suffix tx position state accepted inst deleted

theorem canonical_insert_physical (network : NotionCorePayloadNetwork.State) (reachable : Reach network)
    (peer : Session) (pre suffix : List Transaction) (tx : Transaction)
    (position : transactions network peer = pre ++ tx :: suffix) (state : State)
    (accepted : replay {} pre = some state) (block inst : BlockKey) (origin : Origin)
    (atoms : List Nat) (payload : tx.payload = .insert block inst origin atoms)
    (nonempty : atoms ≠ []) :
    ∃ next, applyOperation state (.insert block inst tx.id origin atoms) = some next ∧
      physical next (blockName inst) = NotionCorePartition.spliceAfterBy NotionCoreSource.Atom.address
        (NotionCorePhysicalReplay.originAddress (blockName inst) origin)
        ((NotionCorePayload.textItems tx.id atoms
          (fun id => decide (id ∈ (getInstance state (blockName inst)).pending))).map
          (NotionCorePhysicalReplay.atom (blockName inst))) (physical state (blockName inst)) :=
  canonical_insert_physical_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed (NotionCorePayloadNetwork.forget_reachable reachable) peer)
    pre suffix tx position state accepted block inst origin atoms payload nonempty

#print axioms canonical_forest_version
#print axioms canonical_ready_version
#print axioms canonical_reference_in_forest_version
#print axioms canonical_insert_physical_version

#print axioms canonical_forest
#print axioms canonical_ready
#print axioms canonical_reference_in_forest
#print axioms canonical_births_apart
#print axioms canonical_insert_physical
end Sal.MRDTs.Instances.NotionCoreMachineCanonicalForest
