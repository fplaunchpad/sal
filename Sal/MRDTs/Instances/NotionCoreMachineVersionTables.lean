import Sal.MRDTs.Instances.NotionCoreMachineTableGraph

/-! Actual table and physical uniqueness for arbitrary closed versions of one
issued archive. The chronological interpreter is unchanged. Table identities
need archive uniqueness; closure additionally uses the version's saved-past
closure, never a fabricated peer or a free row/provider assertion. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineVersionTables
open NotionRunAllocation (Run Id)
open NotionCorePayload (Transaction BlockKey reservation)
open NotionCorePayloadNetwork (State Reach forget)
open NotionCorePayloadParents (prefixRows prefix_row_member)
open NotionCoreParentMap (Table Unique Increasing Closed)
open NotionCoreMachineTableGraph (graph_of_perm)

/-- Same-instance external providers occur earlier in every closed archive
version; internal predecessors belong to the same whole transaction. -/
theorem version_prefix_closed (network : State) (reachable : Reach network)
    (version : List Run) (closed : NotionCoreIssuance.Closed (forget network).records version)
    (pre suffix : List Run) (position : NotionCoreIssuance.replay (forget network) version = pre ++ suffix)
    (inst : BlockKey) (deleted : BlockKey → Id → Bool) : Closed (prefixRows network.entries pre inst deleted) := by
  intro row member
  obtain ⟨entry,present,selected,born⟩ := (prefix_row_member _ _ _ _ _).mp member
  cases parent : row.origin with
  | start => trivial
  | item old =>
    rcases NotionCoreReplayGraph.located_birth_parent entry.tx deleted inst row born old parent with external | internal
    · obtain ⟨before,after,same⟩ := List.append_of_mem selected
      have located : NotionCoreIssuance.replay (forget network) version =
          before ++ reservation entry.tx :: (after ++ suffix) := by
        rw [position,same]
        simp [List.append_assoc]
      obtain ⟨provider,providerMember,prior,birth,_⟩ :=
        NotionCorePayloadNetwork.replay_located_provider_version reachable version closed present
          before (after ++ suffix) located external
      rw [← NotionCorePayloadNetwork.birthAddresses_deleted provider.tx deleted] at birth
      obtain ⟨value,bornProvider,addressEq⟩ := List.mem_map.mp birth
      have instEq := congrArg Prod.fst addressEq
      have idEq := congrArg Prod.snd addressEq
      refine List.mem_map.mpr ⟨value.2,?_,idEq⟩
      apply (prefix_row_member _ _ _ _ _).mpr
      refine ⟨provider,providerMember,?_,?_⟩
      · rw [same]
        exact List.mem_append_left _ prior
      · have valueEq : (inst,value.2) = value := Prod.ext instEq.symm rfl
        exact valueEq ▸ bornProvider
    · rw [← NotionCorePayloadNetwork.birthAddresses_deleted entry.tx deleted] at internal
      obtain ⟨value,bornSame,addressEq⟩ := List.mem_map.mp internal
      have instEq := congrArg Prod.fst addressEq
      have idEq := congrArg Prod.snd addressEq
      refine List.mem_map.mpr ⟨value.2,?_,idEq⟩
      apply (prefix_row_member _ _ _ _ _).mpr
      refine ⟨entry,present,selected,?_⟩
      have valueEq : (inst,value.2) = value := Prod.ext instEq.symm rfl
      exact valueEq ▸ bornSame

theorem version_prefix_graph (network : State) (reachable : Reach network)
    (version : List Run) (closed : NotionCoreIssuance.Closed (forget network).records version)
    (pre suffix : List Run) (position : NotionCoreIssuance.replay (forget network) version = pre ++ suffix)
    (inst : BlockKey) (deleted : BlockKey → Id → Bool) :
    Unique (prefixRows network.entries pre inst deleted) ∧
      Increasing (prefixRows network.entries pre inst deleted) ∧
      Closed (prefixRows network.entries pre inst deleted) :=
  ⟨NotionCoreReplayGraph.prefix_unique reachable pre inst deleted,
   NotionCoreReplayGraph.prefix_increasing reachable pre inst deleted,
   version_prefix_closed network reachable version closed pre suffix position inst deleted⟩

/-- Actual storage identities hold even before requiring saved-past closure;
archive-wide fresh births supply the generic replay table theorem. -/
theorem version_tables (network : State) (reachable : Reach network) (version : List Run)
    (pre suffix : List Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ suffix)
    (state : NotionCoreMachine.State) (accepted : NotionCoreMachine.replay {} pre = some state) :
    ∀ inst, (NotionCoreMachine.getInstance state (NotionCoreMachine.blockName inst)).rows =
        NotionCoreTableView.rows pre inst ∧
      (NotionCoreMachine.getInstance state (NotionCoreMachine.blockName inst)).pending =
        NotionCoreTableView.targets pre inst :=
  NotionCoreMachineTables.replay_tables pre state accepted
    (NotionCoreArchiveOrder.version_prefix_birth_ids_unique network reachable version pre suffix position _)

theorem version_prefix_view_perm (network : State) (reachable : Reach network) (version : List Run)
    (pre suffix : List Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ suffix) (inst : BlockKey) :
    (NotionCoreTableView.rows pre inst).Perm (prefixRows network.entries (pre.map reservation) inst
      (fun _ id => decide (id ∈ NotionCoreTableView.targets pre inst))) := by
  rw [NotionCoreTableView.rows_flatMap]
  exact NotionCoreArchiveOrder.version_prefix_rows_perm network reachable version pre suffix position inst _

theorem version_prefix_rows_perm (network : State) (reachable : Reach network) (version : List Run)
    (pre suffix : List Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ suffix)
    (state : NotionCoreMachine.State) (accepted : NotionCoreMachine.replay {} pre = some state) (inst : BlockKey) :
    ((NotionCoreMachine.getInstance state (NotionCoreMachine.blockName inst)).rows).Perm
      (prefixRows network.entries (pre.map reservation) inst
        (fun _ id => decide (id ∈ NotionCoreTableView.targets pre inst))) := by
  rw [(version_tables network reachable version pre suffix position state accepted inst).1]
  exact version_prefix_view_perm network reachable version pre suffix position inst

theorem version_view_graph (network : State) (reachable : Reach network)
    (version : List Run) (closed : NotionCoreIssuance.Closed (forget network).records version)
    (pre suffix : List Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ suffix) (inst : BlockKey) :
    Unique (NotionCoreTableView.rows pre inst) ∧ Increasing (NotionCoreTableView.rows pre inst) ∧
      Closed (NotionCoreTableView.rows pre inst) := by
  have runPosition : NotionCoreIssuance.replay (forget network) version =
      pre.map reservation ++ suffix.map reservation := by
    rw [← NotionCoreReconstruction.transactionsFor_runs,position,List.map_append]
  obtain ⟨unique,increasing,graphClosed⟩ := version_prefix_graph network reachable version closed
    (pre.map reservation) (suffix.map reservation) runPosition inst
    (fun _ id => decide (id ∈ NotionCoreTableView.targets pre inst))
  exact graph_of_perm _ _ (version_prefix_view_perm network reachable version pre suffix position inst)
    unique increasing graphClosed

theorem version_table_graph (network : State) (reachable : Reach network)
    (version : List Run) (closed : NotionCoreIssuance.Closed (forget network).records version)
    (pre suffix : List Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ suffix)
    (state : NotionCoreMachine.State) (accepted : NotionCoreMachine.replay {} pre = some state) (inst : BlockKey) :
    let rows := (NotionCoreMachine.getInstance state (NotionCoreMachine.blockName inst)).rows
    Unique rows ∧ Increasing rows ∧ Closed rows := by
  dsimp only
  rw [(version_tables network reachable version pre suffix position state accepted inst).1]
  exact version_view_graph network reachable version closed pre suffix position inst

/-- Arbitrary numeric lookup keys are covered too: actual stored keys derive
from typed replay provenance, while absent keys have only virtual START. -/
theorem version_physical_unique_all (network : State) (reachable : Reach network)
    (version : List Run) (closed : NotionCoreIssuance.Closed (forget network).records version)
    (pre suffix : List Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ suffix)
    (state : NotionCoreMachine.State) (accepted : NotionCoreMachine.replay {} pre = some state) :
    ∀ key, ((NotionCoreMachine.physical state key).map NotionCoreSource.Atom.address).Nodup := by
  intro key
  by_cases existsInstance : ∃ entry ∈ state.instances, entry.1 = key
  · obtain ⟨entry,member,equal⟩ := existsInstance
    have stored : key ∈ NotionCoreMachineCreators.instanceKeys state := List.mem_map.mpr ⟨entry,member,equal⟩
    obtain ⟨tx,inPre,inst,used,encoded⟩ := NotionCoreMachineCreators.replay_instance_used pre state accepted key stored
    rw [encoded]
    obtain ⟨unique,increasing,graphClosed⟩ := version_table_graph network reachable version closed pre suffix position state accepted inst
    exact NotionCoreMachineTableGraph.physical_ids_unique state _ unique increasing graphClosed
  · have absent : state.instances.find? (fun entry => entry.1 == key) = none := by
      apply List.find?_eq_none.mpr
      intro entry member selected
      exact existsInstance ⟨entry,member,by simpa using selected⟩
    simp [NotionCoreMachine.physical,NotionCoreMachine.getInstance,absent,NotionCoreMachine.traversal,
      NotionCorePhysicalReplay.physical,NotionCorePhysicalReplay.start,NotionCorePartition.boundary]

#print axioms version_prefix_closed
#print axioms version_tables
#print axioms version_table_graph
#print axioms version_physical_unique_all

namespace SPOT
private def a : Id := ⟨1,[65]⟩
private def x : Id := ⟨2,[65]⟩
private def child : Transaction := ⟨x,.insert .initial .initial (.item a) [88]⟩
private def childRow : NotionCoreParentMap.Row := ⟨⟨x,.text 88 false⟩,.item a⟩
private def orphan : Table := NotionCoreTableView.rows [child] .initial
/-- The whole provider-plus-child version contains a then X. Selecting only
its dependent child omits a; closed-version admission is therefore essential. -/
theorem closed_parent_control :
    NotionCoreTableView.rows [NotionCorePayload.bootstrap [97],child] .initial =
      [⟨⟨a,.text 97 false⟩,.start⟩,childRow] ∧ ¬Closed orphan := by
  constructor
  · decide +kernel
  · intro closed
    have member : childRow ∈ orphan := by decide +kernel
    have absent : a ∉ orphan.map (fun row => row.item.id) := by decide +kernel
    have present := closed childRow member
    exact absent present
end SPOT

/-- Row integration's actual duplicate/self-parent guards need only archive
freshness and increasing births. Spatial origin availability is separate. -/
theorem version_next_integrates (network : State) (reachable : Reach network) (version : List Run)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : NotionCoreMachine.State) (accepted : NotionCoreMachine.replay {} pre = some state)
    (inst : BlockKey) (freshDeleted : BlockKey → Id → Bool) :
    let table := (NotionCoreMachine.getInstance state (NotionCoreMachine.blockName inst)).rows
    let fresh := NotionCoreMachinePrefix.transactionRows tx inst freshDeleted
    NotionCoreMachine.integrateRows table fresh = some (table ++ fresh) := by
  obtain ⟨entry,member,same,_⟩ := NotionCoreReconstruction.transactionsFor_received network version tx
    (position ▸ List.mem_append_right pre (by simp))
  have runPosition : NotionCoreIssuance.replay (forget network) version =
      pre.map reservation ++ reservation entry.tx :: suffix.map reservation := by
    rw [← NotionCoreReconstruction.transactionsFor_runs,position,List.map_append,List.map_cons,same]
  have integrated := NotionCoreMachinePrefix.integrate_prefix_permutation_version reachable version member
    (pre.map reservation) (suffix.map reservation) runPosition inst
    (fun _ id => decide (id ∈ NotionCoreTableView.targets pre inst)) freshDeleted _
    (version_prefix_rows_perm network reachable version pre (tx :: suffix) position state accepted inst)
  simpa only [same] using integrated

/-- Closed versions include the exact same-instance provider of every next
located reference, and actual prefix storage contains that provider item. -/
theorem version_next_reference_present (network : State) (reachable : Reach network)
    (version : List Run) (closed : NotionCoreIssuance.Closed (forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : NotionCoreMachine.State) (accepted : NotionCoreMachine.replay {} pre = some state)
    (inst : BlockKey) (id : Id) (reference : (inst,id) ∈ NotionCorePayloadNetwork.locatedReferences tx.payload) :
    id ∈ (NotionCoreMachine.getInstance state (NotionCoreMachine.blockName inst)).rows.map (fun row => row.item.id) := by
  obtain ⟨entry,member,same,_⟩ := NotionCoreReconstruction.transactionsFor_received network version tx
    (position ▸ List.mem_append_right pre (by simp))
  have runPosition : NotionCoreIssuance.replay (forget network) version =
      pre.map reservation ++ reservation entry.tx :: suffix.map reservation := by
    rw [← NotionCoreReconstruction.transactionsFor_runs,position,List.map_append,List.map_cons,same]
  obtain ⟨provider,published,earlier,born,_⟩ := NotionCorePayloadNetwork.replay_located_provider_version
    reachable version closed member (pre.map reservation) (suffix.map reservation) runPosition (same ▸ reference)
  let deleted : BlockKey → Id → Bool := fun _ id => decide (id ∈ NotionCoreTableView.targets pre inst)
  rw [← NotionCorePayloadNetwork.birthAddresses_deleted provider.tx deleted] at born
  obtain ⟨birth,present,equal⟩ := List.mem_map.mp born
  have instanceEq := congrArg Prod.fst equal
  have idEq := congrArg Prod.snd equal
  have present' : (inst,birth.2) ∈ NotionCorePayload.births provider.tx deleted := by
    have pairEq : birth = (inst,birth.2) := Prod.ext instanceEq rfl
    exact pairEq ▸ present
  have prefixMember := (prefix_row_member network.entries (pre.map reservation) inst deleted birth.2).mpr
    ⟨provider,published,earlier,present'⟩
  have actual := (version_prefix_rows_perm network reachable version pre (tx :: suffix) position state accepted inst).mem_iff.mpr prefixMember
  exact List.mem_map.mpr ⟨birth.2,actual,idEq⟩

#print axioms version_next_integrates
#print axioms version_next_reference_present
end Sal.MRDTs.Instances.NotionCoreMachineVersionTables
