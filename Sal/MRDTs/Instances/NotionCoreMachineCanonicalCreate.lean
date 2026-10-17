import Sal.MRDTs.Instances.NotionCoreMachineCreatorPresence
import Sal.MRDTs.Instances.NotionCoreMachinePartitionCreate

/-! Canonical next destination freshness is derived from actual prefix storage
provenance and earlier creators, not supplied absence assumptions. This closes
fresh create's partition/progress guard, not the stronger normal-form invariant. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineCanonicalCreate
open NotionRunAllocation (Id Run Session)
open NotionCorePayload (BlockKey Transaction reservation)
open NotionCorePayloadNetwork (Entry)
open NotionCoreMachine
open NotionCoreReconstruction (transactions)
open NotionCoreMachineCreatorPresence (StoredInstance)

theorem created_issued_id (tx : Transaction) (id : Id)
    (created : BlockKey.issued id ∈ NotionCoreCreatorNetwork.createdBlocks tx) : tx.id = id := by
  cases tx with
  | mk first payload => cases payload <;>
      simp [NotionCoreCreatorNetwork.createdBlocks] at created <;> simp_all

private theorem prefix_used_creator_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (position : NotionCoreReconstruction.transactionsFor network version = pre ++ suffix)
    (previous : Transaction) (present : previous ∈ pre) (key : BlockKey)
    (used : key ∈ NotionCoreMachineCreators.usedBlocks previous) :
    ∃ provider ∈ network.entries, reservation provider.tx ∈ pre.map reservation ∧
      key ∈ NotionCoreCreatorNetwork.createdBlocks provider.tx := by
  obtain ⟨entry,member,same,_⟩ := NotionCoreReconstruction.transactionsFor_received network version previous
    (position ▸ List.mem_append_left suffix present)
  rcases List.mem_append.mp used with created | required
  · exact ⟨entry,member,List.mem_map.mpr ⟨previous,present,by rw [same]⟩,same ▸ created⟩
  · obtain ⟨before,after,shape⟩ := List.mem_iff_append.mp present
    have runPosition : NotionCoreIssuance.replay (NotionCorePayloadNetwork.forget network)
        version =
        before.map reservation ++ reservation entry.tx :: (after ++ suffix).map reservation := by
      rw [← NotionCoreReconstruction.transactionsFor_runs,position,shape,List.append_assoc,
        List.cons_append,List.map_append,List.map_cons,same]
    obtain ⟨provider,published,earlier,born,_⟩ :=
      NotionCoreCreatorNetwork.replay_creator_provider_version reachable version closed member
        (before.map reservation) ((after ++ suffix).map reservation) runPosition (same ▸ required)
    refine ⟨provider,published,?_,born⟩
    rw [shape,List.map_append,List.map_cons]
    exact List.mem_append_left _ earlier

theorem canonical_destination_fresh_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state) :
    (∀ entry ∈ state.instances, entry.1 ≠ blockName (.issued tx.id)) ∧
      FreshBlock state (blockName (.issued tx.id)) := by
  have payloadReach := NotionCoreCreatorNetwork.payload_reachable reachable
  have ordered := position ▸ NotionCoreReconstruction.transactionsFor_ordered network payloadReach version
  have earlier (previous : Transaction) (present : previous ∈ pre) :
      NotionRunAllocation.Before previous.id tx.id :=
    (List.pairwise_append.mp ordered).2.2 previous present tx (by simp)
  have freshInstances : ∀ entry ∈ state.instances, entry.1 ≠ blockName (.issued tx.id) := by
    intro stored member sameName
    have keyMember : stored.1 ∈ NotionCoreMachineCreators.instanceKeys state :=
      List.mem_map.mpr ⟨stored,member,rfl⟩
    obtain ⟨previous,present,key,used,encoded⟩ :=
      NotionCoreMachineCreators.replay_instance_used pre state accepted stored.1 keyMember
    have sameKey : key = .issued tx.id := blockName_injective (encoded.symm.trans sameName)
    obtain ⟨provider,published,inPrefix,born⟩ := prefix_used_creator_version network reachable version closed pre (tx::suffix)
      position previous present key used
    have idEq : provider.tx.id = tx.id := created_issued_id provider.tx tx.id (sameKey ▸ born)
    obtain ⟨earlierTx,earlierMember,runEq⟩ := List.mem_map.mp inPrefix
    have firstEq : earlierTx.id = tx.id := (congrArg Run.first runEq).trans idEq
    have contradiction := earlier earlierTx earlierMember
    rw [firstEq] at contradiction
    exact NotionCoreSourceInvariant.before_irrefl tx.id contradiction
  have supported := (NotionCoreMachineCreatorPresence.replay_created_instances pre state accepted).1
  refine ⟨freshInstances,?_,?_⟩
  · intro block member sameName
    obtain ⟨entry,present,same⟩ := supported block.id (List.mem_append_left _ (List.mem_map.mpr ⟨block,member,rfl⟩))
    exact freshInstances entry present (same.trans sameName)
  · intro shown
    obtain ⟨entry,present,same⟩ := supported _ (List.mem_append_right _ shown)
    exact freshInstances entry present same

theorem canonical_destination_fresh (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (peer : Session)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state) :
    (∀ entry ∈ state.instances, entry.1 ≠ blockName (.issued tx.id)) ∧
      FreshBlock state (blockName (.issued tx.id)) := by
  have issued := NotionCorePayloadNetwork.forget_reachable
    (NotionCoreCreatorNetwork.payload_reachable reachable)
  exact canonical_destination_fresh_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed issued peer) pre suffix tx position state accepted

/-- Actual create phase for either a next create request or split destination.
No assumed block/instance absence or next-step acceptance enters this theorem. -/
theorem canonical_create_partitioned_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (partitioned : NotionCoreMachinePartition.Partitioned state) (afterBlock : Option BlockKey) :
    ∃ result, applyOperation state (.create (.issued tx.id) afterBlock) = some result ∧
      NotionCoreMachinePartition.Partitioned result := by
  obtain ⟨freshInstance,freshBlock⟩ := canonical_destination_fresh_version network reachable version closed pre suffix tx position state accepted
  exact NotionCoreMachinePartitionCreate.create_partitioned state (.issued tx.id) afterBlock
    partitioned freshInstance freshBlock.1

/-- Actual create phase for either a next create request or split destination.
No assumed block/instance absence or next-step acceptance enters this theorem. -/
theorem canonical_create_partitioned (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (peer : Session)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (partitioned : NotionCoreMachinePartition.Partitioned state) (afterBlock : Option BlockKey) :
    ∃ result, applyOperation state (.create (.issued tx.id) afterBlock) = some result ∧
      NotionCoreMachinePartition.Partitioned result := by
  have issued := NotionCorePayloadNetwork.forget_reachable
    (NotionCoreCreatorNetwork.payload_reachable reachable)
  exact canonical_create_partitioned_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed issued peer) pre suffix tx position state accepted partitioned afterBlock

/-- Literal state shape of a genuinely fresh source create phase. -/
theorem fresh_create_shape (state result : State) (block : BlockKey) (afterBlock : Option BlockKey)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName block)
    (freshBlock : FreshBlock state (blockName block))
    (accepted : applyOperation state (.create block afterBlock) = some result) :
    result.instances = state.instances ++ [(blockName block,({} : Instance))] ∧
      result.forest = state.forest ++ [⟨blockName block,NotionCoreSliceForest.freshTitle (blockName block)⟩] ∧
      result.display = NotionCoreDisplayOrder.insert (state.display.filter (· != blockName block))
        (blockName block) (afterBlock.map blockName) := by
  have noInstance : state.instances.any (fun entry => entry.1 == blockName block) = false := by
    apply Bool.eq_false_iff.mpr
    intro found
    obtain ⟨entry,member,equal⟩ := List.any_eq_true.mp found
    exact freshInstance entry member (by simpa using equal)
  have noBlock : state.forest.any (fun old => old.id == blockName block) = false := by
    apply Bool.eq_false_iff.mpr
    intro found
    obtain ⟨old,member,equal⟩ := List.any_eq_true.mp found
    exact freshBlock.1 old member (by simpa using equal)
  have noPutBlock : (putInstance state (blockName block) {}).forest = state.forest := by
    simp [putInstance,noInstance]
  simp only [applyOperation,freshBlock.2,noBlock,Bool.false_eq_true,if_false,noInstance,
    noPutBlock,Option.some.injEq] at accepted
  subst result
  simp [putInstance,noInstance]

/-- Fresh actual create preserves every old instance's raw physical traversal
and installs an empty START-only instance for the destination. -/
theorem fresh_create_physical (state result : State) (block : BlockKey) (afterBlock : Option BlockKey)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName block)
    (freshBlock : FreshBlock state (blockName block))
    (accepted : applyOperation state (.create block afterBlock) = some result) :
    physical result (blockName block) = NotionCoreSliceForest.emptyPhysical (blockName block) ∧
      ∀ inst, inst ≠ blockName block → physical result inst = physical state inst := by
  have absentInstance : state.instances.any (fun entry => entry.1 == blockName block) = false := by
    apply Bool.eq_false_iff.mpr
    intro found
    obtain ⟨entry,member,equal⟩ := List.any_eq_true.mp found
    exact freshInstance entry member (by simpa using equal)
  simp only [applyOperation,freshBlock.2,Bool.false_eq_true,if_false,
    absentInstance,Option.some.injEq] at accepted
  subst result
  have get (inst : Nat) : getInstance (putInstance state (blockName block) {}) inst =
      if inst = blockName block then {} else getInstance state inst :=
    NotionCoreMachineTables.getInstance_put state _ inst {}
  constructor
  · change physical (putInstance state (blockName block) {}) (blockName block) = _
    simp [physical,get,NotionCoreMachine.traversal,NotionCorePhysicalReplay.physical,
      NotionCorePhysicalReplay.start,NotionCoreSliceForest.emptyPhysical]
  · intro inst different
    change physical (putInstance state (blockName block) {}) inst = physical state inst
    simp [physical,get,different]

/-- Fresh creation adds only the new empty instance; every other actual row
and pending list is unchanged, not merely its visible text. -/
theorem fresh_create_storage (state result : State) (block : BlockKey) (afterBlock : Option BlockKey)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName block)
    (freshBlock : FreshBlock state (blockName block))
    (accepted : applyOperation state (.create block afterBlock) = some result) :
    ∀ inst, getInstance result inst = if inst = blockName block then {} else getInstance state inst := by
  have noInstance : state.instances.any (fun entry => entry.1 == blockName block) = false := by
    apply Bool.eq_false_iff.mpr
    intro found
    obtain ⟨entry,member,equal⟩ := List.any_eq_true.mp found
    exact freshInstance entry member (by simpa using equal)
  simp only [applyOperation,freshBlock.2,Bool.false_eq_true,if_false,noInstance,Option.some.injEq] at accepted
  subst result
  intro inst
  change getInstance (putInstance state (blockName block) {}) inst = _
  exact NotionCoreMachineTables.getInstance_put state _ inst {}

/-- Complete canonical create-phase output for the following marker phase. -/
theorem canonical_create_phase_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (partitioned : NotionCoreMachinePartition.Partitioned state) (afterBlock : Option BlockKey) :
    ∃ result, applyOperation state (.create (.issued tx.id) afterBlock) = some result ∧
      NotionCoreMachinePartition.Partitioned result ∧
      physical result (blockName (.issued tx.id)) =
        NotionCoreSliceForest.emptyPhysical (blockName (.issued tx.id)) ∧
      ∀ inst, getInstance result inst = if inst = blockName (.issued tx.id) then {} else getInstance state inst := by
  obtain ⟨result,step,partition⟩ := canonical_create_partitioned_version network reachable version closed pre suffix tx position
    state accepted partitioned afterBlock
  obtain ⟨freshInstance,freshBlock⟩ := canonical_destination_fresh_version network reachable version closed pre suffix tx position state accepted
  exact ⟨result,step,partition,(fresh_create_physical state result (.issued tx.id) afterBlock
    freshInstance freshBlock step).1,fresh_create_storage state result (.issued tx.id) afterBlock
    freshInstance freshBlock step⟩

theorem canonical_create_phase (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (peer : Session)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (partitioned : NotionCoreMachinePartition.Partitioned state) (afterBlock : Option BlockKey) :
    ∃ result, applyOperation state (.create (.issued tx.id) afterBlock) = some result ∧
      NotionCoreMachinePartition.Partitioned result ∧
      physical result (blockName (.issued tx.id)) =
        NotionCoreSliceForest.emptyPhysical (blockName (.issued tx.id)) ∧
      ∀ inst, getInstance result inst = if inst = blockName (.issued tx.id) then {} else getInstance state inst := by
  have issued := NotionCorePayloadNetwork.forget_reachable
    (NotionCoreCreatorNetwork.payload_reachable reachable)
  exact canonical_create_phase_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed issued peer) pre suffix tx position state accepted partitioned afterBlock

#print axioms canonical_destination_fresh_version
#print axioms canonical_create_partitioned_version
#print axioms canonical_create_phase_version
#print axioms canonical_create_phase
#print axioms canonical_destination_fresh
#print axioms canonical_create_partitioned
#print axioms fresh_create_physical
end Sal.MRDTs.Instances.NotionCoreMachineCanonicalCreate
