import Sal.MRDTs.Instances.NotionCoreMachinePartitionSplit
import Sal.MRDTs.Instances.NotionCoreMachineShape

/-! Complete actual canonical split success and joint structural preservation.
The active-instance premise concerns the old replay state. Honest client
selection supplies it in the issuer's state; transport to this canonical
prefix remains a separate history-provenance obligation. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineCanonicalSplit
open NotionCoreMachine
open NotionCoreMachinePartition (Partitioned)
open NotionCoreMachineMarkerProgress
open NotionCoreMachineShape
open NotionCorePayload (BlockKey Transaction)
open NotionCoreSliceForest (FreshMarker forestNodes)

/-- The complete create/marker/move transaction executes and restores the
partition and strong shape. No next acceptance, desired output forest,
selected owner, name freshness or recursive routing result is assumed. -/
theorem canonical_split_preserves_active_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (partitioned : Partitioned state) (shapeInvariant : ShapeInvariant state)
    (block inst : BlockKey) (origin : NotionCoreOriginTree.Origin)
    (payload : tx.payload = .split block inst origin)
    (activeInstance : ActiveInstance state (blockName inst)) :
    ∃ result, applyTransaction state tx = some result ∧
      Partitioned result ∧ ShapeInvariant result ∧
      ∀ key, ActiveInstance result key ↔ ActiveInstance state key := by
  obtain ⟨created,rows,createStep,integrated,stage,rawForest,emptyTarget,_⟩ :=
    canonical_split_marker_phase_version network reachable version closed pre suffix tx position state accepted
      partitioned block inst origin payload
  let raw := putInstance created (blockName inst)
    {getInstance created (blockName inst) with rows := rows}
  let marker := NotionCorePhysicalReplay.address (blockName inst) tx.id
  let target := blockName (.issued tx.id)
  obtain ⟨freshInstance,freshBlock⟩ := NotionCoreMachineCanonicalCreate.canonical_destination_fresh_version
    network reachable version closed pre suffix tx position state accepted
  have freshTarget : target ∉ state.forest.map NotionCoreSliceForest.Block.id := by
    intro member
    obtain ⟨old,member,equal⟩ := List.mem_map.mp member
    exact freshBlock.1 old member equal
  have freshName := fresh_name_of_instance state partitioned target freshInstance
  have createShape := fresh_create_shape_preserves state created (.issued tx.id) (some block)
    shapeInvariant partitioned freshInstance freshBlock createStep
  have createActive := fresh_create_active state created (.issued tx.id) (some block)
    freshInstance freshBlock createStep (blockName inst) activeInstance
  have rawShape : ShapeInvariant raw := raw_marker_shape_preserves created inst rows createShape createActive
  have freshMarker : FreshMarker state.forest marker := by
    intro old member key
    obtain ⟨ref,inTree,equal⟩ := List.mem_map.mp key
    have oldMember : old ∈ raw.forest := by rw [rawForest]; exact List.mem_append_left _ member
    exact stage.fresh (old.id,ref)
      (List.mem_flatMap.mpr ⟨old,oldMember,List.mem_map.mpr ⟨ref,inTree,rfl⟩⟩) equal
  have markerEvent : marker.2 ≠ .start := by
    simp [marker,NotionCorePhysicalReplay.address,NotionCorePhysicalReplay.localId]
  have deadRejects : ∀ dead, (dead,false) ∈ forestNodes state.forest →
      NotionCoreSliceForest.contains (physical raw) dead marker = false := by
    intro dead member
    apply dead_title_rejects raw rawShape dead _ marker
    rw [rawForest,NotionCoreSliceForest.forestNodes_append]
    exact List.mem_append_left _ member
  have existsInstance : ∃ entry ∈ raw.instances, entry.1 = marker.1 := by
    by_cases present : created.instances.any (fun entry => entry.1 == blockName inst) = true
    · have old : ∃ entry ∈ created.instances, entry.1 = blockName inst := by simpa using present
      exact (NotionCoreMachinePartitionUpdates.putInstance_exists_iff created
        (blockName inst) (blockName inst) _ old).mpr old
    · simp [raw,putInstance,present,marker,NotionCorePhysicalReplay.address]
  obtain ⟨forest,atomic,finalPart⟩ := NotionCoreMachinePartitionSplit.atomicSplit_partitioned
    raw state.forest marker target rawForest stage.partitioned stage.unique
      (fun found member => (shapeInvariant.1 found member).1)
      freshMarker freshTarget emptyTarget existsInstance stage.present stage.fresh
  refine ⟨{raw with forest := forest},
    split_transaction_of_atomic state created tx block inst origin rows forest payload createStep
      integrated stage rawForest atomic,finalPart,?_⟩
  constructor
  · exact atomic_split_shape_preserves state raw target marker forest shapeInvariant rawForest rawShape
      emptyTarget freshMarker markerEvent freshName atomic
  · intro key
    exact atomic_split_active (physical raw) marker target state.forest forest shapeInvariant.1
      freshMarker freshTarget emptyTarget markerEvent deadRejects atomic key

theorem canonical_split_preserves_active (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (partitioned : Partitioned state) (shapeInvariant : ShapeInvariant state)
    (block inst : BlockKey) (origin : NotionCoreOriginTree.Origin)
    (payload : tx.payload = .split block inst origin)
    (activeInstance : ActiveInstance state (blockName inst)) :
    ∃ result, applyTransaction state tx = some result ∧
      Partitioned result ∧ ShapeInvariant result ∧
      ∀ key, ActiveInstance result key ↔ ActiveInstance state key := by
  have issued := NotionCorePayloadNetwork.forget_reachable (NotionCoreCreatorNetwork.payload_reachable reachable)
  exact canonical_split_preserves_active_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed issued peer) pre suffix tx position state accepted partitioned shapeInvariant
    block inst origin payload activeInstance

/-- Compatibility projection retaining just transaction success and the two
structural invariants. The strengthened theorem also classifies active instances. -/
theorem canonical_split_preserves_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (partitioned : Partitioned state) (shapeInvariant : ShapeInvariant state)
    (block inst : BlockKey) (origin : NotionCoreOriginTree.Origin)
    (payload : tx.payload = .split block inst origin)
    (activeInstance : ActiveInstance state (blockName inst)) :
    ∃ result, applyTransaction state tx = some result ∧
      Partitioned result ∧ ShapeInvariant result := by
  obtain ⟨result,step,part,shape,_⟩ := canonical_split_preserves_active_version network reachable version closed pre suffix tx
    position state accepted partitioned shapeInvariant block inst origin payload activeInstance
  exact ⟨result,step,part,shape⟩

/-- Compatibility projection retaining just transaction success and the two
structural invariants. The strengthened theorem also classifies active instances. -/
theorem canonical_split_preserves (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (partitioned : Partitioned state) (shapeInvariant : ShapeInvariant state)
    (block inst : BlockKey) (origin : NotionCoreOriginTree.Origin)
    (payload : tx.payload = .split block inst origin)
    (activeInstance : ActiveInstance state (blockName inst)) :
    ∃ result, applyTransaction state tx = some result ∧
      Partitioned result ∧ ShapeInvariant result := by
  have issued := NotionCorePayloadNetwork.forget_reachable (NotionCoreCreatorNetwork.payload_reachable reachable)
  exact canonical_split_preserves_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed issued peer) pre suffix tx position state accepted partitioned shapeInvariant
    block inst origin payload activeInstance

/-- A merge transaction always executes: it moves a whole chain, so the
partition (with owners recomputed), the strong shape, and the live instances
are all unchanged. -/
theorem merge_preserves_active (state : State) (tx : Transaction) (source inst : BlockKey)
    (stop : Option NotionRunAllocation.Id) (payload : tx.payload = .merge source inst stop)
    (partitioned : Partitioned state) (shapeInvariant : ShapeInvariant state)
    (unique : ∀ inst, ((physical state inst).map NotionCoreSource.Atom.address).Nodup) :
    ∃ result, applyTransaction state tx = some result ∧
      Partitioned result ∧ ShapeInvariant result ∧
      ∀ key, ActiveInstance result key ↔ ActiveInstance state key := by
  refine ⟨{state with forest := (NotionCoreSliceForest.mergeForest state.forest
    (blockName source) (mergeAnchor inst stop))},?_,?_,merge_shape state source inst stop shapeInvariant,
    merge_active state source inst stop shapeInvariant⟩
  · simp [applyTransaction,NotionCorePayload.operations,payload,applyOperations,applyOperation]
  · exact NotionCoreMachinePartition.merge_partitioned state _ _ partitioned unique shapeInvariant.2.1

theorem canonical_merge_preserves_active_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (partitioned : Partitioned state) (shapeInvariant : ShapeInvariant state)
    (source inst : BlockKey) (stop : Option NotionRunAllocation.Id)
    (payload : tx.payload = .merge source inst stop) :
    ∃ result, applyTransaction state tx = some result ∧
      Partitioned result ∧ ShapeInvariant result ∧
      ∀ key, ActiveInstance result key ↔ ActiveInstance state key :=
  merge_preserves_active state tx source inst stop payload partitioned shapeInvariant
    (canonical_physical_unique_all_version network (NotionCoreCreatorNetwork.payload_reachable reachable)
      version closed pre (tx :: suffix) position state accepted)

theorem canonical_merge_preserves_active (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (partitioned : Partitioned state) (shapeInvariant : ShapeInvariant state)
    (source inst : BlockKey) (stop : Option NotionRunAllocation.Id)
    (payload : tx.payload = .merge source inst stop) :
    ∃ result, applyTransaction state tx = some result ∧
      Partitioned result ∧ ShapeInvariant result ∧
      ∀ key, ActiveInstance result key ↔ ActiveInstance state key :=
  merge_preserves_active state tx source inst stop payload partitioned shapeInvariant
    (canonical_physical_unique_all network (NotionCoreCreatorNetwork.payload_reachable reachable)
      peer pre (tx :: suffix) position state accepted)

#print axioms merge_preserves_active
#print axioms canonical_merge_preserves_active_version
#print axioms canonical_split_preserves_active_version
#print axioms canonical_split_preserves_version
#print axioms canonical_split_preserves_active

#print axioms canonical_split_preserves
end Sal.MRDTs.Instances.NotionCoreMachineCanonicalSplit
