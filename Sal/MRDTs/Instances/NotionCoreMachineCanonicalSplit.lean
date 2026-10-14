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
open NotionCoreSliceForest (FreshMarker)

/-- The complete create/marker/move transaction executes and restores the
partition and strong shape. No next acceptance, desired output forest,
selected owner, name freshness or recursive routing result is assumed. -/
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
  obtain ⟨created,rows,createStep,integrated,stage,rawForest,emptyTarget,_⟩ :=
    canonical_split_marker_phase network reachable peer pre suffix tx position state accepted
      partitioned block inst origin payload
  let raw := putInstance created (blockName inst)
    {getInstance created (blockName inst) with rows := rows}
  let marker := NotionCorePhysicalReplay.address (blockName inst) tx.id
  let target := blockName (.issued tx.id)
  obtain ⟨freshInstance,freshBlock⟩ := NotionCoreMachineCanonicalCreate.canonical_destination_fresh
    network reachable peer pre suffix tx position state accepted
  have freshTarget : target ∉ state.forest.map NotionCoreSliceForest.Block.id := by
    intro member
    obtain ⟨old,member,equal⟩ := List.mem_map.mp member
    exact freshBlock old member equal
  have createShape := fresh_create_shape_preserves state created (.issued tx.id) (some block)
    shapeInvariant freshInstance freshBlock createStep
  have createActive := fresh_create_active state created (.issued tx.id) (some block)
    freshInstance freshBlock createStep (blockName inst) activeInstance
  have rawShape : ShapeInvariant raw := raw_marker_shape_preserves created inst rows createShape createActive
  have freshMarker : FreshMarker state.forest marker := by
    intro old member key
    obtain ⟨ref,inTree,equal⟩ := List.mem_map.mp key
    have oldMember : old ∈ raw.forest := by rw [rawForest]; exact List.mem_append_left _ member
    exact stage.fresh (old.id,ref)
      (List.mem_flatMap.mpr ⟨old,oldMember,List.mem_map.mpr ⟨ref,inTree,rfl⟩⟩) equal
  have inactive : ∀ old ∈ state.forest, NotionCoreSliceForest.attached old.title = true →
      NotionCoreSliceForest.contains (physical raw) (NotionCoreSliceForest.titleRef old.id) marker = false := by
    intro old member attached
    apply inactive_title_rejects raw rawShape old _ attached marker
    rw [rawForest]
    exact List.mem_append_left _ member
  have existsInstance : ∃ entry ∈ raw.instances, entry.1 = marker.1 := by
    by_cases present : created.instances.any (fun entry => entry.1 == blockName inst) = true
    · have old : ∃ entry ∈ created.instances, entry.1 = blockName inst := by simpa using present
      exact (NotionCoreMachinePartitionUpdates.putInstance_exists_iff created
        (blockName inst) (blockName inst) _ old).mpr old
    · simp [raw,putInstance,present,marker,NotionCorePhysicalReplay.address]
  have distinct : marker.1 ≠ target := marker_instance_ne_empty raw (blockName inst) target tx.id
    stage.present emptyTarget
  obtain ⟨forest,atomic,finalPart⟩ := NotionCoreMachinePartitionSplit.atomicSplit_partitioned
    raw state.forest marker target rawForest stage.partitioned stage.unique shapeInvariant.1
      freshMarker freshTarget inactive emptyTarget distinct existsInstance stage.present stage.fresh
  refine ⟨{raw with forest := forest},
    split_transaction_of_atomic state created tx block inst origin rows forest payload createStep
      integrated stage rawForest atomic,finalPart,?_⟩
  constructor
  · exact atomic_split_shape_preserves state raw target marker forest shapeInvariant rawForest rawShape
      emptyTarget freshMarker freshTarget atomic
  · intro key
    exact atomic_split_active (physical raw) marker target state.forest forest shapeInvariant.1
      freshMarker freshTarget inactive emptyTarget atomic key

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
  obtain ⟨result,step,part,shape,_⟩ := canonical_split_preserves_active network reachable peer pre suffix tx
    position state accepted partitioned shapeInvariant block inst origin payload activeInstance
  exact ⟨result,step,part,shape⟩

#print axioms canonical_split_preserves_active

#print axioms canonical_split_preserves
end Sal.MRDTs.Instances.NotionCoreMachineCanonicalSplit
