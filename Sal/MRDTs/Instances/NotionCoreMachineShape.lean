import Sal.MRDTs.Instances.NotionCoreMachineBootstrap
import Sal.MRDTs.Instances.NotionCoreMachineCanonicalCreate

/-! Strong core shape for the actual combined state: chain titles and empty,
unshared dead titles. Creator admission alone cannot establish the
live-instance premise of physical update preservation;
MachineInactiveTitleBoundary gives a raw admitted countermodel. The adapter
below changes representation only, not the document interpreter. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineShape
open NotionCoreMachine
open NotionCoreSliceForest (ChainForest EmptyInactive FreshName forestNodes forestRefs)
open NotionCorePayload (BlockKey)
open NotionCoreSpec (Address)

private theorem view_ext (a b : NotionCoreSliceForest.State)
    (blocks : a.blocks = b.blocks) (contents : a.physical = b.physical) : a = b := by
  cases a; cases b; simp_all

/-- Projection to the existing source-tree invariant's physical view. -/
def shapeView (state : State) : NotionCoreSliceForest.State := ⟨state.forest,physical state⟩
def ShapeInvariant (state : State) : Prop := NotionCoreSliceForest.Invariant (shapeView state)
/-- Some live node of the forest lies in the instance. -/
def ActiveInstance (state : State) (inst : Nat) : Prop :=
  ∃ live, (live,true) ∈ forestNodes state.forest ∧ live.start.1 = inst

theorem initial_shape : ShapeInvariant {} := by
  simp [ShapeInvariant,shapeView,NotionCoreSliceForest.Invariant,
    ChainForest,EmptyInactive,forestNodes,NotionCoreSliceForest.StopsKeyed,
    NotionCoreSliceForest.AnchorsUnique,forestRefs]

theorem seeded_shape (atoms : List Nat) : ShapeInvariant (NotionCoreMachineBootstrap.seeded atoms) := by
  have refs : forestRefs (shapeView (NotionCoreMachineBootstrap.seeded atoms)).blocks =
      [NotionCoreSliceForest.titleRef 0] := by
    simp [shapeView,NotionCoreMachineBootstrap.seeded,forestRefs,NotionCoreSliceForest.freshTitle,
      NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.preorderChildren]
  refine ⟨?_,by simp [shapeView,NotionCoreMachineBootstrap.seeded],?_,?_,?_⟩
  · intro block member
    simp only [shapeView,NotionCoreMachineBootstrap.seeded,List.mem_singleton] at member
    subst block
    exact ⟨.leaf _,rfl⟩
  · intro dead member
    simp [shapeView,NotionCoreMachineBootstrap.seeded,forestNodes,NotionCoreSliceForest.freshTitle,
      NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.preorderChildren,
      NotionCoreSliceForest.nodes,NotionCoreSliceForest.tagBefore] at member
  · intro ref member stop stopped
    rw [refs] at member
    simp [List.mem_singleton.mp member,NotionCoreSliceForest.titleRef] at stopped
  · simp [NotionCoreSliceForest.AnchorsUnique,refs]

/-- Actual bootstrap execution establishes stronger shape for empty and
nonempty initial text alike. -/
theorem bootstrap_shape (atoms : List Nat) :
    ∃ state, applyTransaction {} (NotionCorePayload.bootstrap atoms) = some state ∧ ShapeInvariant state :=
  ⟨NotionCoreMachineBootstrap.seeded atoms,NotionCoreMachineBootstrap.bootstrap_executes atoms,seeded_shape atoms⟩

/-- Every forest node lies in an allocated instance, so a name with no
allocated instance is fresh for the forest. -/
theorem fresh_name_of_instance (state : State) (partitioned : NotionCoreMachinePartition.Partitioned state)
    (name : Nat) (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ name) :
    FreshName state.forest name := by
  intro ref member same
  rw [← NotionCoreForestRefs.ownedRefs_refs] at member
  obtain ⟨owned,ownedMember,rfl⟩ := List.mem_map.mp member
  obtain ⟨entry,present,instanceEq⟩ := partitioned.refsExist owned ownedMember
  exact freshInstance entry present (instanceEq.trans same)

/-- A fresh standalone root may contain arbitrary physical text. Other
instances retain their old contents, so old dead titles stay empty. This
also covers bootstrap following independent earlier creations. -/
theorem fresh_root_frame_shape (state result : State) (bid : Nat)
    (prior : ShapeInvariant state) (fresh : FreshName state.forest bid)
    (forest : result.forest = state.forest ++ [⟨bid,NotionCoreSliceForest.freshTitle bid⟩])
    (other : ∀ key, key ≠ bid → physical result key = physical state key) : ShapeInvariant result := by
  let created := NotionCoreSliceForest.create (shapeView state) bid
  have createInvariant := NotionCoreSliceForest.create_preserves (shapeView state) bid prior fresh
  have activeNew : ∃ live, (live,true) ∈ forestNodes created.blocks ∧ live.start.1 = bid := by
    refine ⟨NotionCoreSliceForest.titleRef bid,?_,rfl⟩
    simp [created,NotionCoreSliceForest.create,NotionCoreSliceForest.forestNodes_append,
      NotionCoreSliceForest.forestNodes_fresh]
  have updated := NotionCoreSliceForest.updateInstance_preserves created bid (physical result bid)
    createInvariant activeNew
  have view : shapeView result = NotionCoreSliceForest.updateInstance created bid (physical result bid) := by
    apply view_ext
    · exact forest
    · funext key
      by_cases selected : key = bid
      · subst key
        simp [shapeView,NotionCoreSliceForest.updateInstance,NotionCoreSliceForest.write]
      · simpa [shapeView,NotionCoreSliceForest.updateInstance,NotionCoreSliceForest.write,
          created,NotionCoreSliceForest.create,selected] using other key selected
  unfold ShapeInvariant
  rw [view]
  exact updated

#print axioms fresh_root_frame_shape

/-- Literal fresh create supplies exactly the old source-tree create view. -/
theorem fresh_create_view (state result : State) (block : BlockKey) (afterBlock : Option BlockKey)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName block)
    (freshBlock : FreshBlock state (blockName block))
    (accepted : applyOperation state (.create block afterBlock) = some result) :
    shapeView result = NotionCoreSliceForest.create (shapeView state) (blockName block) := by
  have shape := NotionCoreMachineCanonicalCreate.fresh_create_shape state result block afterBlock
    freshInstance freshBlock accepted
  have physicalEq := NotionCoreMachineCanonicalCreate.fresh_create_physical state result block afterBlock
    freshInstance freshBlock accepted
  apply view_ext
  · exact shape.2.1
  · funext inst
    by_cases selected : inst = blockName block
    · subst inst
      simpa [shapeView,NotionCoreSliceForest.create,NotionCoreSliceForest.write] using physicalEq.1
    · simpa [NotionCoreSliceForest.create,NotionCoreSliceForest.write,shapeView,selected]
        using physicalEq.2 inst selected

theorem fresh_create_shape_preserves (state result : State) (block : BlockKey) (afterBlock : Option BlockKey)
    (prior : ShapeInvariant state) (partitioned : NotionCoreMachinePartition.Partitioned state)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName block)
    (freshBlock : FreshBlock state (blockName block))
    (accepted : applyOperation state (.create block afterBlock) = some result) : ShapeInvariant result := by
  unfold ShapeInvariant
  rw [fresh_create_view state result block afterBlock freshInstance freshBlock accepted]
  exact NotionCoreSliceForest.create_preserves _ _ prior
    (fresh_name_of_instance state partitioned _ freshInstance)

theorem canonical_create_shape (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state result : State) (acceptedPrefix : replay {} pre = some state)
    (prior : ShapeInvariant state) (partitioned : NotionCoreMachinePartition.Partitioned state)
    (afterBlock : Option BlockKey)
    (created : applyOperation state (.create (.issued tx.id) afterBlock) = some result) : ShapeInvariant result := by
  obtain ⟨freshInstance,freshBlock⟩ := NotionCoreMachineCanonicalCreate.canonical_destination_fresh
    network reachable peer pre suffix tx position state acceptedPrefix
  exact fresh_create_shape_preserves state result (.issued tx.id) afterBlock prior partitioned
    freshInstance freshBlock created

theorem fresh_create_active (state result : State) (block : BlockKey) (afterBlock : Option BlockKey)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName block)
    (freshBlock : FreshBlock state (blockName block))
    (accepted : applyOperation state (.create block afterBlock) = some result)
    (inst : Nat) (owned : ActiveInstance state inst) : ActiveInstance result inst := by
  obtain ⟨live,member,equal⟩ := owned
  have shape := NotionCoreMachineCanonicalCreate.fresh_create_shape state result block afterBlock
    freshInstance freshBlock accepted
  refine ⟨live,?_,equal⟩
  rw [shape.2.1,NotionCoreSliceForest.forestNodes_append]
  exact List.mem_append_left _ member

/-- Actual structural atomic split retains every old live instance and adds
no new one: both halves of the cut node keep its instance, and the
destination's own title root is dead. This is an accepted-tree-phase theorem,
not replay progress or issuer-selection proof. -/
theorem atomic_split_active (physical : Nat → List NotionCoreSource.Atom)
    (marker : Address) (target : Nat) (forest result : NotionCoreSliceForest.Forest)
    (chains : ChainForest forest) (fresh : NotionCoreSliceForest.FreshMarker forest marker)
    (freshTarget : target ∉ forest.map NotionCoreSliceForest.Block.id)
    (empty : physical target = NotionCoreSliceForest.emptyPhysical target)
    (markerEvent : marker.2 ≠ .start)
    (deadRejects : ∀ dead, (dead,false) ∈ forestNodes forest →
      NotionCoreSliceForest.contains physical dead marker = false)
    (accepted : NotionCoreSliceForest.atomicSplit physical marker target forest = some result)
    (inst : Nat) :
    (∃ live, (live,true) ∈ forestNodes result ∧ live.start.1 = inst) ↔
      ∃ live, (live,true) ∈ forestNodes forest ∧ live.start.1 = inst := by
  obtain ⟨ref,refLive,inside,classify,retained,leftMember,_,_,_,_⟩ :=
    NotionCoreSliceForest.atomicSplit_nodes physical marker target forest result chains fresh freshTarget
      empty markerEvent deadRejects accepted
  have sameInstance : ref.start.1 = marker.1 :=
    (Bool.and_eq_true_iff.mp inside).1 |> of_decide_eq_true
  constructor
  · rintro ⟨live,member,rfl⟩
    rcases classify _ member with old | equal | equal | equal
    · exact ⟨live,old,rfl⟩
    · exact ⟨ref,refLive,by simp [(Prod.mk.inj equal).1,NotionCoreSliceForest.leftRef]⟩
    · simp at equal
    · exact ⟨ref,refLive,by
        rw [(Prod.mk.inj equal).1]; exact sameInstance⟩
  · rintro ⟨live,member,rfl⟩
    rcases retained _ member with kept | equal
    · exact ⟨live,kept,rfl⟩
    · obtain ⟨rfl,-⟩ := Prod.mk.inj equal
      exact ⟨_,leftMember,rfl⟩

/-- A fresh split destination's own name cannot be a live instance. -/
theorem fresh_name_not_active (state : State) (fresh : Nat)
    (absent : FreshName state.forest fresh) : ¬ ActiveInstance state fresh := by
  rintro ⟨live,member,equal⟩
  exact absent live (NotionCoreSliceForest.node_ref member) equal

/-- Actual row/pending update leaves the forest and all other physical
instances unchanged. The selected contents need not be supplied as an output
observation or satisfy a rendering contract. -/
theorem put_shape_view (state : State) (inst : Nat) (value : Instance) :
    shapeView (putInstance state inst value) =
      NotionCoreSliceForest.updateInstance (shapeView state) inst
        (physical (putInstance state inst value) inst) := by
  apply view_ext
  · unfold shapeView putInstance
    split <;> rfl
  · funext key
    by_cases selected : key = inst
    · subst key
      simp [NotionCoreSliceForest.updateInstance,NotionCoreSliceForest.write,shapeView]
    · simp [NotionCoreSliceForest.updateInstance,NotionCoreSliceForest.write,shapeView,
        physical,NotionCoreMachineTables.getInstance_put,selected]

/-- This is the exact remaining source-selection guard: update an instance
owned by a live node, rather than an unused dead title. -/
theorem put_active_preserves (state : State) (inst : Nat) (value : Instance)
    (prior : ShapeInvariant state) (activeInstance : ActiveInstance state inst) :
    ShapeInvariant (putInstance state inst value) := by
  unfold ShapeInvariant
  rw [put_shape_view]
  exact NotionCoreSliceForest.updateInstance_preserves _ inst _ prior activeInstance

/-- Before tree splitting, raw marker integration is a live-instance put.
The theorem does not assert the chain shape for the transient tree-split phase. -/
theorem raw_marker_shape_preserves (state : State) (inst : BlockKey)
    (rows : NotionCoreParentMap.Table) (prior : ShapeInvariant state)
    (activeInstance : ActiveInstance state (blockName inst)) :
    ShapeInvariant (putInstance state (blockName inst) {getInstance state (blockName inst) with rows := rows}) :=
  put_active_preserves state (blockName inst) _ prior activeInstance

theorem dead_title_rejects (state : State) (prior : ShapeInvariant state)
    (dead : NotionCoreSliceForest.Ref) (member : (dead,false) ∈ forestNodes state.forest) (marker : Address) :
    NotionCoreSliceForest.contains (physical state) dead marker = false := by
  obtain ⟨form,empty,_⟩ := prior.2.2.1 dead member
  rw [form]
  exact NotionCoreSliceForest.empty_title_rejects (physical state) _ marker empty

/-- Compose raw live-instance marker integration with the actual structural
atomic tree split. The fresh title already exists in raw storage; recreating
it in the source-tree adapter is a physical no-op because it is still empty. -/
theorem atomic_split_shape_preserves (old raw : State) (target : Nat) (marker : Address)
    (forest : NotionCoreSliceForest.Forest) (oldInvariant : ShapeInvariant old)
    (rawForest : raw.forest = old.forest ++ [⟨target,NotionCoreSliceForest.freshTitle target⟩])
    (rawInvariant : ShapeInvariant raw)
    (empty : physical raw target = NotionCoreSliceForest.emptyPhysical target)
    (fresh : NotionCoreSliceForest.FreshMarker old.forest marker)
    (markerEvent : marker.2 ≠ .start)
    (freshTarget : FreshName old.forest target)
    (accepted : NotionCoreSliceForest.atomicSplit (physical raw) marker target old.forest = some forest) :
    ShapeInvariant {raw with forest := forest} := by
  let base : NotionCoreSliceForest.State := ⟨old.forest,physical raw⟩
  have baseInvariant : NotionCoreSliceForest.Invariant base := by
    refine ⟨oldInvariant.1,oldInvariant.2.1,?_,oldInvariant.2.2.2⟩
    intro dead member
    have rawMember : (dead,false) ∈ forestNodes raw.forest := by
      rw [rawForest,NotionCoreSliceForest.forestNodes_append]
      exact List.mem_append_left _ member
    obtain ⟨form,physicalEq,lives⟩ := rawInvariant.2.2.1 dead rawMember
    refine ⟨form,physicalEq,fun live liveMember => lives live ?_⟩
    change (live,true) ∈ forestNodes raw.forest
    rw [rawForest,NotionCoreSliceForest.forestNodes_append]
    exact List.mem_append_left _ liveMember
  have createdPhysical : (NotionCoreSliceForest.create base target).physical = physical raw := by
    funext inst
    by_cases selected : inst = target
    · subst inst
      simpa [NotionCoreSliceForest.create,NotionCoreSliceForest.write] using empty.symm
    · simp [NotionCoreSliceForest.create,NotionCoreSliceForest.write,base,selected]
  have executed : NotionCoreSliceForest.split base marker target = some ⟨forest,physical raw⟩ := by
    simp only [NotionCoreSliceForest.split,createdPhysical]
    exact congrArg (fun result => result.map (fun blocks => (⟨blocks,physical raw⟩ : NotionCoreSliceForest.State))) accepted
  exact NotionCoreSliceForest.split_preserves base ⟨forest,physical raw⟩ marker target
    baseInvariant fresh markerEvent freshTarget executed

/-- Merge moves whole chains: shape and the live instances are unchanged. -/
theorem merge_shape (state : State) (source inst : BlockKey) (stop : Option NotionRunAllocation.Id)
    (prior : ShapeInvariant state) :
    ShapeInvariant {state with forest := (NotionCoreSliceForest.mergeForest state.forest
      (blockName source) (mergeAnchor inst stop))} :=
  NotionCoreSliceForest.merge_preserves (shapeView state) _ _ prior

theorem merge_active (state : State) (source key : BlockKey) (stop : Option NotionRunAllocation.Id)
    (prior : ShapeInvariant state) (inst : Nat) :
    ActiveInstance {state with forest := (NotionCoreSliceForest.mergeForest state.forest
      (blockName source) (mergeAnchor key stop))} inst ↔ ActiveInstance state inst := by
  simp only [ActiveInstance]
  constructor
  · rintro ⟨live,member,equal⟩
    exact ⟨live,(NotionCoreSliceForest.mergeForest_nodes _ _ _ prior.1 prior.2.1 _).mp member,equal⟩
  · rintro ⟨live,member,equal⟩
    exact ⟨live,(NotionCoreSliceForest.mergeForest_nodes _ _ _ prior.1 prior.2.1 _).mpr member,equal⟩

#print axioms atomic_split_shape_preserves
/-- An empty inactive title cannot intercept any marker, including START;
extraction excludes the slice's own start boundary. -/
theorem empty_title_control :
    NotionCoreSliceForest.contains NotionCoreSliceForest.emptyPhysical
      (NotionCoreSliceForest.titleRef 7) (7,.event (0,1)) = false ∧
    NotionCoreSliceForest.contains NotionCoreSliceForest.emptyPhysical
      (NotionCoreSliceForest.titleRef 7) (7,.start) ≠ true := by decide +kernel

#print axioms bootstrap_shape
#print axioms canonical_create_shape
#print axioms atomic_split_active
#print axioms fresh_name_not_active
#print axioms fresh_create_shape_preserves
#print axioms put_active_preserves
#print axioms dead_title_rejects
#print axioms merge_shape
#print axioms merge_active
end Sal.MRDTs.Instances.NotionCoreMachineShape
