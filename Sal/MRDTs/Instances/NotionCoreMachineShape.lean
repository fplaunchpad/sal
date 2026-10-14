import Sal.MRDTs.Instances.NotionCoreMachineBootstrap
import Sal.MRDTs.Instances.NotionCoreMachineCanonicalCreate

/-! Strong core shape for the actual combined state. Creator admission alone
cannot establish the active-instance premise of physical update preservation;
MachineInactiveTitleBoundary gives a raw admitted countermodel. The adapter
below changes representation only, not the document interpreter. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineShape
open NotionCoreMachine
open NotionCoreSliceForest (NormalForest ProfileValid EmptyInactive profile active attached)
open NotionCorePayload (BlockKey)
open NotionCoreSpec (Address)

private theorem view_ext (a b : NotionCoreSliceForest.State)
    (blocks : a.blocks = b.blocks) (contents : a.physical = b.physical) : a = b := by
  cases a; cases b; simp_all

/-- Projection to the existing source-tree invariant's physical view. -/
def shapeView (state : State) : NotionCoreSliceForest.State := ⟨state.forest,physical state⟩
def ShapeInvariant (state : State) : Prop := NotionCoreSliceForest.Invariant (shapeView state)
def ActiveInstance (state : State) (inst : Nat) : Prop :=
  ∃ block ∈ state.forest, (active block.title).start.1 = inst

theorem initial_shape : ShapeInvariant {} := by
  simp [ShapeInvariant,shapeView,NotionCoreSliceForest.Invariant,
    NormalForest,ProfileValid,EmptyInactive,profile]

theorem seeded_shape (atoms : List Nat) : ShapeInvariant (NotionCoreMachineBootstrap.seeded atoms) := by
  simp [ShapeInvariant,shapeView,NotionCoreSliceForest.Invariant,
    NotionCoreMachineBootstrap.seeded,NormalForest,ProfileValid,EmptyInactive,profile,
    NotionCoreSliceForest.freshTitle,NotionCoreSliceForest.titleRef,active,attached,
    NotionCoreSliceForest.Tree.children,NotionCoreSliceForest.Tree.slice,
    NotionCoreSliceForest.Normal.own]

/-- Actual bootstrap execution establishes stronger shape for empty and
nonempty initial text alike. -/
theorem bootstrap_shape (atoms : List Nat) :
    ∃ state, applyTransaction {} (NotionCorePayload.bootstrap atoms) = some state ∧ ShapeInvariant state :=
  ⟨NotionCoreMachineBootstrap.seeded atoms,NotionCoreMachineBootstrap.bootstrap_executes atoms,seeded_shape atoms⟩

/-- Literal fresh create supplies exactly the old source-tree create view. -/
theorem fresh_create_view (state result : State) (block : BlockKey) (afterBlock : Option BlockKey)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName block)
    (freshBlock : ∀ old ∈ state.forest, old.id ≠ blockName block)
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
    (prior : ShapeInvariant state)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName block)
    (freshBlock : ∀ old ∈ state.forest, old.id ≠ blockName block)
    (accepted : applyOperation state (.create block afterBlock) = some result) : ShapeInvariant result := by
  unfold ShapeInvariant
  rw [fresh_create_view state result block afterBlock freshInstance freshBlock accepted]
  apply NotionCoreSliceForest.create_preserves _ _ prior
  intro member
  obtain ⟨old,present,equal⟩ := List.mem_map.mp member
  exact freshBlock old present equal

theorem canonical_create_shape (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state result : State) (acceptedPrefix : replay {} pre = some state)
    (prior : ShapeInvariant state) (afterBlock : Option BlockKey)
    (created : applyOperation state (.create (.issued tx.id) afterBlock) = some result) : ShapeInvariant result := by
  obtain ⟨freshInstance,freshBlock⟩ := NotionCoreMachineCanonicalCreate.canonical_destination_fresh
    network reachable peer pre suffix tx position state acceptedPrefix
  exact fresh_create_shape_preserves state result (.issued tx.id) afterBlock prior freshInstance freshBlock created

theorem fresh_create_active (state result : State) (block : BlockKey) (afterBlock : Option BlockKey)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName block)
    (freshBlock : ∀ old ∈ state.forest, old.id ≠ blockName block)
    (accepted : applyOperation state (.create block afterBlock) = some result)
    (inst : Nat) (owned : ActiveInstance state inst) : ActiveInstance result inst := by
  obtain ⟨owner,present,equal⟩ := owned
  have shape := NotionCoreMachineCanonicalCreate.fresh_create_shape state result block afterBlock
    freshInstance freshBlock accepted
  refine ⟨owner,?_,equal⟩
  rw [shape.2.1]
  exact List.mem_append_left _ present

/-- Actual structural atomic split retains every old active instance and adds
no new one: the destination inherits the selected source's instance. This is
an accepted-tree-phase theorem, not replay progress or issuer-selection proof. -/
theorem atomic_split_active (physical : Nat → List NotionCoreSource.Atom)
    (marker : Address) (target : Nat) (forest result : NotionCoreSliceForest.Forest)
    (normal : NormalForest forest) (fresh : NotionCoreSliceForest.FreshMarker forest marker)
    (freshTarget : target ∉ forest.map NotionCoreSliceForest.Block.id)
    (inactiveEmpty : ∀ block ∈ forest, attached block.title = true →
      NotionCoreSliceForest.contains physical (NotionCoreSliceForest.titleRef block.id) marker = false)
    (empty : physical target = NotionCoreSliceForest.emptyPhysical target)
    (accepted : NotionCoreSliceForest.atomicSplit physical marker target forest = some result)
    (inst : Nat) :
    (∃ block ∈ result, (active block.title).start.1 = inst) ↔
      ∃ block ∈ forest, (active block.title).start.1 = inst := by
  obtain ⟨remaining,source,member,_,sameProfile,selected,shape⟩ :=
    NotionCoreSliceForest.atomicSplit_result physical marker target forest result normal fresh freshTarget
      inactiveEmpty empty accepted
  have sameInstance : (active source.title).start.1 = marker.1 := by
    have both : decide ((active source.title).start.1 = marker.1) = true ∧ _ :=
      Bool.and_eq_true_iff.mp selected
    have first := both.1
    simpa only [decide_eq_true_eq] using first
  have markerOld : ∃ block ∈ forest, (active block.title).start.1 = marker.1 :=
    ⟨source,member,sameInstance⟩
  have preserve : ∀ key,
      (∃ block ∈ remaining, (active block.title).start.1 = key) ↔
        ∃ block ∈ forest, (active block.title).start.1 = key := by
    intro key
    have mapped := congrArg (fun ps => ps.map (fun p => p.2.1.1)) sameProfile
    have instances : remaining.map (fun b => (active b.title).start.1) =
        forest.map (fun b => (active b.title).start.1) := by
      simpa only [profile,List.map_map,Function.comp_def] using mapped
    have membership := congrArg (fun values => key ∈ values) instances
    simpa only [List.mem_map] using Iff.of_eq membership
  rw [shape]
  constructor
  · rintro ⟨block,present,equal⟩
    rcases List.mem_append.mp present with old | newest
    · exact (preserve inst).mp ⟨block,old,equal⟩
    · have blockEq := List.mem_singleton.mp newest
      subst block
      have markerEq : marker.1 = inst := equal
      exact markerEq ▸ markerOld
  · intro old
    obtain ⟨block,present,equal⟩ := (preserve inst).mpr old
    exact ⟨block,List.mem_append_left _ present,equal⟩

theorem active_instance_names (state : State) (prior : ShapeInvariant state)
    (inst : Nat) (owned : ActiveInstance state inst) : inst ∈ state.forest.map NotionCoreSliceForest.Block.id := by
  obtain ⟨block,member,equal⟩ := owned
  have selected : (block.id,(active block.title).start,attached block.title) ∈ profile state.forest :=
    List.mem_map.mpr ⟨block,member,rfl⟩
  have present := (prior.2.1.2 _ selected).1
  rw [equal] at present
  simpa only [profile,List.map_map,Function.comp_def] using present

/-- Combined with atomic_split_active, a fresh split destination's own name
cannot become an active text instance after the complete structural split. -/
theorem fresh_name_not_active (state : State) (prior : ShapeInvariant state) (fresh : Nat)
    (absent : fresh ∉ state.forest.map NotionCoreSliceForest.Block.id) : ¬ ActiveInstance state fresh := by
  intro owned
  exact absent (active_instance_names state prior fresh owned)

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
owned by an active interval, rather than an unused attached block title. -/
theorem put_active_preserves (state : State) (inst : Nat) (value : Instance)
    (prior : ShapeInvariant state) (activeInstance : ActiveInstance state inst) :
    ShapeInvariant (putInstance state inst value) := by
  unfold ShapeInvariant
  rw [put_shape_view]
  exact NotionCoreSliceForest.updateInstance_preserves _ inst _ prior activeInstance

/-- Before tree splitting, raw marker integration is an active-instance put.
The theorem does not assert NormalForest for the transient tree-split phase. -/
theorem raw_marker_shape_preserves (state : State) (inst : BlockKey)
    (rows : NotionCoreParentMap.Table) (prior : ShapeInvariant state)
    (activeInstance : ActiveInstance state (blockName inst)) :
    ShapeInvariant (putInstance state (blockName inst) {getInstance state (blockName inst) with rows := rows}) :=
  put_active_preserves state (blockName inst) _ prior activeInstance

theorem inactive_title_rejects (state : State) (prior : ShapeInvariant state)
    (block : NotionCoreSliceForest.Block) (member : block ∈ state.forest)
    (inactive : attached block.title = true) (marker : Address) :
    NotionCoreSliceForest.contains (physical state) (NotionCoreSliceForest.titleRef block.id) marker = false := by
  have selected : (block.id,(active block.title).start,attached block.title) ∈ profile state.forest :=
    List.mem_map.mpr ⟨block,member,rfl⟩
  have empty : physical state block.id = NotionCoreSliceForest.emptyPhysical block.id :=
    prior.2.2 _ selected inactive
  exact NotionCoreSliceForest.empty_title_rejects (physical state) block.id marker empty

/-- Compose raw active-instance marker integration with the actual structural
atomic tree split. The fresh title already exists in raw storage; recreating
it in the source-tree adapter is a physical no-op because it is still empty. -/
theorem atomic_split_shape_preserves (old raw : State) (target : Nat) (marker : Address)
    (forest : NotionCoreSliceForest.Forest) (oldInvariant : ShapeInvariant old)
    (rawForest : raw.forest = old.forest ++ [⟨target,NotionCoreSliceForest.freshTitle target⟩])
    (rawInvariant : ShapeInvariant raw)
    (empty : physical raw target = NotionCoreSliceForest.emptyPhysical target)
    (fresh : NotionCoreSliceForest.FreshMarker old.forest marker)
    (freshTarget : target ∉ old.forest.map NotionCoreSliceForest.Block.id)
    (accepted : NotionCoreSliceForest.atomicSplit (physical raw) marker target old.forest = some forest) :
    ShapeInvariant {raw with forest := forest} := by
  let base : NotionCoreSliceForest.State := ⟨old.forest,physical raw⟩
  have rawProfile : profile raw.forest = profile old.forest ++ [(target,(target,.start),false)] := by
    rw [rawForest]
    simp [profile,NotionCoreSliceForest.freshTitle,NotionCoreSliceForest.titleRef,
      active,attached,NotionCoreSliceForest.Tree.children,NotionCoreSliceForest.Tree.slice]
  have baseInvariant : NotionCoreSliceForest.Invariant base := by
    refine ⟨oldInvariant.1,oldInvariant.2.1,?_⟩
    intro current member inactive
    exact rawInvariant.2.2 current (rawProfile ▸ List.mem_append_left _ member) inactive
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
    baseInvariant fresh freshTarget executed

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
#print axioms inactive_title_rejects
end Sal.MRDTs.Instances.NotionCoreMachineShape
