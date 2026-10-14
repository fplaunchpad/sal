import Sal.MRDTs.Instances.NotionCoreMachineDocument
import Sal.MRDTs.Instances.NotionCoreMachineClient
import Sal.MRDTs.Instances.NotionCoreMachineBlockPresence
import Sal.MRDTs.Instances.NotionCoreMachineCanonicalCreate

/-! Direct create-phase correspondence with the existing materialized document.
The search forest appends while the displayed document inserts at the requested
predecessor. This file connects those actual effects without a new interpreter. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineDocumentCreate
open NotionCoreMachine
open NotionCoreMachineDocument
open NotionCorePayload (BlockKey)
open NotionCoreSliceForest (active NormalForest)

/-- A fresh create preserves every successfully extracted old slice, including
empty inactive titles: its new storage name cannot equal an old slice instance. -/
theorem fresh_create_slice (state result : State) (key : BlockKey) (after : Option BlockKey)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName key)
    (freshBlock : ∀ old ∈ state.forest, old.id ≠ blockName key)
    (created : applyOperation state (.create key after) = some result)
    (ref : NotionCoreSliceForest.Ref) (atoms : List NotionCoreSource.Atom)
    (extracted : sliceAtoms state ref = some atoms) : sliceAtoms result ref = some atoms := by
  have storedExists := (NotionCoreMachineClient.slice_storage state ref atoms extracted).1
  have stored : state.instances.any (fun entry => entry.1 == ref.start.1) = true := by simpa using storedExists
  obtain ⟨entry,member,instanceName⟩ := storedExists
  have different : ref.start.1 ≠ blockName key := fun same => freshInstance entry member (instanceName.trans same)
  have shape := NotionCoreMachineCanonicalCreate.fresh_create_shape state result key after freshInstance freshBlock created
  have physicalEq := (NotionCoreMachineCanonicalCreate.fresh_create_physical state result key after
    freshInstance freshBlock created).2 ref.start.1 different
  have storedNext : result.instances.any (fun item => item.1 == ref.start.1) = true := by
    rw [shape.1]
    simp [List.any_append,stored]
  simpa only [sliceAtoms,physicalEq,storedNext,stored] using extracted

/-- The existing source block is unchanged by a fresh create's storage phase. -/
theorem fresh_create_block (state result : State) (key : BlockKey) (after : Option BlockKey)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName key)
    (freshBlock : ∀ old ∈ state.forest, old.id ≠ blockName key)
    (created : applyOperation state (.create key after) = some result)
    (block : NotionCoreSliceForest.Block) (source : NotionCoreSource.Block)
    (accepted : materializeBlock state block = some source) :
    materializeBlock result block = some source := by
  cases extracted : sliceAtoms state (active block.title) with
  | none => simp [materializeBlock,extracted] at accepted
  | some atoms =>
    have same := fresh_create_slice state result key after freshInstance freshBlock created _ atoms extracted
    simpa [materializeBlock,same,extracted] using accepted

/-- The newly appended tree materializes to the independent empty source root. -/
theorem fresh_create_new_block (state result : State) (key : BlockKey) (after : Option BlockKey)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName key)
    (freshBlock : ∀ old ∈ state.forest, old.id ≠ blockName key)
    (created : applyOperation state (.create key after) = some result) :
    materializeBlock result ⟨blockName key,NotionCoreSliceForest.freshTitle (blockName key)⟩ =
      some (NotionCoreSourceDocument.freshBlock (blockName key) (blockName key)) := by
  have shape := NotionCoreMachineCanonicalCreate.fresh_create_shape state result key after freshInstance freshBlock created
  have physicalEq := (NotionCoreMachineCanonicalCreate.fresh_create_physical state result key after
    freshInstance freshBlock created).1
  have stored : result.instances.any (fun item => item.1 == blockName key) = true := by
    simp [shape.1]
  have extracted := NotionCoreMachineSlices.empty_title_atoms result (blockName key) stored physicalEq
  change (sliceAtoms result (NotionCoreSliceForest.titleRef (blockName key)) >>= fun atoms =>
    some (⟨blockName key,.own,⟨(blockName key,.start),atoms⟩⟩ : NotionCoreSource.Block)) = _
  rw [extracted]
  rfl

private def lookupBlock (state : State) (bid : Nat) : Option NotionCoreSource.Block := do
  let block ← state.forest.find? (fun block => block.id == bid)
  materializeBlock state block

private theorem lookup_id (state : State) (bid : Nat) (source : NotionCoreSource.Block)
    (accepted : lookupBlock state bid = some source) : source.id = bid := by
  cases found : state.forest.find? (fun block => block.id == bid) with
  | none => simp [lookupBlock,found] at accepted
  | some block =>
    have named : block.id = bid := by simpa using List.find?_some found
    have decoded : materializeBlock state block = some source := by simpa [lookupBlock,found] using accepted
    exact (materialized_atoms state block source decoded).2.trans named

private theorem old_lookup (state result : State) (key : BlockKey) (after : Option BlockKey)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName key)
    (freshBlock : ∀ old ∈ state.forest, old.id ≠ blockName key)
    (created : applyOperation state (.create key after) = some result)
    (bid : Nat) (source : NotionCoreSource.Block) (accepted : lookupBlock state bid = some source) :
    lookupBlock result bid = some source := by
  cases found : state.forest.find? (fun block => block.id == bid) with
  | none => simp [lookupBlock,found] at accepted
  | some block =>
    have decoded : materializeBlock state block = some source := by simpa [lookupBlock,found] using accepted
    have frame := fresh_create_block state result key after freshInstance freshBlock created block source decoded
    have shape := NotionCoreMachineCanonicalCreate.fresh_create_shape state result key after freshInstance freshBlock created
    simp [lookupBlock,shape.2.1,List.find?_append,found,frame]

private theorem new_lookup (state result : State) (key : BlockKey) (after : Option BlockKey)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName key)
    (freshBlock : ∀ old ∈ state.forest, old.id ≠ blockName key)
    (created : applyOperation state (.create key after) = some result) :
    lookupBlock result (blockName key) =
      some (NotionCoreSourceDocument.freshBlock (blockName key) (blockName key)) := by
  have absent : state.forest.find? (fun block => block.id == blockName key) = none := by
    apply List.find?_eq_none.mpr
    intro block member
    simp [freshBlock block member]
  have shape := NotionCoreMachineCanonicalCreate.fresh_create_shape state result key after freshInstance freshBlock created
  have fresh := fresh_create_new_block state result key after freshInstance freshBlock created
  simp [lookupBlock,shape.2.1,List.find?_append,absent,fresh]

private theorem mapM_frame (ids : List Nat) (doc : List NotionCoreSource.Block)
    (f g : Nat → Option NotionCoreSource.Block) (accepted : ids.mapM f = some doc)
    (frame : ∀ bid source, f bid = some source → g bid = some source) : ids.mapM g = some doc := by
  induction ids generalizing doc with
  | nil => simpa using accepted
  | cons bid rest ih =>
    simp only [List.mapM_cons] at accepted
    obtain ⟨source,first,later⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨suffix,tail,same⟩ := Option.bind_eq_some_iff.mp later
    have equal : source :: suffix = doc := Option.some.inj same
    subst doc
    rw [List.mapM_cons,frame bid source first,ih suffix tail]
    rfl

private theorem mapM_insert_after (ids : List Nat) (doc : List NotionCoreSource.Block)
    (f g : Nat → Option NotionCoreSource.Block) (previous fresh : Nat) (value : NotionCoreSource.Block)
    (accepted : ids.mapM f = some doc)
    (names : ∀ bid source, f bid = some source → source.id = bid)
    (frame : ∀ bid source, f bid = some source → g bid = some source)
    (new : g fresh = some value) :
    (ids.flatMap (fun bid => if bid = previous then [bid,fresh] else [bid])).mapM g =
      some (doc.flatMap (fun block => if block.id = previous then [block,value] else [block])) := by
  induction ids generalizing doc with
  | nil => have equal : doc = [] := by simpa using accepted.symm
           subst doc; rfl
  | cons bid rest ih =>
    simp only [List.mapM_cons] at accepted
    obtain ⟨source,first,later⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨suffix,tail,same⟩ := Option.bind_eq_some_iff.mp later
    have equal : source :: suffix = doc := Option.some.inj same
    subst doc
    have tailEq := ih suffix tail
    have sourceName := names bid source first
    have headEq := frame bid source first
    by_cases chosen : bid = previous
    · rw [chosen] at headEq
      simp [List.flatMap_cons,chosen,sourceName,headEq,new,tailEq]
    · simp [List.flatMap_cons,chosen,sourceName,headEq,tailEq]

/-- Fresh actual creation simulates the existing independent source-document
create transition, including its exact display insertion order. Freshness and
predecessor existence are structural guards, not assumed output equations. -/
theorem fresh_create_document (state result : State) (key : BlockKey) (after : Option BlockKey)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName key)
    (freshBlock : ∀ old ∈ state.forest, old.id ≠ blockName key)
    (created : applyOperation state (.create key after) = some result)
    (aligned : NotionCoreMachineDisplay.Aligned state)
    (document : NotionCoreSourceDocument.Document)
    (materialized : materializeDocument state = some document)
    (predecessor : ∀ previous, after = some previous → blockName previous ∈ state.display) :
    ∃ next, materializeDocument result = some next ∧
      NotionCoreSourceDocument.step document (.create (blockName key) (blockName key) (after.map blockName)) = some next := by
  have ids := materialized_ids state document materialized
  have absent : blockName key ∉ state.display := by
    intro member
    have stored := aligned.2.mem_iff.mp member
    obtain ⟨block,present,equal⟩ := List.mem_map.mp stored
    exact freshBlock block present equal
  have filtered : state.display.filter (· != blockName key) = state.display := by
    apply List.filter_eq_self.mpr
    intro bid member
    simp only [bne_iff_ne]
    exact fun equal => absent (equal ▸ member)
  have shape := NotionCoreMachineCanonicalCreate.fresh_create_shape state result key after freshInstance freshBlock created
  have display : result.display = NotionCoreDisplayOrder.insert state.display (blockName key) (after.map blockName) := by
    simpa [filtered] using shape.2.2
  have old : state.display.mapM (lookupBlock state) = some document := materialized
  have frame := old_lookup state result key after freshInstance freshBlock created
  have new := new_lookup state result key after freshInstance freshBlock created
  cases after with
  | none =>
    refine ⟨NotionCoreSourceDocument.freshBlock (blockName key) (blockName key) :: document,?_,?_⟩
    · change result.display.mapM (lookupBlock result) = _
      rw [display]
      simp only [Option.map_none,NotionCoreDisplayOrder.insert,NotionCoreDisplayOrder.insertionIndex,
        List.take_zero,List.drop_zero,List.nil_append,List.mapM_cons,new]
      rw [mapM_frame state.display document _ _ old frame]
      rfl
    · simp [NotionCoreSourceDocument.step,ids,absent]
  | some previous =>
    have present := predecessor previous rfl
    have unique : state.display.Nodup := aligned.2.nodup_iff.mpr aligned.1
    let next := document.flatMap (fun block => if block.id = blockName previous then
      [block,NotionCoreSourceDocument.freshBlock (blockName key) (blockName key)] else [block])
    refine ⟨next,?_,?_⟩
    · change result.display.mapM (lookupBlock result) = _
      rw [display]
      simp only [Option.map_some]
      rw [NotionCoreDisplayOrder.insert_after_flatMap state.display (blockName key) (blockName previous) unique present]
      exact mapM_insert_after state.display document _ _ _ _ _ old (lookup_id state) frame new
    · simp [NotionCoreSourceDocument.step,ids,absent,present,next]

/-- The actual canonical create phase has fresh names and an available
predecessor derived from archived creators. This covers standalone create and
the create phase of split, with their literal required-block metadata. -/
theorem canonical_create_document (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (part : NotionCoreMachinePartition.Partitioned state)
    (document : NotionCoreSourceDocument.Document) (materialized : materializeDocument state = some document)
    (after : Option BlockKey)
    (required : ∀ previous, after = some previous → previous ∈ NotionCoreCreatorNetwork.requiredBlocks tx.payload) :
    ∃ result next, applyOperation state (.create (.issued tx.id) after) = some result ∧
      materializeDocument result = some next ∧
      NotionCoreSourceDocument.step document
        (.create (blockName (.issued tx.id)) (blockName (.issued tx.id)) (after.map blockName)) = some next := by
  have aligned := NotionCoreMachineDisplay.replay_aligned {} state pre
    ⟨by simp [NotionCoreDisplayOrder.names],List.Perm.refl []⟩ accepted
  obtain ⟨freshInstance,freshBlock⟩ := NotionCoreMachineCanonicalCreate.canonical_destination_fresh network
    reachable peer pre suffix tx position state accepted
  obtain ⟨result,created,_⟩ := NotionCoreMachineCanonicalCreate.canonical_create_partitioned network
    reachable peer pre suffix tx position state accepted part after
  have predecessor : ∀ previous, after = some previous → blockName previous ∈ state.display := by
    intro previous selected
    apply aligned.2.mem_iff.mpr
    exact NotionCoreMachineBlockPresence.canonical_required_block network reachable peer pre suffix tx position
      state accepted previous (required previous selected)
  obtain ⟨next,projected,step⟩ := fresh_create_document state result (.issued tx.id) after freshInstance
    freshBlock created aligned document materialized predecessor
  exact ⟨result,next,created,projected,step⟩

#print axioms canonical_create_document

#print axioms fresh_create_document

#print axioms fresh_create_slice
#print axioms fresh_create_block
#print axioms fresh_create_new_block
end Sal.MRDTs.Instances.NotionCoreMachineDocumentCreate
