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

/-- A fresh create preserves every successfully extracted old slice, including
empty inactive titles: its new storage name cannot equal an old slice instance. -/
theorem fresh_create_slice (state result : State) (key : BlockKey) (after : Option BlockKey)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName key)
    (freshBlock : FreshBlock state (blockName key))
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

private theorem mapM_frame {α β : Type} (ids : List α) (doc : List β)
    (f g : α → Option β) (accepted : ids.mapM f = some doc)
    (frame : ∀ bid ∈ ids, ∀ source, f bid = some source → g bid = some source) : ids.mapM g = some doc := by
  induction ids generalizing doc with
  | nil => simpa using accepted
  | cons bid rest ih =>
    simp only [List.mapM_cons] at accepted
    obtain ⟨source,first,later⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨suffix,tail,same⟩ := Option.bind_eq_some_iff.mp later
    have equal : source :: suffix = doc := Option.some.inj same
    subst doc
    rw [List.mapM_cons,frame bid (by simp) source first,
      ih suffix tail (fun other member => frame other (List.mem_cons_of_mem _ member))]
    rfl

/-- The existing source block is unchanged by a fresh create's storage phase. -/
theorem fresh_create_block (state result : State) (key : BlockKey) (after : Option BlockKey)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName key)
    (freshBlock : FreshBlock state (blockName key))
    (created : applyOperation state (.create key after) = some result)
    (block : NotionCoreSliceForest.Block) (source : NotionCoreSource.Block)
    (accepted : materializeBlock state block = some source) :
    materializeBlock result block = some source := by
  obtain ⟨extracted,name,instEq⟩ := materialized_slices state block source accepted
  have same : NotionCoreMachineClient.materialize result block.title = some source.slices := by
    unfold NotionCoreMachineClient.materialize at extracted ⊢
    apply mapM_frame _ _ _ _ extracted
    intro ref _ slice selected
    cases atoms : sliceAtoms state ref with
    | none => simp [atoms] at selected
    | some found =>
      simpa [fresh_create_slice state result key after freshInstance freshBlock created ref found atoms,
        atoms] using selected
  cases source
  simp only at name instEq
  subst name instEq
  simp [materializeBlock, same]

/-- The newly appended tree materializes to the independent empty source root. -/
theorem fresh_create_new_block (state result : State) (key : BlockKey) (after : Option BlockKey)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName key)
    (freshBlock : FreshBlock state (blockName key))
    (created : applyOperation state (.create key after) = some result) :
    materializeBlock result ⟨blockName key,NotionCoreSliceForest.freshTitle (blockName key)⟩ =
      some (NotionCoreSourceDocument.freshBlock (blockName key) (blockName key)) := by
  have shape := NotionCoreMachineCanonicalCreate.fresh_create_shape state result key after freshInstance freshBlock created
  have physicalEq := (NotionCoreMachineCanonicalCreate.fresh_create_physical state result key after
    freshInstance freshBlock created).1
  have stored : result.instances.any (fun item => item.1 == blockName key) = true := by
    simp [shape.1]
  have extracted := NotionCoreMachineSlices.empty_title_atoms result (blockName key) stored physicalEq
  simp only [materializeBlock, NotionCoreMachineClient.materialize, NotionCoreSliceForest.freshTitle,
    NotionCoreSliceForest.preorderTree, NotionCoreSliceForest.preorderChildren, List.mapM_cons,
    List.mapM_nil, extracted]
  rfl

private theorem old_lookup (state result : State) (key : BlockKey) (after : Option BlockKey)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName key)
    (freshBlock : FreshBlock state (blockName key))
    (created : applyOperation state (.create key after) = some result)
    (bid : Nat) (shown : bid ∈ state.display) (source : NotionCoreSource.Block)
    (accepted : materializeEntry state bid = some source) :
    materializeEntry result bid = some source := by
  have shape := NotionCoreMachineCanonicalCreate.fresh_create_shape state result key after freshInstance freshBlock created
  have different : bid ≠ blockName key := fun same => freshBlock.2 (same ▸ shown)
  cases found : state.forest.find? (fun block => block.id == bid) with
  | none =>
    rw [materializeEntry_tombstone state bid found] at accepted
    rw [materializeEntry_tombstone result bid (by simp [shape.2.1,List.find?_append,found,different.symm])]
    exact accepted
  | some block =>
    rw [materializeEntry_stored state bid block found] at accepted
    have frame := fresh_create_block state result key after freshInstance freshBlock created block source accepted
    rw [materializeEntry_stored result bid block (by simp [shape.2.1,List.find?_append,found])]
    exact frame

private theorem new_lookup (state result : State) (key : BlockKey) (after : Option BlockKey)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName key)
    (freshBlock : FreshBlock state (blockName key))
    (created : applyOperation state (.create key after) = some result) :
    materializeEntry result (blockName key) =
      some (NotionCoreSourceDocument.freshBlock (blockName key) (blockName key)) := by
  have absent : state.forest.find? (fun block => block.id == blockName key) = none := by
    apply List.find?_eq_none.mpr
    intro block member
    simp [freshBlock.1 block member]
  have shape := NotionCoreMachineCanonicalCreate.fresh_create_shape state result key after freshInstance freshBlock created
  have fresh := fresh_create_new_block state result key after freshInstance freshBlock created
  rw [materializeEntry_stored result _ ⟨blockName key,NotionCoreSliceForest.freshTitle (blockName key)⟩
    (by simp [shape.2.1,List.find?_append,absent])]
  exact fresh

private theorem mapM_insert_after (ids : List Nat) (doc : List NotionCoreSource.Block)
    (f g : Nat → Option NotionCoreSource.Block) (previous fresh : Nat) (value : NotionCoreSource.Block)
    (accepted : ids.mapM f = some doc)
    (names : ∀ bid source, f bid = some source → source.id = bid)
    (frame : ∀ bid ∈ ids, ∀ source, f bid = some source → g bid = some source)
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
    have tailEq := ih suffix tail (fun other member => frame other (List.mem_cons_of_mem _ member))
    have sourceName := names bid source first
    have headEq := frame bid (by simp) source first
    by_cases chosen : bid = previous
    · rw [chosen] at headEq
      simp [List.flatMap_cons,chosen,sourceName,headEq,new,tailEq]
    · simp [List.flatMap_cons,chosen,sourceName,headEq,tailEq]

/-- Fresh actual creation simulates the existing independent source-document
create transition, including its exact display insertion order. Freshness and
predecessor existence are structural guards, not assumed output equations. -/
theorem fresh_create_document (state result : State) (key : BlockKey) (after : Option BlockKey)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName key)
    (freshBlock : FreshBlock state (blockName key))
    (created : applyOperation state (.create key after) = some result)
    (aligned : NotionCoreMachineDisplay.Aligned state)
    (document : NotionCoreSourceDocument.Document)
    (materialized : materializeDocument state = some document)
    (predecessor : ∀ previous, after = some previous → blockName previous ∈ state.display) :
    ∃ next, materializeDocument result = some next ∧
      NotionCoreSourceDocument.step document (.create (blockName key) (blockName key) (after.map blockName)) = some next := by
  have ids := materialized_ids state document materialized
  have absent : blockName key ∉ state.display := freshBlock.2
  have filtered : state.display.filter (· != blockName key) = state.display := by
    apply List.filter_eq_self.mpr
    intro bid member
    simp only [bne_iff_ne]
    exact fun equal => absent (equal ▸ member)
  have shape := NotionCoreMachineCanonicalCreate.fresh_create_shape state result key after freshInstance freshBlock created
  have display : result.display = NotionCoreDisplayOrder.insert state.display (blockName key) (after.map blockName) := by
    simpa [filtered] using shape.2.2
  have old : state.display.mapM (materializeEntry state) = some document := materialized
  have frame := old_lookup state result key after freshInstance freshBlock created
  have new := new_lookup state result key after freshInstance freshBlock created
  cases after with
  | none =>
    refine ⟨NotionCoreSourceDocument.freshBlock (blockName key) (blockName key) :: document,?_,?_⟩
    · change result.display.mapM (materializeEntry result) = _
      rw [display]
      simp only [Option.map_none,NotionCoreDisplayOrder.insert,NotionCoreDisplayOrder.insertionIndex,
        List.take_zero,List.drop_zero,List.nil_append,List.mapM_cons,new]
      rw [mapM_frame state.display document _ _ old frame]
      rfl
    · simp [NotionCoreSourceDocument.step,ids,absent]
  | some previous =>
    have present := predecessor previous rfl
    have unique : state.display.Nodup := aligned.2.1
    let next := document.flatMap (fun block => if block.id = blockName previous then
      [block,NotionCoreSourceDocument.freshBlock (blockName key) (blockName key)] else [block])
    refine ⟨next,?_,?_⟩
    · change result.display.mapM (materializeEntry result) = _
      rw [display]
      simp only [Option.map_some]
      rw [NotionCoreDisplayOrder.insert_after_flatMap state.display (blockName key) (blockName previous) unique present]
      exact mapM_insert_after state.display document _ _ _ _ _ old (materialized_named_id state) frame new
    · simp [NotionCoreSourceDocument.step,ids,absent,present,next]

/-- The actual canonical create phase has fresh names and an available
predecessor derived from archived creators. This covers standalone create and
the create phase of split, with their literal required-block metadata. -/
theorem canonical_create_document_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
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
    (by simp [NotionCoreMachineDisplay.Aligned,NotionCoreDisplayOrder.Aligned,NotionCoreDisplayOrder.names,
      NotionCoreDisplayOrder.shown]) accepted
  obtain ⟨freshInstance,freshBlock⟩ := NotionCoreMachineCanonicalCreate.canonical_destination_fresh_version network
    reachable version closed pre suffix tx position state accepted
  obtain ⟨result,created,_⟩ := NotionCoreMachineCanonicalCreate.canonical_create_partitioned_version network
    reachable version closed pre suffix tx position state accepted part after
  have predecessor : ∀ previous, after = some previous → blockName previous ∈ state.display := by
    intro previous selected
    exact NotionCoreMachineBlockPresence.canonical_required_block_version network reachable version closed pre suffix tx position
      state accepted previous (required previous selected)
  obtain ⟨next,projected,step⟩ := fresh_create_document state result (.issued tx.id) after freshInstance
    freshBlock created aligned document materialized predecessor
  exact ⟨result,next,created,projected,step⟩

/-- Standalone creation supplies an atomic source-history update from honest
canonical reconstruction, without caller-supplied partition or predecessor guards. -/
theorem canonical_create_execution_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : State) (replayed : replay {} pre = some state)
    (document : NotionCoreSourceDocument.Document) (materialized : materializeDocument state = some document)
    (after : Option BlockKey) (payload : tx.payload = .create after) :
    ∃ result next, applyTransaction state tx = some result ∧
      materializeDocument result = some next ∧
      NotionCoreSourceDocument.Execution document
        [.create (blockName (.issued tx.id)) (blockName (.issued tx.id)) (after.map blockName)] next := by
  obtain ⟨checked,checkedReplay,part,_,_⟩ :=
    NotionCoreMachineHonestReplay.honest_prefix_reconstruct_version network reachable version closed pre (tx :: suffix) position
  have equal : checked = state := Option.some.inj (checkedReplay.symm.trans replayed)
  subst checked
  obtain ⟨result,next,operation,projected,stepped⟩ := canonical_create_document_version network
    (NotionCoreMachineNetwork.creator_reachable reachable) version closed pre suffix tx position state replayed part
    document materialized after (by
      intro previous selected
      simp [payload,NotionCoreCreatorNetwork.requiredBlocks,selected])
  have transaction : applyTransaction state tx = some result := by
    simp [applyTransaction,NotionCorePayload.operations,payload,applyOperations,operation]
  have aligned := NotionCoreMachineDisplay.replay_aligned {} state pre
    (by simp [NotionCoreMachineDisplay.Aligned,NotionCoreDisplayOrder.Aligned,NotionCoreDisplayOrder.names,
      NotionCoreDisplayOrder.shown]) replayed
  have names : (document.map NotionCoreSource.Block.id).Nodup := by
    rw [materialized_ids state document materialized]
    exact aligned.2.1
  exact ⟨result,next,transaction,projected,.cons ⟨names,True.intro⟩ stepped (.nil next)⟩

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
        (.create (blockName (.issued tx.id)) (blockName (.issued tx.id)) (after.map blockName)) = some next :=
  canonical_create_document_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed (NotionCorePayloadNetwork.forget_reachable (NotionCoreCreatorNetwork.payload_reachable reachable)) peer)
    pre suffix tx position state accepted part document materialized after required

theorem canonical_create_execution (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (replayed : replay {} pre = some state)
    (document : NotionCoreSourceDocument.Document) (materialized : materializeDocument state = some document)
    (after : Option BlockKey) (payload : tx.payload = .create after) :
    ∃ result next, applyTransaction state tx = some result ∧
      materializeDocument result = some next ∧
      NotionCoreSourceDocument.Execution document
        [.create (blockName (.issued tx.id)) (blockName (.issued tx.id)) (after.map blockName)] next :=
  canonical_create_execution_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed (NotionCorePayloadNetwork.forget_reachable (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))) peer)
    pre suffix tx position state replayed document materialized after payload

#print axioms canonical_create_document_version
#print axioms canonical_create_execution_version
#print axioms canonical_create_execution

#print axioms canonical_create_document

#print axioms fresh_create_document

#print axioms fresh_create_slice
#print axioms fresh_create_block
#print axioms fresh_create_new_block
end Sal.MRDTs.Instances.NotionCoreMachineDocumentCreate
