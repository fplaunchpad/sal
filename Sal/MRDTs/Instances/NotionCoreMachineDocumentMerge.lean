import Sal.MRDTs.Instances.NotionCoreMachineDocumentSplit

/-! Checked materialization under the actual merge operation. A merge moves a
whole stored chain below the last node of the chain holding the target's
title root, or changes nothing. The holder found by the forest search is the
owner of the target's root interval in the materialized document, so the
machine's merge is the source document's merge, and hence the specification's.
-/
namespace Sal.MRDTs.Instances.NotionCoreMachineDocumentMerge
open NotionCoreSpec (Address)
open NotionCoreSource (Atom Slice Block)
open NotionCorePartition (Cell flatten)
open NotionCoreSliceForest (Ref)
open NotionCoreMachine
open NotionCoreMachineDocument

private theorem find_member (forest : NotionCoreSliceForest.Forest)
    (unique : (forest.map NotionCoreSliceForest.Block.id).Nodup)
    (block : NotionCoreSliceForest.Block) (member : block ∈ forest) (bid : Nat) (name : block.id = bid) :
    forest.find? (fun old => old.id == bid) = some block := by
  subst name
  exact NotionCoreMachineClient.find_block_member forest unique block member

private theorem mapM_member_input {α β : Type} (f : α → Option β)
    (xs : List α) (ys : List β) (accepted : xs.mapM f = some ys)
    (x : α) (member : x ∈ xs) : ∃ y ∈ ys, f x = some y := by
  induction xs generalizing ys with
  | nil => simp at member
  | cons head rest ih =>
    cases first : f head with
    | none => simp [List.mapM_cons,first] at accepted
    | some value =>
      cases later : rest.mapM f with
      | none => simp [List.mapM_cons,first,later] at accepted
      | some tail =>
        have equal : value :: tail = ys := by simpa [List.mapM_cons,first,later] using accepted
        subst ys
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨value,by simp,first⟩
        · obtain ⟨y,member,eq⟩ := ih tail later member
          exact ⟨y,List.mem_cons_of_mem _ member,eq⟩

private theorem mapM_transport {α β : Type} (xs : List α) (f g : α → Option β)
    (change : β → β) (pointwise : ∀ x ∈ xs, ∀ y, f x = some y → g x = some (change y))
    (ys : List β) (accepted : xs.mapM f = some ys) :
    xs.mapM g = some (ys.map change) := by
  induction xs generalizing ys with
  | nil => simpa using accepted
  | cons head tail ih =>
    cases first : f head with
    | none => simp [List.mapM_cons,first] at accepted
    | some value =>
      cases rest : tail.mapM f with
      | none => simp [List.mapM_cons,first,rest] at accepted
      | some values =>
        have equal : value :: values = ys := by
          simpa [List.mapM_cons,first,rest] using accepted
        subst ys
        simp [List.mapM_cons,pointwise head (by simp) value first,
          ih (fun x member => pointwise x (List.mem_cons_of_mem _ member)) values rest]

private theorem find_doc_member (document : NotionCoreSourceDocument.Document)
    (unique : (document.map Block.id).Nodup) (value : Block) (member : value ∈ document)
    (bid : Nat) (name : value.id = bid) :
    NotionCoreSourceDocument.findBlock document bid = some value := by
  subst name
  unfold NotionCoreSourceDocument.findBlock
  induction document with
  | nil => simp at member
  | cons first rest ih =>
    have nd := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with rfl | member
    · simp
    · have different : first.id ≠ value.id := by
        intro equal
        exact nd.1 (List.mem_map.mpr ⟨value,member,equal.symm⟩)
      simp [different,ih nd.2 member]

/-- Lookup in a merged forest: the source is gone, the holder carries the
appended chain, and every other block is unchanged. -/
theorem merged_find (forest : NotionCoreSliceForest.Forest)
    (unique : (forest.map NotionCoreSliceForest.Block.id).Nodup)
    (moved holder : NotionCoreSliceForest.Block) (holderMember : holder ∈ forest) (bid : Nat) :
    (((forest.filter fun block => block.id != moved.id).map fun block =>
        if block.id = holder.id then
          {block with title := NotionCoreSliceForest.appendLast block.title moved.title}
        else block).find? fun block => block.id == bid) =
      if bid = moved.id then none
      else if bid = holder.id then
        some {holder with title := NotionCoreSliceForest.appendLast holder.title moved.title}
      else forest.find? fun block => block.id == bid := by
  rw [List.find?_map]
  have ids : ((fun block : NotionCoreSliceForest.Block => block.id == bid) ∘
      fun block => if block.id = holder.id then
        {block with title := NotionCoreSliceForest.appendLast block.title moved.title} else block) =
      fun block => block.id == bid := by
    funext block
    simp only [Function.comp_apply]
    split <;> rfl
  rw [ids, List.find?_filter]
  by_cases isSource : bid = moved.id
  · subst bid
    simp only [↓reduceIte]
    rw [List.find?_eq_none.mpr]
    · rfl
    · intro block _
      cases equal : block.id == moved.id <;> simp_all
  · simp only [isSource, ↓reduceIte]
    have same : (fun block : NotionCoreSliceForest.Block =>
        decide ((block.id != moved.id) = true ∧ (block.id == bid) = true)) =
        fun block => block.id == bid := by
      funext block
      by_cases named : block.id = bid
      · simp [named, isSource]
      · simp [named]
    rw [same]
    by_cases isHolder : bid = holder.id
    · rw [find_member forest unique holder holderMember bid isHolder.symm]
      simp [isHolder]
    · simp only [isHolder, ↓reduceIte]
      cases found : forest.find? (fun block => block.id == bid) with
      | none => rfl
      | some block =>
        have name : block.id = bid := by simpa using List.find?_some found
        simp [name, isHolder]

/-- The title root of every stored instance is a node of some stored chain:
the instance's first cell starts at its root. -/
theorem holder_exists (state : State) (part : NotionCoreMachinePartition.Partitioned state)
    (target : Nat) (stored : ∃ entry ∈ state.instances, entry.1 = target) :
    ∃ holder, NotionCoreSliceForest.holderOf state.forest target = some holder := by
  obtain ⟨cells,physicalEq,permutation⟩ := part.partitions target stored
  cases cells with
  | nil =>
    simp [physical, NotionCorePhysicalReplay.physical, flatten] at physicalEq
  | cons first rest =>
    have startEq : first.slice.start = (target,.start) := by
      simp only [physical, NotionCorePhysicalReplay.physical, flatten, List.flatMap_cons,
        NotionCorePartition.Cell.physical, List.cons_append, List.cons.injEq] at physicalEq
      have heads := congrArg NotionCoreSource.Atom.address physicalEq.1
      simpa [NotionCorePhysicalReplay.start, NotionCorePartition.boundary] using heads.symm
    let owned : Nat × Ref :=
      (first.owner,⟨first.slice.start,rest.head?.map (fun next => next.slice.start)⟩)
    have ownedCells : owned ∈ NotionCoreMachinePartition.cellRefs (first :: rest) :=
      (NotionCoreMachinePartition.cellRefs_member _ owned).mpr ⟨[],first,rest,rfl,rfl⟩
    have ownedMember := (List.mem_filter.mp (permutation.mem_iff.mpr ownedCells)).1
    obtain ⟨block,blockMember,refMapped⟩ := List.mem_flatMap.mp ownedMember
    obtain ⟨ref,inTree,refEq⟩ := List.mem_map.mp refMapped
    have refStart : ref.start = (target,.start) := by
      have := congrArg (fun pair : Nat × Ref => pair.2.start) refEq
      simpa [owned, startEq] using this
    cases found : NotionCoreSliceForest.holderOf state.forest target with
    | some holder => exact ⟨holder, rfl⟩
    | none =>
      have absent := List.find?_eq_none.mp found block blockMember
      exact absurd (List.any_eq_true.mpr ⟨ref, inTree, by simp [refStart]⟩) absent

/-- The holder of a target's title root materializes to the owner of the
target's root address in the materialized document. -/
theorem holder_owner (state : State) (part : NotionCoreMachinePartition.Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (aligned : NotionCoreMachineDisplay.Aligned state)
    (document : NotionCoreSourceDocument.Document)
    (old : materializeDocument state = some document)
    (docUnique : (NotionCoreInvariant.addresses (NotionCoreSourceDocument.project document)).Nodup)
    (target : Nat) (holder : NotionCoreSliceForest.Block)
    (found : NotionCoreSliceForest.holderOf state.forest target = some holder) :
    ∃ source, materializeBlock state holder = some source ∧
      NotionCoreSourceDocument.owner document (target,.start) = some source := by
  have found' : state.forest.find? (fun block => (NotionCoreSliceForest.preorderTree block.title).any
      fun ref => ref.start == (target,.start)) = some holder := found
  have holderMember := List.mem_of_find?_eq_some found'
  have hit := List.find?_some found'
  simp only at hit
  obtain ⟨ref,inTree,refStart⟩ := List.any_eq_true.mp hit
  obtain ⟨source,sourceMat⟩ := materializeBlock_total state part unique holder holderMember
  refine ⟨source,sourceMat,?_⟩
  have sourceMember := NotionCoreMachineDocumentSplit.materialized_member state aligned document old holder
    holderMember source sourceMat
  have held : (target,NotionCoreSpec.LocalId.start) ∈ source.traversal := by
    have extracted := (materialized_slices state holder source sourceMat).1
    obtain ⟨slice,sliceMember,sliceRead⟩ :=
      mapM_member_input _ _ _ extracted ref inTree
    cases atoms : sliceAtoms state ref with
    | none => simp [atoms] at sliceRead
    | some found =>
      have sliceEq : slice = ⟨ref.start,found⟩ := by simpa [atoms] using sliceRead.symm
      subst slice
      have startEq : ref.start = (target,.start) := by simpa using refStart
      exact List.mem_flatMap.mpr ⟨_,sliceMember,by simp [NotionCoreSource.Slice.traversal, startEq]⟩
  exact NotionCoreMachineDocumentSplit.owner_of_materialized_slice document docUnique source sourceMember _ held

private theorem mapM_append_some {α β : Type} (f : α → Option β) (xs ys : List α) (as bs : List β)
    (left : xs.mapM f = some as) (right : ys.mapM f = some bs) : (xs ++ ys).mapM f = some (as ++ bs) := by
  induction xs generalizing as with
  | nil => simp at left; subst as; simpa using right
  | cons head rest ih =>
    simp only [List.mapM_cons] at left
    obtain ⟨a, first, later⟩ := Option.bind_eq_some_iff.mp left
    obtain ⟨tail, following, same⟩ := Option.bind_eq_some_iff.mp later
    have equal : a :: tail = as := Option.some.inj same
    subst as
    simp [List.mapM_cons, first, ih tail following]

private theorem mapM_pointwise {α β : Type} (xs : List α) (f g : α → Option β)
    (pointwise : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons head rest ih =>
    rw [List.mapM_cons, List.mapM_cons, pointwise head (by simp),
      ih (fun x member => pointwise x (List.mem_cons_of_mem _ member))]

/-- Actual merge simulates the source document's merge transition. The
target is a displayed block whose instance is stored; no next document or
holder equation is assumed. -/
theorem merge_source_step (state : State) (part : NotionCoreMachinePartition.Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (aligned : NotionCoreMachineDisplay.Aligned state)
    (document : NotionCoreSourceDocument.Document)
    (old : materializeDocument state = some document)
    (docUnique : (NotionCoreInvariant.addresses (NotionCoreSourceDocument.project document)).Nodup)
    (source target : Nat) (targetShown : target ∈ state.display)
    (targetStored : ∃ entry ∈ state.instances, entry.1 = target) :
    ∃ after, materializeDocument
        {state with forest := NotionCoreSliceForest.mergeForest state.forest source target} = some after ∧
      NotionCoreSourceDocument.step document (.merge source target) = some after := by
  have docIds : (document.map Block.id).Nodup := by
    rw [materialized_ids state document old]
    exact aligned.2.1
  have findDoc : ∀ bid ∈ state.display, ∀ value, materializeEntry state bid = some value →
      NotionCoreSourceDocument.findBlock document bid = some value := by
    intro bid shown value entry
    obtain ⟨other,otherMember,otherEntry⟩ := mapM_member_input _ state.display document old bid shown
    rw [entry] at otherEntry
    cases otherEntry
    exact find_doc_member document docIds value otherMember bid (materialized_named_id state bid value entry)
  obtain ⟨tgt,_,tgtEntry⟩ := mapM_member_input _ state.display document old target targetShown
  have tgtFound := findDoc target targetShown tgt tgtEntry
  have tgtInst : tgt.inst = target := by
    cases found : state.forest.find? (fun old => old.id == target) with
    | none =>
      rw [materializeEntry_tombstone state target found] at tgtEntry
      cases tgtEntry
      rfl
    | some block =>
      rw [materializeEntry_stored state target block found] at tgtEntry
      have name : block.id = target := by simpa using List.find?_some found
      exact (materialized_slices state block tgt tgtEntry).2.2.trans name
  obtain ⟨holder,holderFound⟩ := holder_exists state part target targetStored
  obtain ⟨holderSource,holderMat,holderOwner⟩ := holder_owner state part unique aligned document old
    docUnique target holder holderFound
  have holderMember := List.mem_of_find?_eq_some holderFound
  have holderId : holderSource.id = holder.id := (materialized_slices state holder holderSource holderMat).2.1
  have stepShape : ∀ src, NotionCoreSourceDocument.findBlock document source = some src →
      NotionCoreSourceDocument.step document (.merge source target) =
        if src.alive = true ∧ holderSource.id ≠ source then
          some (document.map fun block =>
            if block.id = holderSource.id then {block with slices := block.slices ++ src.slices}
            else if block.id = source then {block with slices := []}
            else block)
        else some document := by
    intro src srcFound
    simp only [NotionCoreSourceDocument.step, srcFound, tgtFound, tgtInst, holderOwner]
  cases sourceFound : state.forest.find? (fun old => old.id == source) with
  | none =>
    have same : NotionCoreSliceForest.mergeForest state.forest source target = state.forest := by
      simp [NotionCoreSliceForest.mergeForest, sourceFound]
    refine ⟨document, by simpa [same] using old, ?_⟩
    cases srcFound : NotionCoreSourceDocument.findBlock document source with
    | none => simp [NotionCoreSourceDocument.step, srcFound]
    | some src =>
      rw [stepShape src srcFound]
      have srcMember := List.mem_of_find?_eq_some srcFound
      have srcName : src.id = source := by simpa using List.find?_some srcFound
      obtain ⟨bid,shown,entry⟩ := NotionCoreMachineDelete.mapM_source _ state.display
        document old src srcMember
      have named := materialized_named_id state bid src entry
      rw [srcName] at named
      subst bid
      rw [materializeEntry_tombstone state source sourceFound] at entry
      cases entry
      simp [Block.alive]
  | some moved =>
    have movedMember := List.mem_of_find?_eq_some sourceFound
    have movedId : moved.id = source := by simpa using List.find?_some sourceFound
    obtain ⟨src,srcMat⟩ := materializeBlock_total state part unique moved movedMember
    have srcShown : source ∈ state.display := by
      have shown := (NotionCoreDisplayOrder.shown_member _ _).mp
        (aligned.2.2.mem_iff.mpr (List.mem_map.mpr ⟨moved,movedMember,rfl⟩))
      simpa [movedId] using shown.1
    have srcFound := findDoc source srcShown src
      (by rw [materializeEntry_stored state source moved sourceFound]; exact srcMat)
    rw [stepShape src srcFound]
    have srcAlive := materialized_alive state moved src srcMat
    have srcId : src.id = source := (materialized_slices state moved src srcMat).2.1.trans movedId
    by_cases cycle : holder.id = source
    · have same : NotionCoreSliceForest.mergeForest state.forest source target = state.forest := by
        simp [NotionCoreSliceForest.mergeForest, sourceFound, holderFound, cycle]
      refine ⟨document, by simpa [same] using old, ?_⟩
      simp [holderId, cycle]
    · have merged : NotionCoreSliceForest.mergeForest state.forest source target =
          (state.forest.filter fun block => block.id != moved.id).map fun block =>
            if block.id = holder.id then
              {block with title := NotionCoreSliceForest.appendLast block.title moved.title}
            else block := by
        simp [NotionCoreSliceForest.mergeForest, sourceFound, holderFound, cycle, movedId]
      rw [if_pos ⟨srcAlive, by rw [holderId]; exact cycle⟩]
      refine ⟨_, ?_, rfl⟩
      let changeSource := fun block : Block =>
        if block.id = holderSource.id then {block with slices := block.slices ++ src.slices}
        else if block.id = source then {block with slices := []}
        else block
      unfold materializeDocument at old ⊢
      change state.display.mapM _ = some (document.map changeSource)
      have distinct : holder.id ≠ moved.id := by rw [movedId]; exact cycle
      have mergedFind : ∀ bid,
          ({state with forest := NotionCoreSliceForest.mergeForest state.forest source target} : State).forest.find?
            (fun block => block.id == bid) =
          if bid = moved.id then none
          else if bid = holder.id then
            some {holder with title := NotionCoreSliceForest.appendLast holder.title moved.title}
          else state.forest.find? fun block => block.id == bid := by
        intro bid
        show (NotionCoreSliceForest.mergeForest state.forest source target).find? _ = _
        rw [merged]
        exact merged_find state.forest aligned.1 moved holder holderMember bid
      have transform : ∀ bid ∈ state.display, ∀ value, materializeEntry state bid = some value →
          materializeEntry {state with forest := NotionCoreSliceForest.mergeForest state.forest source target}
            bid = some (changeSource value) := by
        intro bid _ value entry
        have name := materialized_named_id state bid value entry
        by_cases isSource : bid = source
        · rw [isSource] at entry name ⊢
          rw [materializeEntry_stored state source moved sourceFound, srcMat] at entry
          cases entry
          rw [materializeEntry_tombstone _ source (by rw [mergedFind]; simp [movedId])]
          have srcInst : src.inst = source := (materialized_slices state moved src srcMat).2.2.trans movedId
          have notHolder : source ≠ holderSource.id := by rw [holderId]; exact Ne.symm cycle
          simp only [changeSource, srcId, notHolder, ↓reduceIte]
          cases src
          simp_all
        · by_cases isHolder : bid = holder.id
          · rw [isHolder] at entry name ⊢
            rw [materializeEntry_stored state holder.id holder
              (find_member state.forest aligned.1 holder holderMember _ rfl), holderMat] at entry
            cases entry
            rw [materializeEntry_stored _ holder.id
              {holder with title := NotionCoreSliceForest.appendLast holder.title moved.title}
              (by rw [mergedFind]; simp [movedId, cycle])]
            have holderRead := (materialized_slices state holder holderSource holderMat).1
            have movedRead := (materialized_slices state moved src srcMat).1
            have appended : NotionCoreMachineClient.materialize
                {state with forest := NotionCoreSliceForest.mergeForest state.forest source target}
                (NotionCoreSliceForest.appendLast holder.title moved.title) =
                some (holderSource.slices ++ src.slices) := by
              unfold NotionCoreMachineClient.materialize at holderRead movedRead ⊢
              rw [NotionCoreSliceForest.preorder_appendLast]
              exact mapM_append_some _ _ _ _ _ holderRead movedRead
            have instEq := (materialized_slices state holder holderSource holderMat).2.2
            cases holderSource
            simp only at holderId instEq
            subst holderId instEq
            simp [materializeBlock, appended, changeSource]
          · have untouched : changeSource value = value := by
              simp [changeSource, name, holderId, isHolder, isSource]
            rw [untouched]
            cases found : state.forest.find? (fun old => old.id == bid) with
            | none =>
              rw [materializeEntry_tombstone state bid found] at entry
              cases entry
              rw [materializeEntry_tombstone _ bid (by rw [mergedFind]; simp [movedId, isSource, isHolder, found])]
            | some block =>
              rw [materializeEntry_stored state bid block found] at entry
              rw [materializeEntry_stored _ bid block (by rw [mergedFind]; simp [movedId, isSource, isHolder, found])]
              exact entry
      exact mapM_transport state.display _ _ changeSource transform document old

/-- Honest canonical merge executes an atomic source-history update with one
merge command. The target is a displayed block with a stored instance,
derived from the archived creator of the merge's required target. -/
theorem canonical_merge_execution_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : State) (replayed : replay {} pre = some state)
    (document : NotionCoreSourceDocument.Document)
    (materialized : materializeDocument state = some document)
    (source target : NotionCorePayload.BlockKey)
    (payload : tx.payload = .merge source target) :
    ∃ result after, applyTransaction state tx = some result ∧
      materializeDocument result = some after ∧
      NotionCoreSourceDocument.Execution document
        [.merge (blockName source) (blockName target)] after := by
  have creators := NotionCoreMachineNetwork.creator_reachable reachable
  obtain ⟨checked,checkedReplay,part,_,_⟩ :=
    NotionCoreMachineHonestReplay.honest_prefix_reconstruct_version network reachable version closed pre
      (tx :: suffix) position
  have equal : checked = state := Option.some.inj (checkedReplay.symm.trans replayed)
  subst checked
  have unique := NotionCoreMachineMarkerProgress.canonical_physical_unique_all_version network
    (NotionCoreCreatorNetwork.payload_reachable creators) version closed pre (tx :: suffix) position state replayed
  have aligned := NotionCoreMachineDisplay.replay_aligned {} state pre
    (by simp [NotionCoreMachineDisplay.Aligned,NotionCoreDisplayOrder.Aligned,NotionCoreDisplayOrder.names,
      NotionCoreDisplayOrder.shown]) replayed
  have targetShown := NotionCoreMachineBlockPresence.canonical_required_block_version network creators
    version closed pre suffix tx position state replayed target
    (by simp [payload,NotionCoreCreatorNetwork.requiredBlocks])
  have targetStored := NotionCoreMachineCreatorPresence.canonical_required_instance_version network creators
    version closed pre suffix tx position state replayed target
    (by simp [payload,NotionCoreCreatorNetwork.requiredBlocks])
  have docUnique := NotionCoreMachineDocumentInvariant.projected_addresses_unique state part unique aligned
    document materialized
  obtain ⟨after,afterMat,stepped⟩ := merge_source_step state part unique aligned document materialized docUnique
    (blockName source) (blockName target) targetShown targetStored
  let merged := NotionCoreSliceForest.mergeForest state.forest (blockName source) (blockName target)
  have transaction : applyTransaction state tx = some {state with forest := merged} := by
    simp [applyTransaction,NotionCorePayload.operations,payload,applyOperations,applyOperation,merged]
  have guard := NotionCoreMachineDocumentInvariant.accepted_source_guard state part unique aligned
    document after materialized _ stepped
  exact ⟨_,after,transaction,afterMat,.cons guard stepped (.nil after)⟩

theorem canonical_merge_execution (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (replayed : replay {} pre = some state)
    (document : NotionCoreSourceDocument.Document)
    (materialized : materializeDocument state = some document)
    (source target : NotionCorePayload.BlockKey)
    (payload : tx.payload = .merge source target) :
    ∃ result after, applyTransaction state tx = some result ∧
      materializeDocument result = some after ∧
      NotionCoreSourceDocument.Execution document
        [.merge (blockName source) (blockName target)] after :=
  canonical_merge_execution_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed (NotionCorePayloadNetwork.forget_reachable
      (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))) peer)
    pre suffix tx position state replayed document materialized source target payload

namespace SPOT
private def cut : NotionCorePayload.Transaction := ⟨⟨3,[83]⟩,.split .initial .initial (.item ⟨1,[65]⟩)⟩
private def back : NotionCorePayload.Transaction := ⟨⟨4,[83]⟩,.merge (.issued ⟨3,[83]⟩) .initial⟩
private def split := replay {} [NotionCorePayload.bootstrap [97,98],cut]

/-- The machine merge of the split destination back into its source and the
source document's merge give the same document: ab in block 0 and a
tombstone for the destination. Rendering only the left half is excluded. -/
theorem merge_document_control :
    ((split >>= fun state => applyTransaction state back) >>= materializeDocument) =
      ((split >>= materializeDocument) >>= fun document =>
        NotionCoreSourceDocument.step document
          (.merge (blockName (.issued ⟨3,[83]⟩)) (blockName .initial))) ∧
    ((split >>= fun state => applyTransaction state back) >>= materializeDocument).map
      (fun doc => NotionCoreSpec.view (NotionCoreSourceDocument.project doc)) = some [(0,[97,98])] ∧
    ((split >>= fun state => applyTransaction state back) >>= materializeDocument).map
      (fun doc => NotionCoreSpec.view (NotionCoreSourceDocument.project doc)) ≠ some [(0,[97])] := by
  decide +kernel
end SPOT

#print axioms merged_find
#print axioms holder_exists
#print axioms holder_owner
#print axioms merge_source_step
#print axioms canonical_merge_execution_version
#print axioms canonical_merge_execution
#print axioms SPOT.merge_document_control
end Sal.MRDTs.Instances.NotionCoreMachineDocumentMerge
