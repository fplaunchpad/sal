import Sal.MRDTs.Instances.NotionCoreMachineDocumentMerge
import Sal.MRDTs.Instances.NotionCoreMachineInsertEffects

/-! Honest merge request effects. The issuer merges a displayed block into
the previous displayed block, anchored at the last node of that block's chain;
its next rendering shows the previous block's text followed by the merged
block's text, and the merged block is no longer displayed. The atomic merge
executes through the source-document simulation, whose holder is the owner of
the anchor's close slot: the previous block itself.
-/
namespace Sal.MRDTs.Instances.NotionCoreMachineMergeEffects
open NotionCoreMachine
open NotionCoreMachineClient
open NotionCoreMachineDocument
open NotionCorePayload (BlockKey Transaction)
open NotionCoreSource (Block Slice)

/-- An alive materialized block holds the root interval of its own instance. -/
theorem materialized_root (state : State) (shape : NotionCoreMachineShape.ShapeInvariant state)
    (document : NotionCoreSourceDocument.Document) (materialized : materializeDocument state = some document)
    (source : Block) (member : source ∈ document) (alive : source.alive = true) :
    (source.inst,NotionCoreSpec.LocalId.start) ∈ source.traversal := by
  obtain ⟨bid,_,entry⟩ := NotionCoreMachineDelete.mapM_source _ state.display document materialized source member
  cases found : state.forest.find? (fun old => old.id == bid) with
  | none =>
    rw [materializeEntry_tombstone state bid found] at entry
    cases entry
    simp [Block.alive] at alive
  | some block =>
    rw [materializeEntry_stored state bid block found] at entry
    have blockMember := List.mem_of_find?_eq_some found
    obtain ⟨extracted,_,instEq⟩ := materialized_slices state block source entry
    have rootStart := (shape.1 block blockMember).2
    unfold NotionCoreMachineClient.materialize at extracted
    rw [NotionCoreSliceForest.preorderTree_eq, List.mapM_cons] at extracted
    obtain ⟨first,firstRead,later⟩ := Option.bind_eq_some_iff.mp extracted
    obtain ⟨rest,_,same⟩ := Option.bind_eq_some_iff.mp later
    have slicesEq : first :: rest = source.slices := Option.some.inj same
    cases atoms : sliceAtoms state block.title.slice with
    | none => simp [atoms] at firstRead
    | some found =>
      have firstEq : first = ⟨block.title.slice.start,found,block.title.slice.stop⟩ := by
        simpa [atoms] using firstRead.symm
      rw [Block.traversal, ← slicesEq, firstEq, instEq, ← rootStart]
      simp [Slice.traversal]

private theorem find_doc_member (document : NotionCoreSourceDocument.Document)
    (unique : (document.map Block.id).Nodup) (value : Block) (member : value ∈ document) :
    NotionCoreSourceDocument.findBlock document value.id = some value := by
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

/-- The source document's merge of an alive block into the previous alive
block, across tombstones only, renders the target's text followed by the
source's, and drops the source from the view. -/
theorem merged_view (before gap afterBlocks : NotionCoreSourceDocument.Document) (target source : Block)
    (unique : ((before ++ target :: gap ++ source :: afterBlocks).map Block.id).Nodup)
    (targetAlive : target.alive = true) (gapDead : ∀ block ∈ gap, block.alive = false) :
    NotionCoreSpec.view (NotionCoreSourceDocument.project
      ((before ++ target :: gap ++ source :: afterBlocks).map fun block =>
        if block.id = target.id then {block with slices := block.slices ++ source.slices}
        else if block.id = source.id then {block with slices := []}
        else block)) =
      NotionCoreSpec.view (NotionCoreSourceDocument.project before) ++
        [(target.id,NotionCoreSpec.text target.project.slots ++ NotionCoreSpec.text source.project.slots)] ++
        NotionCoreSpec.view (NotionCoreSourceDocument.project afterBlocks) := by
  have perm : ((before ++ target :: gap ++ source :: afterBlocks).map Block.id).Perm
      (target.id :: source.id :: (before ++ gap ++ afterBlocks).map Block.id) := by
    apply List.perm_iff_count.mpr
    intro x
    simp only [List.map_append, List.map_cons, List.count_append, List.count_cons]
    omega
  have nd := perm.nodup_iff.mp unique
  obtain ⟨targetFresh,rest⟩ := List.nodup_cons.mp nd
  obtain ⟨sourceFresh,_⟩ := List.nodup_cons.mp rest
  have distinct : source.id ≠ target.id := fun equal => targetFresh (by simp [equal])
  have kept : ∀ block ∈ before ++ gap ++ afterBlocks,
      (if block.id = target.id then {block with slices := block.slices ++ source.slices}
        else if block.id = source.id then ({block with slices := []} : Block) else block) = block := by
    intro block member
    have notTarget : block.id ≠ target.id := fun equal =>
      targetFresh (by rw [← equal]; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨block,member,rfl⟩))
    have notSource : block.id ≠ source.id := fun equal =>
      sourceFresh (by rw [← equal]; exact List.mem_map.mpr ⟨block,member,rfl⟩)
    simp [notTarget,notSource]
  have keepList (xs : NotionCoreSourceDocument.Document) (inside : ∀ block ∈ xs, block ∈ before ++ gap ++ afterBlocks) :
      xs.map (fun block => if block.id = target.id then {block with slices := block.slices ++ source.slices}
        else if block.id = source.id then ({block with slices := []} : Block) else block) = xs := by
    conv_rhs => rw [← List.map_id xs]
    exact List.map_congr_left fun block member => kept block (inside block member)
  simp only [List.map_append, List.map_cons]
  rw [keepList before (fun b m => by simp [m]), keepList gap (fun b m => by simp [m]),
    keepList afterBlocks (fun b m => by simp [m])]
  have gapView : NotionCoreSpec.view (NotionCoreSourceDocument.project gap) = [] := by
    simp only [NotionCoreSpec.view, NotionCoreSourceDocument.project, List.filter_map]
    rw [List.filter_eq_nil_iff.mpr (fun block member => by simp [gapDead block member])]
    rfl
  have targetLive : (({target with slices := target.slices ++ source.slices} : Block).alive) = true := by
    cases slices : target.slices with
    | nil => simp [Block.alive, slices] at targetAlive
    | cons _ _ => simp [Block.alive]
  simp only [↓reduceIte, distinct]
  simp only [NotionCoreSpec.view, NotionCoreSourceDocument.project, List.map_append, List.map_cons,
    List.filter_append, List.filter_cons, NotionCoreSourceDocument.project_alive, targetLive,
    ↓reduceIte, List.map_append, List.map_cons] at gapView ⊢
  simp [Block.alive, gapView, Block.slots, NotionCoreSpec.text_append, List.flatMap_append]

private theorem lastNode_mem (tree : NotionCoreSliceForest.Tree) :
    NotionCoreSliceForest.lastNode tree ∈ NotionCoreSliceForest.preorderTree tree := by
  unfold NotionCoreSliceForest.lastNode
  rw [NotionCoreSliceForest.preorderTree_eq, List.getLast?_eq_some_getLast (by simp)]
  exact List.getLast_mem _

/-- The previous displayed block of an alive block, across tombstones only,
is a stored block, and the client prepares a merge anchored at the last node
of its chain. -/
theorem prepared_merge_target (txs : List Transaction) (state : State)
    (accepted : replay {} txs = some state) (part : NotionCoreMachinePartition.Partitioned state)
    (aligned : NotionCoreMachineDisplay.Aligned state)
    (before gap afterBlocks : NotionCoreSourceDocument.Document) (target source : Block)
    (materialized : materializeDocument state = some (before ++ target :: gap ++ source :: afterBlocks))
    (targetAlive : target.alive = true) (sourceAlive : source.alive = true)
    (gapDead : ∀ block ∈ gap, block.alive = false)
    (sourceKey : BlockKey) (sourceName : source.id = blockName sourceKey) :
    ∃ stored ∈ state.forest, materializeBlock state stored = some target ∧ ∃ inst stop,
      mergeAnchor inst stop = NotionCoreSliceForest.anchorOf (NotionCoreSliceForest.lastNode stored.title) ∧
      prepareMerge state sourceKey = some (.merge sourceKey inst stop) := by
  have ids := materialized_ids state _ materialized
  have shownIff : ∀ block ∈ before ++ target :: gap ++ source :: afterBlocks,
      (state.forest.any fun stored => stored.id == block.id) = block.alive := by
    intro block member
    obtain ⟨bid,_,entry⟩ := NotionCoreMachineDelete.mapM_source _ state.display _ materialized block member
    have name := materialized_named_id state bid block entry
    subst bid
    cases found : state.forest.find? (fun old => old.id == block.id) with
    | none =>
      rw [materializeEntry_tombstone state block.id found] at entry
      have dead : block.alive = false := by rw [← Option.some.inj entry]; rfl
      have absent : (state.forest.any fun stored => stored.id == block.id) = false := by
        apply Bool.eq_false_iff.mpr
        intro present
        obtain ⟨stored,storedMember,equal⟩ := List.any_eq_true.mp present
        exact List.find?_eq_none.mp found stored storedMember equal
      rw [absent, dead]
    | some stored =>
      rw [materializeEntry_stored state block.id stored found] at entry
      have live := materialized_alive state stored block entry
      rw [live]
      have hit := List.find?_some found
      simp only at hit
      exact List.any_eq_true.mpr ⟨stored,List.mem_of_find?_eq_some found,hit⟩
  have visibleEq : visible state =
      (before.filter Block.alive).map Block.id ++ target.id :: source.id ::
        (afterBlocks.filter Block.alive).map Block.id := by
    unfold visible
    rw [← ids]
    rw [List.filter_map]
    have congrFilter : (before ++ target :: gap ++ source :: afterBlocks).filter
        ((fun bid => state.forest.any fun stored => stored.id == bid) ∘ Block.id) =
        (before ++ target :: gap ++ source :: afterBlocks).filter Block.alive :=
      List.filter_congr (fun block member => by simpa using shownIff block member)
    rw [congrFilter]
    have gapFilter : gap.filter Block.alive = [] :=
      List.filter_eq_nil_iff.mpr (fun block member => by simp [gapDead block member])
    simp [List.filter_append, targetAlive, sourceAlive, gapFilter]
  have shownNodup : (visible state).Nodup := aligned.2.1.filter _
  rw [visibleEq] at shownNodup
  obtain ⟨stored,storedMember,storedName⟩ : ∃ stored ∈ state.forest, stored.id = target.id := by
    have present : (state.forest.any fun stored => stored.id == target.id) = true := by
      rw [shownIff target (by simp)]; exact targetAlive
    obtain ⟨stored,member,equal⟩ := List.any_eq_true.mp present
    exact ⟨stored,member,by simpa using equal⟩
  have storedFound := NotionCoreMachineClient.find_block_member state.forest aligned.1 stored storedMember
  have targetMat : materializeBlock state stored = some target := by
    obtain ⟨bid,_,entry⟩ := NotionCoreMachineDelete.mapM_source _ state.display _ materialized target (by simp)
    have name := materialized_named_id state bid target entry
    subst bid
    rw [materializeEntry_stored state target.id stored (by rw [← storedName]; exact storedFound)] at entry
    exact entry
  have prefixTake : ((visible state).take ((visible state).idxOf (blockName sourceKey))).getLast? =
      some target.id := by
    rw [visibleEq, ← sourceName]
    have notBefore : source.id ∉ (before.filter Block.alive).map Block.id := by
      intro member
      exact (List.nodup_append.mp shownNodup).2.2 _ member _ (by simp) rfl
    have notTarget : target.id ≠ source.id := by
      intro equal
      have := (List.nodup_cons.mp (List.nodup_append.mp shownNodup).2.1).1
      exact this (by simp [equal])
    rw [List.idxOf_append_of_notMem notBefore]
    simp [notTarget, List.take_append]
  have sourceShown : blockName sourceKey ∈ visible state := by
    rw [visibleEq, ← sourceName]
    simp
  let last := NotionCoreSliceForest.lastNode stored.title
  have owned : (stored.id,last) ∈ NotionCoreForestRefs.ownedRefs state.forest :=
    List.mem_flatMap.mpr ⟨stored,storedMember,List.mem_map.mpr ⟨last,lastNode_mem stored.title,rfl⟩⟩
  obtain ⟨entry,entryMember,entryName⟩ := part.refsExist _ owned
  have instanceStored : (state.instances.any fun entry => entry.1 == last.start.1) = true :=
    List.any_eq_true.mpr ⟨entry,entryMember,by simpa using entryName⟩
  obtain ⟨_,_,inst,_,instName⟩ := NotionCoreMachineCreators.replay_instance_used txs state accepted
    last.start.1 (List.mem_map.mpr ⟨entry,entryMember,entryName⟩)
  obtain ⟨stop,stopEq⟩ : ∃ stop : Option NotionRunAllocation.Id,
      last.stop = stop.map (NotionCorePhysicalReplay.address last.start.1) := by
    cases stopped : last.stop with
    | none => exact ⟨none,rfl⟩
    | some marker =>
      obtain ⟨id,rfl⟩ := NotionCoreMachineDocumentInvariant.stop_address state part _ owned marker
        (by simp [stopped])
      exact ⟨some id,rfl⟩
  refine ⟨stored,storedMember,targetMat,inst,stop,?_,?_⟩
  · simp only [mergeAnchor, NotionCoreSliceForest.anchorOf, ← instName]
    change (⟨last.start.1, _⟩ : NotionCoreSliceForest.Anchor) = ⟨last.start.1, last.stop⟩
    rw [stopEq]
  · have decodedInst : decodeBlock last.start.1 = some inst := by rw [instName]; exact decode_blockName inst
    have decodedStop : decodeStop last.start.1 last.stop = some stop := by
      rw [stopEq]; exact decodeStop_address _ stop
    simp only [prepareMerge, sourceShown, ↓reduceIte, prefixTake, ← storedName, storedFound,
      Option.bind_eq_bind, Option.bind_some]
    simp only [last] at instanceStored decodedInst decodedStop
    simp [instanceStored, decodedInst, decodedStop]

/-- A merge prepared at its honest canonical prefix executes and renders the
previous displayed block's text followed by the merged block's text, with the
merged block gone from the display. Replay structure, the anchor, its holder
and the source-document correspondence are derived. -/
theorem canonical_prepared_merge_effect (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (before gap afterBlocks : NotionCoreSourceDocument.Document) (target source : Block)
    (materialized : materializeDocument state = some (before ++ target :: gap ++ source :: afterBlocks))
    (targetAlive : target.alive = true) (sourceAlive : source.alive = true)
    (gapDead : ∀ block ∈ gap, block.alive = false)
    (sourceKey : BlockKey) (sourceName : source.id = blockName sourceKey)
    (prepared : prepareMerge state sourceKey = some tx.payload) :
    ∃ next after, applyTransaction state tx = some next ∧ materializeDocument next = some after ∧
      render next = some (NotionCoreSpec.view (NotionCoreSourceDocument.project before) ++
        [(target.id,NotionCoreSpec.text target.project.slots ++ NotionCoreSpec.text source.project.slots)] ++
        NotionCoreSpec.view (NotionCoreSourceDocument.project afterBlocks)) := by
  obtain ⟨checked,checkedReplay,part,shape,_⟩ := NotionCoreMachineHonestReplay.honest_prefix_reconstruct
    network reachable peer pre (tx :: suffix) position
  have same : checked = state := Option.some.inj (checkedReplay.symm.trans accepted)
  subst checked
  have unique := NotionCoreMachineMarkerProgress.canonical_physical_unique_all network
    (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))
    peer pre (tx :: suffix) position state accepted
  have aligned := NotionCoreMachineDisplay.replay_aligned {} state pre
    (by simp [NotionCoreMachineDisplay.Aligned,NotionCoreDisplayOrder.Aligned,NotionCoreDisplayOrder.names,
      NotionCoreDisplayOrder.shown]) accepted
  have docUnique := NotionCoreMachineDocumentInvariant.projected_addresses_unique state part unique
    shape.2.2.2.2 aligned _ materialized
  have ids : ((before ++ target :: gap ++ source :: afterBlocks).map Block.id).Nodup := by
    rw [materialized_ids state _ materialized]
    exact aligned.2.1
  obtain ⟨stored,storedMember,targetMat,inst,stop,anchorEq,preparedEq⟩ := prepared_merge_target pre state
    accepted part aligned before gap afterBlocks target source materialized targetAlive sourceAlive gapDead
    sourceKey sourceName
  have payload : tx.payload = .merge sourceKey inst stop := Option.some.inj (prepared.symm.trans preparedEq)
  obtain ⟨next,after,transaction,extracted,execution⟩ := NotionCoreMachineDocumentMerge.canonical_merge_execution
    network reachable peer pre suffix tx position state accepted _ materialized sourceKey inst stop payload
  have stepped : NotionCoreSourceDocument.step (before ++ target :: gap ++ source :: afterBlocks)
      (.merge (blockName sourceKey) (NotionCoreMachineCommands.anchorAddress inst stop)) = some after := by
    cases execution with
    | cons _ first rest =>
      cases rest
      exact first
  have sourceMember : source ∈ before ++ target :: gap ++ source :: afterBlocks := by simp
  have sourceFound := find_doc_member _ ids source sourceMember
  rw [sourceName] at sourceFound
  have owner : NotionCoreSourceDocument.owner (before ++ target :: gap ++ source :: afterBlocks)
      (NotionCoreMachineCommands.anchorAddress inst stop) = some target := by
    rw [← (NotionCoreMachineDocumentMerge.mergeAnchor_close inst stop).1, anchorEq]
    exact NotionCoreMachineDocumentMerge.node_close_owner state aligned _ materialized docUnique stored
      storedMember _ (lastNode_mem stored.title) target targetMat
  have distinct : target.id ≠ blockName sourceKey := by
    intro equal
    have perm : ((before ++ target :: gap ++ source :: afterBlocks).map Block.id).Perm
        (target.id :: source.id :: (before ++ gap ++ afterBlocks).map Block.id) := by
      apply List.perm_iff_count.mpr
      intro x
      simp only [List.map_append, List.map_cons, List.count_append, List.count_cons]
      omega
    have nd := perm.nodup_iff.mp ids
    exact (List.nodup_cons.mp nd).1 (by simp [equal, sourceName])
  have computed : NotionCoreSourceDocument.step (before ++ target :: gap ++ source :: afterBlocks)
      (.merge (blockName sourceKey) (NotionCoreMachineCommands.anchorAddress inst stop)) =
      some ((before ++ target :: gap ++ source :: afterBlocks).map fun block =>
        if block.id = target.id then {block with slices := block.slices ++ source.slices}
        else if block.id = source.id then {block with slices := []}
        else block) := by
    simp only [NotionCoreSourceDocument.step, sourceFound, owner]
    rw [if_pos ⟨sourceAlive, distinct⟩, sourceName]
  have afterEq := Option.some.inj (stepped.symm.trans computed)
  have rendered := materialized_render next after extracted
  rw [afterEq, merged_view before gap afterBlocks target source ids targetAlive gapDead] at rendered
  exact ⟨next,after,transaction,extracted,rendered⟩

#print axioms canonical_prepared_merge_effect

private theorem replay_append (state : State) (a b : List Transaction) :
    replay state (a ++ b) = (replay state a >>= fun next => replay next b) := by
  induction a generalizing state with
  | nil => rfl
  | cons tx rest ih =>
    simp only [List.cons_append,replay]
    cases step : applyTransaction state tx <;> simp [ih]

private theorem reconstructed_partitioned (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (state : State) (reconstructed : NotionCoreReconstruction.reconstruct network peer = some state) :
    NotionCoreMachinePartition.Partitioned state := by
  obtain ⟨checked,current,part,_,_⟩ := NotionCoreMachineHonestReplay.honest_reconstruct network reachable peer
  have same : checked = state := Option.some.inj (current.symm.trans reconstructed)
  subst checked
  exact part

/-- Actual honest issuance places the merge after the issuer's received
prefix and yields the previous block's text followed by the merged block's
text, with the merged block gone from the new rendering. -/
theorem issued_merge_effect (network nextNetwork : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (sourceKey : BlockKey)
    (issued : NotionCoreMachineNetwork.issue network peer (.merge sourceKey) = some nextNetwork)
    (state : State) (reconstructed : NotionCoreReconstruction.reconstruct network peer = some state)
    (before gap afterBlocks : NotionCoreSourceDocument.Document) (target source : Block)
    (materialized : materializeDocument state = some (before ++ target :: gap ++ source :: afterBlocks))
    (targetAlive : target.alive = true) (sourceAlive : source.alive = true)
    (gapDead : ∀ block ∈ gap, block.alive = false) (sourceName : source.id = blockName sourceKey) :
    (NotionCoreReconstruction.reconstruct nextNetwork peer >>= render) =
      some (NotionCoreSpec.view (NotionCoreSourceDocument.project before) ++
        [(target.id,NotionCoreSpec.text target.project.slots ++ NotionCoreSpec.text source.project.slots)] ++
        NotionCoreSpec.view (NotionCoreSourceDocument.project afterBlocks)) := by
  have nextReach : NotionCoreMachineNetwork.Reach nextNetwork := .request peer (.merge sourceKey) reachable issued
  have aligned := NotionCoreMachineDisplay.reconstructed_aligned network peer state reconstructed
  have part := reconstructed_partitioned network reachable peer state reconstructed
  obtain ⟨_,_,_,inst,stop,_,prepared⟩ := prepared_merge_target _ state reconstructed part aligned before gap
    afterBlocks target source materialized targetAlive sourceAlive gapDead sourceKey sourceName
  cases reserved : NotionCorePayload.prepare (NotionCorePayloadNetwork.forget network) peer
      (.merge sourceKey inst stop) with
  | none => simp [NotionCoreMachineNetwork.issue,NotionCoreMachineNetwork.Request.earlyNoop,
      reconstructed,NotionCoreMachineNetwork.prepareRequest,prepared,reserved] at issued
  | some tx =>
    have networkEq : NotionCorePayloadNetwork.emit network peer (.merge sourceKey inst stop) tx =
        nextNetwork := by
      simpa [NotionCoreMachineNetwork.issue,NotionCoreMachineNetwork.Request.earlyNoop,
        reconstructed,NotionCoreMachineNetwork.prepareRequest,prepared,reserved] using issued
    have txPayload := NotionCorePayloadNetwork.prepared_payload reserved
    have nextOrder := NotionCoreMachineInsertEffects.emitted_transactions_append network
      (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))
      peer _ tx reserved (by rw [networkEq]; exact
        NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable nextReach))
    rw [networkEq] at nextOrder
    have position : NotionCoreReconstruction.transactions nextNetwork peer =
        NotionCoreReconstruction.transactions network peer ++ tx :: [] := by simpa using nextOrder
    obtain ⟨next,after,transaction,_,rendered⟩ := canonical_prepared_merge_effect nextNetwork nextReach peer
      (NotionCoreReconstruction.transactions network peer) [] tx position state reconstructed before gap
      afterBlocks target source materialized targetAlive sourceAlive gapDead sourceKey sourceName
      (by rw [txPayload]; exact prepared)
    have nextReplay : NotionCoreReconstruction.reconstruct nextNetwork peer = some next := by
      unfold NotionCoreReconstruction.reconstruct
      rw [nextOrder,replay_append]
      have oldReplay : replay {} (NotionCoreReconstruction.transactions network peer) = some state := reconstructed
      simp [oldReplay,replay,transaction,Bind.bind,Option.bind]
    simp [nextReplay,rendered]

/-- Every honest merge of a displayed block into the previous displayed
block issues successfully, and the issuer's new rendering shows the previous
block's text followed by the merged block's text, without the merged block. -/
theorem honest_merge_request_effect (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (state : State) (reconstructed : NotionCoreReconstruction.reconstruct network peer = some state)
    (before gap afterBlocks : NotionCoreSourceDocument.Document) (target source : Block)
    (materialized : materializeDocument state = some (before ++ target :: gap ++ source :: afterBlocks))
    (targetAlive : target.alive = true) (sourceAlive : source.alive = true)
    (gapDead : ∀ block ∈ gap, block.alive = false)
    (sourceKey : BlockKey) (sourceName : source.id = blockName sourceKey) :
    ∃ nextNetwork, NotionCoreMachineNetwork.issue network peer (.merge sourceKey) = some nextNetwork ∧
      (NotionCoreReconstruction.reconstruct nextNetwork peer >>= render) =
        some (NotionCoreSpec.view (NotionCoreSourceDocument.project before) ++
          [(target.id,NotionCoreSpec.text target.project.slots ++ NotionCoreSpec.text source.project.slots)] ++
          NotionCoreSpec.view (NotionCoreSourceDocument.project afterBlocks)) := by
  have aligned := NotionCoreMachineDisplay.reconstructed_aligned network peer state reconstructed
  have part := reconstructed_partitioned network reachable peer state reconstructed
  obtain ⟨_,_,_,_,_,_,prepared⟩ := prepared_merge_target _ state reconstructed part aligned before gap
    afterBlocks target source materialized targetAlive sourceAlive gapDead sourceKey sourceName
  have success : ∃ next, NotionCoreMachineNetwork.issue network peer (.merge sourceKey) = some next := by
    simp [NotionCoreMachineNetwork.issue,NotionCoreMachineNetwork.Request.earlyNoop,
      reconstructed,NotionCoreMachineNetwork.prepareRequest,prepared,NotionCorePayload.prepare,
      NotionCorePayload.Payload.emits]
  obtain ⟨next,issued⟩ := success
  exact ⟨next,issued,issued_merge_effect network next reachable peer sourceKey issued state reconstructed
    before gap afterBlocks target source materialized targetAlive sourceAlive gapDead sourceName⟩

#print axioms prepared_merge_target
#print axioms issued_merge_effect
#print axioms honest_merge_request_effect

namespace SPOT
private def x : NotionRunAllocation.Id := ⟨3,[66]⟩
private def created := replay {} [NotionCorePayload.bootstrap [97],⟨x,.create (some .initial)⟩,
  ⟨⟨4,[66]⟩,.insert (.issued x) (.issued x) .start [98]⟩]
private def afterMerge : Option (List (Nat × List Nat)) := do
  let state ← created
  let payload ← prepareMerge state (.issued x)
  applyTransaction state ⟨⟨5,[66]⟩,payload⟩ >>= render

/-- Merging the second block into the first shows ab in the first block and
removes the second. The first block has no previous block, so its merge is
not prepared. Appending in the wrong order and keeping both blocks are
excluded. -/
theorem merge_request_control :
    afterMerge = some [(0,[97,98])] ∧
    (created >>= fun state => prepareMerge state .initial) = none ∧
    afterMerge ≠ some [(0,[98,97])] ∧
    afterMerge ≠ some [(0,[97]),(blockName (.issued x),[98])] := by decide +kernel
end SPOT

end Sal.MRDTs.Instances.NotionCoreMachineMergeEffects
