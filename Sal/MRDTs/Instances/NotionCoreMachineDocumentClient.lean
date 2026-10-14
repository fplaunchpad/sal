import Sal.MRDTs.Instances.NotionCoreMachineDocumentErase
import Sal.MRDTs.Instances.NotionCoreMachineDeleteTotal

/-! Actual positional deletion selects the independent specification's visible
identities. The source range codec permutes those identities; erasure depends
only on membership. Local effects use independent source preparation lemmas. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineDocumentClient
open NotionCoreMachine
open NotionCoreMachineDocument
open NotionCoreMachineClient
open NotionCoreMachineDelete
open NotionCoreSpec (Address)
open NotionCoreSource (Atom Slice Block)
open NotionCorePayload (BlockKey Payload Transaction)
open NotionCorePreparation (nodes characters deleteTargets)

/-- Checked client node extraction equals the existing source block's nodes,
including the empty attached title; this is a projection equality, not replay. -/
theorem materialized_nodes (state : State) (stored : NotionCoreSliceForest.Block) (source : Block)
    (normal : NotionCoreSliceForest.Normal stored.id stored.title)
    (empty : NotionCoreSliceForest.attached stored.title = true →
      physical state stored.id = NotionCoreSliceForest.emptyPhysical stored.id)
    (titleExists : NotionCoreSliceForest.attached stored.title = true →
      state.instances.any (fun entry => entry.1 == stored.id) = true)
    (accepted : materializeBlock state stored = some source) :
    materialize state stored.title = some (nodes source) := by
  cases stored with
  | mk bid tree =>
    change NotionCoreSliceForest.Normal bid tree at normal
    cases normal with
    | own stop =>
      cases extracted : sliceAtoms state ⟨(bid,.start),stop⟩ with
      | none => simp [materializeBlock,NotionCoreSliceForest.active,NotionCoreSliceForest.Tree.children,
          NotionCoreSliceForest.Tree.slice,extracted] at accepted
      | some atoms =>
        have sourceEq : source = ⟨bid,.own,⟨(bid,.start),atoms⟩⟩ := by
          simpa [materializeBlock,NotionCoreSliceForest.active,NotionCoreSliceForest.attached,
            NotionCoreSliceForest.Tree.children,NotionCoreSliceForest.Tree.slice,extracted] using accepted.symm
        simp [materialize,NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.preorderChildren,
          extracted,sourceEq,nodes]
    | attached ref =>
      have root := NotionCoreMachineSlices.empty_title_atoms state bid (titleExists rfl) (empty rfl)
      simp only [NotionCoreSliceForest.titleRef] at root
      cases extracted : sliceAtoms state ref with
      | none => simp [materializeBlock,NotionCoreSliceForest.active,NotionCoreSliceForest.Tree.children,
          NotionCoreSliceForest.Tree.slice,extracted] at accepted
      | some atoms =>
        have sourceEq : source = ⟨bid,.attached bid,⟨ref.start,atoms⟩⟩ := by
          simpa [materializeBlock,NotionCoreSliceForest.active,NotionCoreSliceForest.attached,
            NotionCoreSliceForest.Tree.children,NotionCoreSliceForest.Tree.slice,extracted] using accepted.symm
        simp [materialize,NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.preorderChildren,
          root,extracted,sourceEq,nodes,NotionCoreSliceForest.titleRef]

private theorem decoder_physical_roundtrip (txs : List Transaction) (state : State)
    (accepted : replay {} txs = some state) (address : Address)
    (present : address ∈ (physical state address.1).map Atom.address)
    (inst : BlockKey) (id : NotionRunAllocation.Id)
    (decoded : decodeAddress address = some (inst,.item id)) :
    NotionCorePhysicalReplay.address (blockName inst) id = address := by
  simp only [physical,NotionCorePhysicalReplay.physical,List.map_cons,List.mem_cons,List.mem_map] at present
  rcases present with start | ⟨atom,⟨item,member,equal⟩,addressEq⟩
  · have startId : address.2 = .start := congrArg Prod.snd start
    cases block : decodeBlock address.1 <;> simp [decodeAddress,startId,decodeOrigin,block] at decoded
  · subst atom
    obtain ⟨row,rowMember,itemEq⟩ := NotionCoreMachineBirths.traversal_row_member _ _ _ item member
    obtain ⟨tx,txMember,key,keyName,born⟩ := NotionCoreMachineBirths.replay_row_birth txs state accepted address.1 row rowMember
    have encoded : NotionCorePhysicalReplay.originAddress (blockName key) (.item item.id) = address := by
      simpa [NotionCorePhysicalReplay.originAddress,keyName] using addressEq
    have same := decode_originAddress key (.item item.id)
    rw [encoded,decoded] at same
    have pairEq := Option.some.inj same
    have instEq : inst = key := congrArg Prod.fst pairEq
    have idEq : id = item.id := NotionCoreOriginTree.Origin.item.inj (congrArg Prod.snd pairEq)
    simpa only [instEq,idEq,NotionCorePhysicalReplay.originAddress] using encoded

private theorem decodeTarget_source (inst : BlockKey) (address : Address) (id : NotionRunAllocation.Id)
    (decoded : decodeTarget inst address = some id) : decodeAddress address = some (inst,.item id) := by
  unfold decodeTarget at decoded
  split at decoded <;> try contradiction
  split at decoded <;> simp_all

/-- Decoding retained physical addresses loses no identity information. -/
theorem decodeTargets_roundtrip (txs : List Transaction) (state : State)
    (accepted : replay {} txs = some state) (inst : BlockKey)
    (addresses : List Address) (ids : List NotionRunAllocation.Id)
    (present : ∀ address ∈ addresses, address ∈ (physical state address.1).map Atom.address)
    (decoded : decodeTargets inst addresses = some ids) :
    ids.map (NotionCorePhysicalReplay.address (blockName inst)) = addresses := by
  induction addresses generalizing ids with
  | nil => simp [decodeTargets] at decoded; subst ids; rfl
  | cons first rest ih =>
    cases one : decodeTarget inst first with
    | none => simp [decodeTargets,one] at decoded
    | some id =>
      cases later : decodeTargets inst rest with
      | none =>
        have laterMap := later
        simp only [decodeTargets] at laterMap
        simp [decodeTargets,one,laterMap] at decoded
      | some tail =>
        have laterMap := later
        simp only [decodeTargets] at laterMap
        have equal : id :: tail = ids := by simpa [decodeTargets,one,laterMap] using decoded
        subst ids
        have firstEq := decoder_physical_roundtrip txs state accepted first
          (present first (by simp)) inst id (decodeTarget_source inst first id one)
        have restEq := ih tail (fun address member => present address (List.mem_cons_of_mem _ member)) later
        simp [firstEq,restEq]

private theorem mapM_member {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (accepted : xs.mapM f = some ys) (value : β) (member : value ∈ ys) :
    ∃ x ∈ xs, f x = some value := by
  induction xs generalizing ys with
  | nil => simp at accepted; subst ys; simp at member
  | cons first rest ih =>
    cases one : f first with
    | none => simp [List.mapM_cons,one] at accepted
    | some head =>
      cases later : rest.mapM f with
      | none => simp [List.mapM_cons,one,later] at accepted
      | some tail =>
        have equal : head :: tail = ys := by simpa [List.mapM_cons,one,later] using accepted
        subst ys
        rcases List.mem_cons.mp member with rfl | inside
        · exact ⟨first,by simp,one⟩
        · obtain ⟨x,present,found⟩ := ih tail later inside
          exact ⟨x,List.mem_cons_of_mem _ present,found⟩

/-- A displayed materialized source block determines the actual checked
client slices of that same requested block. -/
theorem document_block_slices (state : State)
    (part : NotionCoreMachinePartition.Partitioned state) (shape : NotionCoreMachineShape.ShapeInvariant state)
    (document : NotionCoreSourceDocument.Document) (materialized : materializeDocument state = some document)
    (source : Block) (member : source ∈ document) (block : BlockKey) (name : source.id = blockName block) :
    blockSlices state block = some (nodes source) := by
  obtain ⟨bid,displayed,decoded⟩ := mapM_member _ state.display document materialized source member
  have named : source.id = bid := materialized_named_id state bid source decoded
  cases found : state.forest.find? (fun old => old.id == bid) with
  | none => simp [found] at decoded
  | some stored =>
    have storedMember := List.mem_of_find?_eq_some found
    have sourceAccepted : materializeBlock state stored = some source := by simpa [found] using decoded
    have rootName : stored.title.slice.start.1 = stored.id := by
      have normal := shape.1 stored storedMember
      rcases stored with ⟨id,title⟩
      change NotionCoreSliceForest.Normal id title at normal
      cases normal <;> rfl
    have titleMember : (stored.id,stored.title.slice) ∈ NotionCoreForestRefs.ownedRefs state.forest := by
      apply List.mem_flatMap.mpr
      refine ⟨stored,storedMember,List.mem_map.mpr ⟨stored.title.slice,?_,rfl⟩⟩
      cases stored.title; simp [NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.Tree.slice]
    have titleExists : state.instances.any (fun entry => entry.1 == stored.id) = true := by
      simpa [rootName] using part.refsExist _ titleMember
    have titleEmpty : NotionCoreSliceForest.attached stored.title = true →
        physical state stored.id = NotionCoreSliceForest.emptyPhysical stored.id := by
      intro attached
      exact shape.2.2 _ (List.mem_map.mpr ⟨stored,storedMember,rfl⟩) attached
    have slices := materialized_nodes state stored source (shape.1 stored storedMember) titleEmpty
      (fun _ => titleExists) sourceAccepted
    have same : bid = blockName block := named.symm.trans name
    simpa [blockSlices,← same,found] using slices

private theorem selection_data (state : State) (block : BlockKey) (start stop : Nat) (payload : Payload)
    (prepared : selectErase state block start stop = some payload) :
    ∃ addresses inst ids, deleteAddresses state block start stop = some addresses ∧
      decodeTargets inst addresses = some ids ∧ payload = .erase block inst (NotionCoreRanges.sorted ids) := by
  cases selected : deleteAddresses state block start stop with
  | none => simp [selectErase,selected] at prepared
  | some addresses =>
    cases head : addresses.head? with
    | none => simp [selectErase,selected,head] at prepared
    | some first =>
      cases decoded : decodeAddress first with
      | none => simp [selectErase,selected,head,decoded] at prepared
      | some pair =>
        rcases pair with ⟨inst,origin⟩
        cases origin with
        | start => simp [selectErase,selected,head,decoded] at prepared
        | item id =>
          cases ids : decodeTargets inst addresses with
          | none => simp [selectErase,prepareErase,selected,head,decoded,ids] at prepared
          | some raw =>
            have equal : payload = .erase block inst (NotionCoreRanges.sorted raw) := by
              simpa [selectErase,prepareErase,selected,head,decoded,ids,NotionCoreRanges.expand_compress] using prepared.symm
            exact ⟨addresses,inst,raw,rfl,ids,equal⟩

/-- Source compression/sorting preserves precisely the visible identity
selection, up to permutation. Neither the target list nor its order is assumed. -/
theorem selectErase_targets (txs : List Transaction) (state : State)
    (accepted : replay {} txs = some state)
    (part : NotionCoreMachinePartition.Partitioned state) (shape : NotionCoreMachineShape.ShapeInvariant state)
    (document : NotionCoreSourceDocument.Document) (materialized : materializeDocument state = some document)
    (source : Block) (member : source ∈ document) (block : BlockKey) (name : source.id = blockName block)
    (start stop : Nat) (payload : Payload) (prepared : selectErase state block start stop = some payload) :
    ∃ inst ids, payload = .erase block inst ids ∧
      (ids.map (NotionCorePhysicalReplay.address (blockName inst))).Perm (deleteTargets source start stop) := by
  obtain ⟨addresses,inst,ids,selected,decoded,equal⟩ := selection_data state block start stop payload prepared
  have raw := decodeTargets_roundtrip txs state accepted inst addresses ids
    (fun address member => delete_physical_member state block start stop addresses selected address member) decoded
  have slices := document_block_slices state part shape document materialized source member block name
  have addressesEq : addresses = deleteTargets source start stop := by
    unfold deleteAddresses at selected
    split at selected
    · contradiction
    · simp only [slices,Bind.bind,Option.bind] at selected
      split at selected
      · contradiction
      · simpa only [Option.some.injEq,deleteTargets] using selected.symm
  refine ⟨inst,NotionCoreRanges.sorted ids,equal,?_⟩
  have permutation := (NotionCoreRanges.sorted_perm ids).map (NotionCorePhysicalReplay.address (blockName inst))
  simpa only [raw,addressesEq] using permutation

private theorem eraseAtom_perm (a b : List Address) (permutation : a.Perm b) (atom : Atom) :
    NotionCoreSource.eraseAtom a atom = NotionCoreSource.eraseAtom b atom := by
  have contains : a.contains atom.address = b.contains atom.address := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.contains_iff_mem]
    exact permutation.mem_iff
  unfold NotionCoreSource.eraseAtom
  rw [contains]

/-- Codec reordering cannot change an independent delete transition. -/
theorem delete_step_perm (document : NotionCoreSourceDocument.Document)
    (a b : List Address) (permutation : a.Perm b) :
    NotionCoreSourceDocument.step document (.delete a) =
      NotionCoreSourceDocument.step document (.delete b) := by
  simp only [NotionCoreSourceDocument.step]
  congr 1
  apply List.map_congr_left
  intro block member
  unfold NotionCoreSourceDocument.eraseBlock NotionCoreSource.eraseSlice
  congr 2
  apply List.map_congr_left
  exact fun atom _ => eraseAtom_perm a b permutation atom

/-- Successful actual positional preparation selects exactly the natural
range-delete command modulo source codec sorting. The actual operation then
has the independent local effect on this block, leaving all other views intact. -/
theorem prepared_erase_effect (txs : List Transaction) (state result : State)
    (accepted : replay {} txs = some state)
    (part : NotionCoreMachinePartition.Partitioned state) (shape : NotionCoreMachineShape.ShapeInvariant state)
    (pre post : NotionCoreSourceDocument.Document) (source : Block)
    (materialized : materializeDocument state = some (pre ++ source :: post))
    (block inst : BlockKey) (name : source.id = blockName block)
    (start stop : Nat) (ids : List NotionRunAllocation.Id)
    (prepared : selectErase state block start stop = some (.erase block inst ids))
    (operation : applyOperation state (.erase block inst ids) = some result)
    (unique : (NotionCoreInvariant.addresses (NotionCoreSourceDocument.project (pre ++ source :: post))).Nodup)
    (ordered : start ≤ stop) :
    ∃ after, materializeDocument result = some after ∧
      NotionCoreSpec.view (NotionCoreSourceDocument.project after) =
        NotionCoreSpec.view (NotionCoreSourceDocument.project pre) ++
        [(source.id,(NotionCoreSpec.text source.project.slots).take start ++
          (NotionCoreSpec.text source.project.slots).drop stop)] ++
        NotionCoreSpec.view (NotionCoreSourceDocument.project post) := by
  obtain ⟨actual,targets,equal,permutation⟩ := selectErase_targets txs state accepted part shape _ materialized source
    (by simp) block name start stop _ prepared
  have same : inst = actual ∧ ids = targets := by simpa using equal
  obtain ⟨rfl,rfl⟩ := same
  obtain ⟨after,extracted,sourceStep⟩ := NotionCoreMachineDocumentErase.erase_source_step
    state result block inst ids _ operation materialized
  obtain ⟨expected,step,effect⟩ := NotionCorePreparation.source_delete_effect pre post source start stop unique ordered
  rw [delete_step_perm _ _ _ permutation,step] at sourceStep
  have afterEq : expected = after := Option.some.inj sourceStep
  exact ⟨after,extracted,afterEq ▸ effect⟩

#print axioms materialized_nodes
#print axioms document_block_slices
#print axioms selectErase_targets
#print axioms prepared_erase_effect

/-- A valid nonempty positional deletion both prepares and executes with the
independent local visible effect. Preparation and operation acceptance are
conclusions, not premises; global retained-address uniqueness is structural. -/
theorem erase_request_effect (txs : List Transaction) (state : State)
    (accepted : replay {} txs = some state)
    (part : NotionCoreMachinePartition.Partitioned state) (shape : NotionCoreMachineShape.ShapeInvariant state)
    (physicalUnique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (pre post : NotionCoreSourceDocument.Document) (source : Block)
    (materialized : materializeDocument state = some (pre ++ source :: post))
    (block : BlockKey) (name : source.id = blockName block)
    (start stop : Nat) (nonempty : start < stop)
    (bound : stop ≤ NotionCoreMachineDeleteTotal.visibleLength state block)
    (unique : (NotionCoreInvariant.addresses (NotionCoreSourceDocument.project (pre ++ source :: post))).Nodup) :
    ∃ inst ids result after,
      selectErase state block start stop = some (.erase block inst ids) ∧
      applyOperation state (.erase block inst ids) = some result ∧
      materializeDocument result = some after ∧
      NotionCoreSpec.view (NotionCoreSourceDocument.project after) =
        NotionCoreSpec.view (NotionCoreSourceDocument.project pre) ++
        [(source.id,(NotionCoreSpec.text source.project.slots).take start ++
          (NotionCoreSpec.text source.project.slots).drop stop)] ++
        NotionCoreSpec.view (NotionCoreSourceDocument.project post) := by
  have clientSlices := document_block_slices state part shape _ materialized source (by simp) block name
  have stored : ∃ found ∈ state.forest, found.id = blockName block := by
    cases found : state.forest.find? (fun old => old.id == blockName block) with
    | none => simp [blockSlices,found] at clientSlices
    | some entry => exact ⟨entry,List.mem_of_find?_eq_some found,by simpa using List.find?_some found⟩
  obtain ⟨inst,raw,prepared,_⟩ := NotionCoreMachineDeleteTotal.selectErase_total txs state accepted part shape
    physicalUnique block stored start stop nonempty bound
  let ids := NotionCoreRanges.sorted raw
  let result := putInstance state (blockName inst)
    ⟨NotionCoreParentErase.erase ids (getInstance state (blockName inst)).rows,
      (getInstance state (blockName inst)).pending ++ ids⟩
  have operation : applyOperation state (.erase block inst ids) = some result := rfl
  obtain ⟨after,extracted,effect⟩ := prepared_erase_effect txs state result accepted part shape pre post source
    materialized block inst name start stop ids prepared operation unique (by omega)
  exact ⟨inst,ids,result,after,prepared,operation,extracted,effect⟩

#print axioms erase_request_effect

namespace SPOT
private def cut : Transaction := ⟨⟨3,[66]⟩,.split .initial .initial (.item ⟨1,[65]⟩)⟩
private def eraseView (state : State) : Option (List (Nat × List Nat)) := do
  let payload ← selectErase state (.issued cut.id) 0 1
  match payload with
  | .erase block inst ids =>
    (applyOperation state (.erase block inst ids) >>= materializeDocument).map
      (fun document => NotionCoreSpec.view (NotionCoreSourceDocument.project document))
  | _ => none
/-- Selecting b in the inherited leaf empties that displayed block and leaves
its preceding a block untouched. Unused destination-title IDs are not targets. -/
theorem inherited_range_effect_control :
    (replay {} [NotionCorePayload.bootstrap [97,98],cut] >>= eraseView) =
      some [(0,[97]),(blockName (.issued cut.id),[])] ∧
    (replay {} [NotionCorePayload.bootstrap [97,98],cut] >>= eraseView) ≠
      some [(0,[]),(blockName (.issued cut.id),[98])] ∧
    (replay {} [NotionCorePayload.bootstrap [97,98],cut] >>= eraseView) ≠
      some [(0,[97]),(blockName (.issued cut.id),[98])] := by decide +kernel
end SPOT

/-- Existing source nodes retain exactly the independent projected slots,
including the otherwise invisible empty title and active start anchors. -/
theorem nodes_project_slots (source : Block) :
    (nodes source).flatMap Slice.slots = source.project.slots := by
  cases source with
  | mk id shape slice =>
    cases shape <;> simp [nodes,Block.project,Slice.slots,Slice.anchor,NotionCoreSpec.root]

#print axioms nodes_project_slots
end Sal.MRDTs.Instances.NotionCoreMachineDocumentClient
