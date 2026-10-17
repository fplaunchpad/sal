import Sal.MRDTs.Instances.NotionCoreMachineDocumentErase
import Sal.MRDTs.Instances.NotionCoreMachineDeleteTotal

/-! Actual positional deletion selects the independent specification's visible
identities, grouped by text instance. The source range codec permutes those
identities within each group; erasure depends only on membership. Local
effects use independent source preparation lemmas. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineDocumentClient
open NotionCoreMachine
open NotionCoreMachineDocument
open NotionCoreMachineClient
open NotionCoreMachineDelete
open NotionCoreSpec (Address)
open NotionCoreSource (Atom Slice Block)
open NotionCorePayload (BlockKey Payload Transaction)
open NotionCorePreparation (nodes characters deleteTargets)

/-- Checked client chain extraction equals the materialized source block's
slices; this is a projection equality, not replay. -/
theorem materialized_nodes (state : State) (stored : NotionCoreSliceForest.Block) (source : Block)
    (accepted : materializeBlock state stored = some source) :
    materialize state stored.title = some (nodes source) :=
  (materialized_slices state stored source accepted).1

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

/-- A displayed alive materialized source block determines the actual checked
client slices of that same requested block. -/
theorem document_block_slices (state : State)
    (document : NotionCoreSourceDocument.Document) (materialized : materializeDocument state = some document)
    (source : Block) (member : source ∈ document) (alive : source.alive = true)
    (block : BlockKey) (name : source.id = blockName block) :
    blockSlices state block = some (nodes source) := by
  obtain ⟨bid,displayed,decoded⟩ := mapM_member _ state.display document materialized source member
  have named : source.id = bid := materialized_named_id state bid source decoded
  have same : bid = blockName block := named.symm.trans name
  cases found : state.forest.find? (fun old => old.id == bid) with
  | none =>
    rw [materializeEntry_tombstone state bid found] at decoded
    cases decoded
    simp [Block.alive] at alive
  | some stored =>
    rw [materializeEntry_stored state bid stored found] at decoded
    have slices := materialized_nodes state stored source decoded
    simpa [blockSlices,← same,found] using slices

/-- A displayed tombstone names a block with no stored chain. -/
theorem document_block_tombstone (state : State)
    (document : NotionCoreSourceDocument.Document) (materialized : materializeDocument state = some document)
    (source : Block) (member : source ∈ document) (dead : source.alive = false)
    (block : BlockKey) (name : source.id = blockName block) :
    blockSlices state block = none := by
  obtain ⟨bid,displayed,decoded⟩ := mapM_member _ state.display document materialized source member
  have named : source.id = bid := materialized_named_id state bid source decoded
  have same : bid = blockName block := named.symm.trans name
  cases found : state.forest.find? (fun old => old.id == bid) with
  | none => simp [blockSlices,← same,found]
  | some stored =>
    rw [materializeEntry_stored state bid stored found] at decoded
    have live := materialized_alive state stored source decoded
    rw [live] at dead
    contradiction

/-- Each prepared group's targets, as physical addresses, permute the run of
selected addresses it was decoded from. -/
private theorem groups_targets (txs : List Transaction) (state : State)
    (accepted : replay {} txs = some state) (runs : List (Nat × List Address))
    (present : ∀ run ∈ runs, ∀ address ∈ run.2, address ∈ (physical state address.1).map Atom.address)
    (groups : List (BlockKey × List NotionRunAllocation.Id))
    (grouped : runs.mapM prepareGroup = some groups) :
    (groups.flatMap fun group => group.2.map (NotionCorePhysicalReplay.address (blockName group.1))).Perm
      (runs.flatMap Prod.snd) := by
  induction runs generalizing groups with
  | nil => simp at grouped; subst groups; simp
  | cons run rest ih =>
    simp only [List.mapM_cons] at grouped
    obtain ⟨group,first,later⟩ := Option.bind_eq_some_iff.mp grouped
    obtain ⟨tail,following,same⟩ := Option.bind_eq_some_iff.mp later
    have equal := Option.some.inj same
    subst groups
    obtain ⟨_,ids,decoded,sortedEq⟩ := group_data run group.1 group.2 first
    have raw := decodeTargets_roundtrip txs state accepted group.1 run.2 ids
      (present run (by simp)) decoded
    have single : (group.2.map (NotionCorePhysicalReplay.address (blockName group.1))).Perm run.2 := by
      rw [sortedEq, ← raw]
      exact (NotionCoreRanges.sorted_perm ids).map _
    simp only [List.flatMap_cons]
    exact single.append (ih (fun other member => present other (List.mem_cons_of_mem _ member)) tail following)

/-- Source compression/sorting preserves precisely the visible identity
selection, up to permutation, across all instance groups. Neither the target
list nor its order is assumed. -/
theorem selectErase_targets (txs : List Transaction) (state : State)
    (accepted : replay {} txs = some state)
    (document : NotionCoreSourceDocument.Document) (materialized : materializeDocument state = some document)
    (source : Block) (member : source ∈ document) (alive : source.alive = true)
    (block : BlockKey) (name : source.id = blockName block)
    (start stop : Nat) (payload : Payload) (prepared : selectErase state block start stop = some payload) :
    ∃ groups, payload = .erase block groups ∧
      (groups.flatMap fun group => group.2.map (NotionCorePhysicalReplay.address (blockName group.1))).Perm
        (deleteTargets source start stop) := by
  obtain ⟨addresses,groups,selected,grouped,equal⟩ := selection_groups state block start stop payload prepared
  have slices := document_block_slices state document materialized source member alive block name
  have addressesEq : addresses = deleteTargets source start stop := by
    unfold deleteAddresses at selected
    split at selected
    · contradiction
    · simp only [slices,Bind.bind,Option.bind] at selected
      split at selected
      · contradiction
      · simpa only [Option.some.injEq,deleteTargets] using selected.symm
  refine ⟨groups,equal,?_⟩
  have permutation := groups_targets txs state accepted (runs addresses)
    (fun run runMember address inside => delete_physical_member state block start stop addresses selected
      address (by rw [← runs_flatten addresses]; exact List.mem_flatMap.mpr ⟨run,runMember,inside⟩))
    groups grouped
  rw [runs_flatten, addressesEq] at permutation
  exact permutation

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
  congr 1
  apply List.map_congr_left
  intro slice _
  congr 1
  apply List.map_congr_left
  exact fun atom _ => eraseAtom_perm a b permutation atom

/-- Successful actual positional preparation selects exactly the natural
range-delete command modulo source codec sorting and instance grouping. The
actual operations then have the independent local effect on this block,
leaving all other views intact. -/
theorem prepared_erase_effect (txs : List Transaction) (state result : State)
    (accepted : replay {} txs = some state)
    (pre post : NotionCoreSourceDocument.Document) (source : Block)
    (materialized : materializeDocument state = some (pre ++ source :: post))
    (alive : source.alive = true)
    (block : BlockKey) (name : source.id = blockName block)
    (start stop : Nat) (groups : List (BlockKey × List NotionRunAllocation.Id))
    (prepared : selectErase state block start stop = some (.erase block groups))
    (operations : applyOperations state (groups.map fun group => .erase block group.1 group.2) = some result)
    (unique : (NotionCoreInvariant.addresses (NotionCoreSourceDocument.project (pre ++ source :: post))).Nodup)
    (ordered : start ≤ stop) :
    ∃ after, materializeDocument result = some after ∧
      NotionCoreSpec.view (NotionCoreSourceDocument.project after) =
        NotionCoreSpec.view (NotionCoreSourceDocument.project pre) ++
        [(source.id,(NotionCoreSpec.text source.project.slots).take start ++
          (NotionCoreSpec.text source.project.slots).drop stop)] ++
        NotionCoreSpec.view (NotionCoreSourceDocument.project post) := by
  obtain ⟨actual,equal,permutation⟩ := selectErase_targets txs state accepted _ materialized source
    (by simp) alive block name start stop _ prepared
  have same : groups = actual := by simpa using equal
  subst same
  have extracted := NotionCoreMachineDocumentErase.materializeDocument_erase_groups state result block groups
    _ operations materialized
  obtain ⟨expected,step,effect⟩ := NotionCorePreparation.source_delete_effect pre post source start stop
    unique alive ordered
  have sourceStep : NotionCoreSourceDocument.step (pre ++ source :: post)
      (.delete (groups.flatMap fun group =>
        group.2.map (NotionCorePhysicalReplay.address (blockName group.1)))) =
      some ((pre ++ source :: post).map (NotionCoreSourceDocument.eraseBlock (groups.flatMap fun group =>
        group.2.map (NotionCorePhysicalReplay.address (blockName group.1))))) := rfl
  rw [delete_step_perm _ _ _ permutation,step] at sourceStep
  exact ⟨_,extracted,(Option.some.inj sourceStep) ▸ effect⟩

#print axioms materialized_nodes
#print axioms document_block_slices
#print axioms selectErase_targets
#print axioms prepared_erase_effect

/-- A valid nonempty positional deletion both prepares and executes with the
independent local visible effect. Preparation and operation acceptance are
conclusions, not premises; global retained-address uniqueness is structural. -/
theorem erase_request_effect (txs : List Transaction) (state : State)
    (accepted : replay {} txs = some state)
    (part : NotionCoreMachinePartition.Partitioned state)
    (physicalUnique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (pre post : NotionCoreSourceDocument.Document) (source : Block)
    (materialized : materializeDocument state = some (pre ++ source :: post))
    (block : BlockKey) (name : source.id = blockName block)
    (start stop : Nat) (nonempty : start < stop)
    (bound : stop ≤ NotionCoreMachineDeleteTotal.visibleLength state block)
    (unique : (NotionCoreInvariant.addresses (NotionCoreSourceDocument.project (pre ++ source :: post))).Nodup) :
    ∃ groups result after,
      selectErase state block start stop = some (.erase block groups) ∧
      applyOperations state (groups.map fun group => .erase block group.1 group.2) = some result ∧
      materializeDocument result = some after ∧
      NotionCoreSpec.view (NotionCoreSourceDocument.project after) =
        NotionCoreSpec.view (NotionCoreSourceDocument.project pre) ++
        [(source.id,(NotionCoreSpec.text source.project.slots).take start ++
          (NotionCoreSpec.text source.project.slots).drop stop)] ++
        NotionCoreSpec.view (NotionCoreSourceDocument.project post) := by
  have alive : source.alive = true := by
    cases live : source.alive
    · have none := document_block_tombstone state _ materialized source (by simp) live block name
      simp [NotionCoreMachineDeleteTotal.visibleLength,none] at bound
      omega
    · rfl
  have clientSlices := document_block_slices state _ materialized source (by simp) alive block name
  have stored : ∃ found ∈ state.forest, found.id = blockName block := by
    cases found : state.forest.find? (fun old => old.id == blockName block) with
    | none => simp [blockSlices,found] at clientSlices
    | some entry => exact ⟨entry,List.mem_of_find?_eq_some found,by simpa using List.find?_some found⟩
  obtain ⟨groups,prepared,_,_⟩ := NotionCoreMachineDeleteTotal.selectErase_total txs state accepted part
    physicalUnique block stored start stop nonempty bound
  obtain ⟨result,operations⟩ := NotionCoreMachineDocumentErase.erase_groups_total state block groups
  obtain ⟨after,extracted,effect⟩ := prepared_erase_effect txs state result accepted pre post source
    materialized alive block name start stop groups prepared operations unique (by omega)
  exact ⟨groups,result,after,prepared,operations,extracted,effect⟩

#print axioms erase_request_effect

namespace SPOT
private def cut : Transaction := ⟨⟨3,[66]⟩,.split .initial .initial (.item ⟨1,[65]⟩)⟩
private def eraseView (state : State) : Option (List (Nat × List Nat)) := do
  let payload ← selectErase state (.issued cut.id) 0 1
  match payload with
  | .erase block groups =>
    (applyOperations state (groups.map fun group => .erase block group.1 group.2) >>=
      materializeDocument).map
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

/-- Source nodes retain exactly the independent projected slots, including
the otherwise invisible dead title and slice start anchors. -/
theorem nodes_project_slots (source : Block) :
    (nodes source).flatMap Slice.slots = source.project.slots := rfl

#print axioms nodes_project_slots
end Sal.MRDTs.Instances.NotionCoreMachineDocumentClient
