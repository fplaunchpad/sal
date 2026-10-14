import Sal.MRDTs.Instances.NotionCoreMachineDelete
import Sal.MRDTs.Instances.NotionCoreMachineClientShape
import Sal.MRDTs.Instances.NotionCoreMachineHonestReplay

/-! Total supported nonempty erase preparation in the no-merge normal shape.
Visible positions count source iterator atoms. This concerns actual internal
selection/codec validation; source wire parsing and JavaScript extraction are
separate boundaries. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineDeleteTotal
open NotionCoreMachine
open NotionCoreMachineClient
open NotionCoreMachineDelete
open NotionCoreMachineShape (ShapeInvariant)
open NotionCoreMachinePartition (Partitioned)
open NotionCorePayload (BlockKey Payload Transaction)
open NotionCoreSource (Atom Slice)
open NotionCoreSpec (Address)
open NotionCoreSliceForest (Normal active)
open NotionCorePreparation (characters visibleAtom)

private theorem mapM_success {α β : Type} (f : α → Option β) (xs : List α)
    (success : ∀ x ∈ xs, ∃ y, f x = some y) : ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons head rest ih =>
    obtain ⟨value,first⟩ := success head (by simp)
    obtain ⟨tail,later⟩ := ih (fun x member => success x (List.mem_cons_of_mem _ member))
    exact ⟨value :: tail,by simp [first,later]⟩

/-- Every stored forest block materializes by its actual checked endpoint
scans; no successful materialization is assumed. -/
theorem materialize_total (state : State) (part : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (found : NotionCoreSliceForest.Block) (member : found ∈ state.forest) :
    ∃ slices, materialize state found.title = some slices := by
  apply mapM_success
  intro ref inTree
  have owned : (found.id,ref) ∈ NotionCoreForestRefs.ownedRefs state.forest :=
    List.mem_flatMap.mpr ⟨found,member,List.mem_map.mpr ⟨ref,inTree,rfl⟩⟩
  obtain ⟨atoms,extracted⟩ := NotionCoreMachinePartition.ref_extracts state part unique (found.id,ref) owned
  exact ⟨⟨ref.start,atoms⟩,by simp [extracted]⟩

/-- The unused title contributes no visible atom. All visible atoms belong
to the one active slice, including after arbitrary splits and tombstones. -/
theorem normal_visible_instance (state : State) (bid : Nat) (tree : NotionCoreSliceForest.Tree)
    (normal : Normal bid tree)
    (empty : NotionCoreSliceForest.attached tree = true →
      physical state bid = NotionCoreSliceForest.emptyPhysical bid)
    (slices : List Slice) (materialized : materialize state tree = some slices) :
    ∀ atom ∈ slices.flatMap characters, atom.address.1 = (active tree).start.1 := by
  cases normal with
  | own stop =>
    cases extracted : sliceAtoms state ⟨(bid,.start),stop⟩ with
    | none => simp [materialize,NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.preorderChildren,extracted] at materialized
    | some atoms =>
      have equal : slices = [⟨(bid,.start),atoms⟩] := by
        simpa [materialize,NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.preorderChildren,extracted] using materialized.symm
      subst slices
      intro atom member
      have inside : atom ∈ atoms := (List.mem_filter.mp (by simpa [characters] using member)).1
      exact (slice_storage state _ atoms extracted).2 atom inside
  | attached ref =>
    cases root : sliceAtoms state (NotionCoreSliceForest.titleRef bid) with
    | none => simp [materialize,NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.preorderChildren,root] at materialized
    | some roots =>
      have existsTitle : state.instances.any (fun entry => entry.1 == bid) = true := by
        simpa [NotionCoreSliceForest.titleRef] using (slice_storage state _ roots root).1
      have rootEmpty := NotionCoreMachineSlices.empty_title_atoms state bid existsTitle (empty rfl)
      have rootsEq : roots = [] := Option.some.inj (root.symm.trans rootEmpty)
      subst roots
      cases leaf : sliceAtoms state ref with
      | none => simp [materialize,NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.preorderChildren,root,leaf] at materialized
      | some atoms =>
        have equal : slices = [⟨(bid,.start),[]⟩,⟨ref.start,atoms⟩] := by
          simpa [materialize,NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.preorderChildren,root,leaf] using materialized.symm
        subst slices
        intro atom member
        have inside : atom ∈ atoms := (List.mem_filter.mp (by simpa [characters] using member)).1
        exact (slice_storage state ref atoms leaf).2 atom inside

private theorem visible_not_start (state : State) (atom : Atom)
    (present : atom ∈ physical state atom.address.1) (visible : visibleAtom atom = true) :
    atom.address.2 ≠ NotionCoreSpec.LocalId.start := by
  simp only [physical,NotionCorePhysicalReplay.physical,List.mem_cons,List.mem_map] at present
  rcases present with equal | ⟨item,member,equal⟩
  · have same := congrArg Atom.kind equal
    simp [NotionCorePhysicalReplay.start,NotionCorePartition.boundary,visibleAtom,same] at visible
  · rw [← equal]
    simp [NotionCorePhysicalReplay.atom,NotionCorePhysicalReplay.address,NotionCorePhysicalReplay.localId]

private theorem decode_block (address : Address) (key : BlockKey) (origin : NotionCoreOriginTree.Origin)
    (decoded : decodeAddress address = some (key,origin)) : decodeBlock address.1 = some key := by
  cases block : decodeBlock address.1 with
  | none => simp [decodeAddress,block] at decoded
  | some actual =>
    cases old : decodeOrigin address.2 with
    | none => simp [decodeAddress,block,old] at decoded
    | some value =>
      have same : actual = key := by simpa [decodeAddress,block,old] using congrArg (Option.map (fun pair => pair.1)) decoded
      exact congrArg some same

private theorem decoded_nonstart (address : Address) (key : BlockKey) (origin : NotionCoreOriginTree.Origin)
    (notStart : address.2 ≠ NotionCoreSpec.LocalId.start)
    (decoded : decodeAddress address = some (key,origin)) : ∃ id, origin = .item id := by
  cases origin with
  | item id => exact ⟨id,rfl⟩
  | start =>
    cases address with
    | mk inst addrId =>
      cases addrId with
      | start => contradiction
      | event event =>
        cases block : decodeBlock inst <;> simp [decodeAddress,decodeOrigin,block] at decoded

/-- Actual visible atoms decode to item IDs, never virtual START, using
accepted storage provenance rather than an assumed decoder-success guard. -/
theorem materialized_visible_decode (txs : List Transaction) (state : State)
    (accepted : replay {} txs = some state) (tree : NotionCoreSliceForest.Tree)
    (slices : List Slice) (materialized : materialize state tree = some slices)
    (atom : Atom) (member : atom ∈ slices.flatMap characters) :
    ∃ key id, decodeAddress atom.address = some (key,.item id) := by
  obtain ⟨slice,inside,visible⟩ := List.mem_flatMap.mp member
  obtain ⟨atomMember,isVisible⟩ := List.mem_filter.mp visible
  obtain ⟨⟨entry,stored,name⟩,same⟩ := materialized_storage state tree slices materialized slice inside
  have sameInst := same atom atomMember
  have instanceMember : atom.address.1 ∈ NotionCoreMachineCreators.instanceKeys state := by
    exact List.mem_map.mpr ⟨entry,stored,name.trans sameInst.symm⟩
  have rawMember : atom ∈ physical state atom.address.1 := by
    rw [sameInst]
    exact (materialized_physical state tree slices materialized slice inside).2 atom atomMember
  obtain ⟨key,origin,decoded⟩ := physical_decode_progress txs state accepted atom.address instanceMember
    (List.mem_map.mpr ⟨atom,rawMember,rfl⟩)
  obtain ⟨id,rfl⟩ := decoded_nonstart atom.address key origin (visible_not_start state atom rawMember isVisible) decoded
  exact ⟨key,id,decoded⟩

def visibleLength (state : State) (block : BlockKey) : Nat :=
  (((blockSlices state block).getD []).flatMap characters).length

private theorem target_mapM (inst : BlockKey) (addresses : List Address)
    (success : ∀ address ∈ addresses, ∃ id, decodeAddress address = some (inst,.item id)) :
    ∃ ids, decodeTargets inst addresses = some ids ∧ ids.length = addresses.length := by
  induction addresses with
  | nil => exact ⟨[],rfl,rfl⟩
  | cons first rest ih =>
    obtain ⟨id,decoded⟩ := success first (by simp)
    obtain ⟨ids,later,length⟩ := ih (fun address member => success address (List.mem_cons_of_mem _ member))
    refine ⟨id :: ids,?_,by simp [length]⟩
    have one : decodeTarget inst first = some id := by simp [decodeTarget,decoded]
    have laterMap : rest.mapM (decodeTarget inst) = some ids := later
    simp [decodeTargets,one,laterMap]

/-- A valid nonempty visible range prepares one source-codec sorted erase.
Normal shape supplies the single-instance validator, and replay provenance
supplies each internal item decoder. No selection success is assumed. -/
theorem selectErase_total (txs : List Transaction) (state : State)
    (accepted : replay {} txs = some state) (part : Partitioned state) (shape : ShapeInvariant state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (block : BlockKey) (stored : ∃ found ∈ state.forest, found.id = blockName block)
    (start stop : Nat) (nonempty : start < stop) (bounded : stop ≤ visibleLength state block) :
    ∃ inst ids, selectErase state block start stop = some (.erase block inst (NotionCoreRanges.sorted ids)) ∧
      ids ≠ [] := by
  cases found : state.forest.find? (fun entry => entry.id == blockName block) with
  | none =>
    obtain ⟨entry,member,equal⟩ := stored
    have absent := List.find?_eq_none.mp found entry member
    simp [equal] at absent
  | some entry =>
    have member := List.mem_of_find?_eq_some found
    obtain ⟨slices,materialized⟩ := materialize_total state part unique entry member
    have blockSlicesEq : blockSlices state block = some slices := by simp [blockSlices,found,materialized]
    have bounds : stop ≤ (slices.flatMap characters).length := by simpa [visibleLength,blockSlicesEq] using bounded
    let selected := ((slices.flatMap characters).drop start).take (stop-start)
    have length : selected.length = stop-start := by
      simp only [selected,List.length_take,List.length_drop]
      omega
    have positive : selected ≠ [] := by
      intro empty
      rw [empty] at length
      simp only [List.length_nil] at length
      omega
    obtain ⟨first,rest,selectedEq⟩ := List.exists_cons_of_ne_nil positive
    have firstMember : first ∈ slices.flatMap characters :=
      List.mem_of_mem_drop (List.mem_of_mem_take (selectedEq ▸ List.mem_cons_self))
    obtain ⟨inst,id,decodedFirst⟩ := materialized_visible_decode txs state accepted entry.title slices materialized first firstMember
    have titleEmpty : NotionCoreSliceForest.attached entry.title = true →
        physical state entry.id = NotionCoreSliceForest.emptyPhysical entry.id := by
      intro attached
      exact shape.2.2 _ (List.mem_map.mpr ⟨entry,member,rfl⟩) attached
    have instanceSame := normal_visible_instance state entry.id entry.title (shape.1 entry member) titleEmpty slices materialized
    have blockDecoded := decode_block first.address inst (.item id) decodedFirst
    have every : ∀ address ∈ selected.map Atom.address, ∃ item, decodeAddress address = some (inst,.item item) := by
      intro address present
      obtain ⟨atom,inSelection,rfl⟩ := List.mem_map.mp present
      have visible : atom ∈ slices.flatMap characters := List.mem_of_mem_drop (List.mem_of_mem_take inSelection)
      obtain ⟨actual,item,decoded⟩ := materialized_visible_decode txs state accepted entry.title slices materialized atom visible
      have sameInst : atom.address.1 = first.address.1 := (instanceSame atom visible).trans (instanceSame first firstMember).symm
      have actualBlock := decode_block atom.address actual (.item item) decoded
      rw [sameInst,blockDecoded] at actualBlock
      have actualEq : actual = inst := (Option.some.inj actualBlock).symm
      exact ⟨item,actualEq ▸ decoded⟩
    obtain ⟨ids,decoded,lengthIds⟩ := target_mapM inst (selected.map Atom.address) every
    have idsNonempty : ids ≠ [] := by
      intro empty
      rw [empty,List.length_nil,List.length_map,length] at lengthIds
      omega
    have selectedNonempty : (selected.map Atom.address).isEmpty = false := by
      simp [selectedEq]
    have addresses : deleteAddresses state block start stop = some (selected.map Atom.address) := by
      simp only [deleteAddresses,show start ≠ stop by omega,if_false,blockSlicesEq,Bind.bind,Option.bind]
      change (if (selected.map Atom.address).isEmpty then none else some (selected.map Atom.address)) = _
      rw [selectedNonempty]
      rfl
    refine ⟨inst,ids,?_,idsNonempty⟩
    have prepared : prepareErase state block inst start stop =
        some (.erase block inst (NotionCoreRanges.sorted ids)) := by
      simp [prepareErase,addresses,decoded,NotionCoreRanges.expand_compress]
    simp [selectErase,addresses,selectedEq,decodedFirst,prepared]

#print axioms materialize_total
#print axioms normal_visible_instance
#print axioms selectErase_total

/-- Honest reconstruction supplies shape, coverage, and physical uniqueness.
The remaining request premises are precisely an existing block and a valid
nonempty range of its displayed iterator atoms. -/
theorem honest_selectErase_total (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (state : State) (reconstructed : NotionCoreReconstruction.reconstruct network peer = some state)
    (block : BlockKey) (stored : ∃ found ∈ state.forest, found.id = blockName block)
    (start stop : Nat) (nonempty : start < stop) (bounded : stop ≤ visibleLength state block) :
    ∃ inst ids, selectErase state block start stop = some (.erase block inst (NotionCoreRanges.sorted ids)) ∧
      ids ≠ [] := by
  obtain ⟨checked,accepted,part,shape,_⟩ := NotionCoreMachineHonestReplay.honest_reconstruct network reachable peer
  have equal : checked = state := Option.some.inj (accepted.symm.trans reconstructed)
  subst checked
  have actual : replay {} (NotionCoreReconstruction.transactions network peer) = some state := reconstructed
  have unique := NotionCoreMachineMarkerProgress.canonical_physical_unique_all network
    (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))
    peer (NotionCoreReconstruction.transactions network peer) [] (by simp) state actual
  exact selectErase_total _ state actual part shape unique block stored start stop nonempty bounded

namespace SPOT
private def first : NotionRunAllocation.Id := ⟨1,[65]⟩
private def second : NotionRunAllocation.Id := ⟨2,[65]⟩
private def cut : Transaction := ⟨⟨3,[66]⟩,.split .initial .initial (.item first)⟩
/-- The inherited leaf displays b and deletes its original-instance ID. The
new block's unused title is not the text instance, and empty ranges emit none. -/
theorem inherited_delete_control :
    (replay {} [NotionCorePayload.bootstrap [97,98],cut] >>= fun state =>
      selectErase state (.issued cut.id) 0 1) = some (.erase (.issued cut.id) .initial [second]) ∧
    (replay {} [NotionCorePayload.bootstrap [97,98],cut] >>= fun state =>
      selectErase state (.issued cut.id) 0 1) ≠ some (.erase (.issued cut.id) (.issued cut.id) [second]) ∧
    (replay {} [NotionCorePayload.bootstrap [97,98],cut] >>= fun state =>
      selectErase state (.issued cut.id) 0 0) = none := by decide +kernel
end SPOT

#print axioms honest_selectErase_total

/-- Total preparation directly on the honestly reconstructed document, with
no successful reconstruction premise. The existing-block and range checks
refer to that document's actual client-visible atom sequence. -/
theorem honest_erase_request_total (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (block : BlockKey) (start stop : Nat)
    (stored : ∃ found ∈ ((NotionCoreReconstruction.reconstruct network peer).getD {}).forest,
      found.id = blockName block)
    (nonempty : start < stop)
    (bounded : stop ≤ visibleLength ((NotionCoreReconstruction.reconstruct network peer).getD {}) block) :
    ∃ state inst ids, NotionCoreReconstruction.reconstruct network peer = some state ∧
      selectErase state block start stop = some (.erase block inst (NotionCoreRanges.sorted ids)) ∧ ids ≠ [] := by
  obtain ⟨state,accepted,_,_,_⟩ := NotionCoreMachineHonestReplay.honest_reconstruct network reachable peer
  rw [accepted] at stored bounded
  obtain ⟨inst,ids,prepared,nonemptyIds⟩ := honest_selectErase_total network reachable peer state accepted
    block stored start stop nonempty bounded
  exact ⟨state,inst,ids,accepted,prepared,nonemptyIds⟩

#print axioms honest_erase_request_total
end Sal.MRDTs.Instances.NotionCoreMachineDeleteTotal
