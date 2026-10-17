import Sal.MRDTs.Instances.NotionCoreMachineDelete
import Sal.MRDTs.Instances.NotionCoreMachineClientShape
import Sal.MRDTs.Instances.NotionCoreMachineHonestReplay

/-! Total supported nonempty erase preparation on chains. Visible positions
count source iterator atoms across every slice of a block's chain, which may
lie in several text instances after merges; the selection is grouped by
instance. This concerns actual internal selection/codec validation; source
wire parsing and JavaScript extraction are separate boundaries. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineDeleteTotal
open NotionCoreMachine
open NotionCoreMachineClient
open NotionCoreMachineDelete
open NotionCoreMachineShape (ShapeInvariant)
open NotionCoreMachinePartition (Partitioned)
open NotionCorePayload (BlockKey Payload Transaction)
open NotionCoreSource (Atom Slice)
open NotionCoreSpec (Address)
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

/-- Every visible atom of a stored chain lies in the instance of a live node
of the forest: dead title roots have physically empty instances. -/
theorem visible_live_instance (state : State) (shape : ShapeInvariant state)
    (found : NotionCoreSliceForest.Block) (member : found ∈ state.forest)
    (slices : List Slice) (materialized : materialize state found.title = some slices) :
    ∀ atom ∈ slices.flatMap characters, ∃ live,
      (live,true) ∈ NotionCoreSliceForest.forestNodes state.forest ∧ live.start.1 = atom.address.1 := by
  intro atom visible
  obtain ⟨slice,inside,character⟩ := List.mem_flatMap.mp visible
  have atomMember := (List.mem_filter.mp character).1
  obtain ⟨ref,inTree,extracted⟩ := mapM_source _ _ _ materialized slice inside
  cases selected : sliceAtoms state ref with
  | none => simp [selected] at extracted
  | some atoms =>
    have sliceEq : slice = ⟨ref.start,atoms⟩ := by simpa [selected] using extracted.symm
    subst slice
    have sameInst := (slice_storage state ref atoms selected).2 atom atomMember
    have refMember : ref ∈ NotionCoreSliceForest.forestRefs state.forest :=
      List.mem_flatMap.mpr ⟨found,member,inTree⟩
    rw [← NotionCoreSliceForest.forestNodes_fst] at refMember
    obtain ⟨⟨node,live⟩,nodeMember,nodeEq⟩ := List.mem_map.mp refMember
    simp only at nodeEq
    subst node
    cases live with
    | true => exact ⟨ref,nodeMember,sameInst.symm⟩
    | false =>
      obtain ⟨titleEq,empty,_⟩ := shape.2.2 ref nodeMember
      have existsInstance := (slice_storage state ref atoms selected).1
      have emptyAtoms := NotionCoreMachineSlices.empty_title_atoms state ref.start.1
        (by simpa using existsInstance) empty
      rw [← titleEq] at emptyAtoms
      have : atoms = [] := Option.some.inj (selected.symm.trans emptyAtoms)
      subst atoms
      simp at atomMember

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

/-- A valid nonempty visible range prepares one source-codec sorted group per
run of one text instance. Replay provenance supplies each internal item
decoder; no selection success and no single-instance shape is assumed. -/
theorem selectErase_total (txs : List Transaction) (state : State)
    (accepted : replay {} txs = some state) (part : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (block : BlockKey) (stored : ∃ found ∈ state.forest, found.id = blockName block)
    (start stop : Nat) (nonempty : start < stop) (bounded : stop ≤ visibleLength state block) :
    ∃ groups, selectErase state block start stop = some (.erase block groups) ∧
      groups ≠ [] ∧ ∀ group ∈ groups, group.2 ≠ [] := by
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
    have selectedNonempty : (selected.map Atom.address).isEmpty = false := by
      obtain ⟨first,rest,selectedEq⟩ := List.exists_cons_of_ne_nil positive
      simp [selectedEq]
    have addresses : deleteAddresses state block start stop = some (selected.map Atom.address) := by
      simp only [deleteAddresses,show start ≠ stop by omega,if_false,blockSlicesEq,Bind.bind,Option.bind]
      change (if (selected.map Atom.address).isEmpty then none else some (selected.map Atom.address)) = _
      rw [selectedNonempty]
      rfl
    have decodes : ∀ address ∈ selected.map Atom.address, ∃ inst id,
        decodeAddress address = some (inst,.item id) := by
      intro address present
      obtain ⟨atom,inSelection,rfl⟩ := List.mem_map.mp present
      exact materialized_visible_decode txs state accepted entry.title slices materialized atom
        (List.mem_of_mem_drop (List.mem_of_mem_take inSelection))
    have groupsSome : ∀ run ∈ runs (selected.map Atom.address), ∃ group,
        prepareGroup run = some group ∧ group.2 ≠ [] := by
      intro run runMember
      obtain ⟨first,rest,runEq⟩ := List.exists_cons_of_ne_nil (runs_nonempty _ run runMember)
      have inRun : ∀ address ∈ run.2, address ∈ selected.map Atom.address := by
        intro address inside
        rw [← runs_flatten (selected.map Atom.address)]
        exact List.mem_flatMap.mpr ⟨run,runMember,inside⟩
      obtain ⟨inst,firstId,firstDecoded⟩ := decodes first (inRun first (by simp [runEq]))
      have firstKey : first.1 = run.1 := runs_key _ run runMember first (by simp [runEq])
      have runBlock : decodeBlock run.1 = some inst := by
        rw [← firstKey]; exact decode_block first inst (.item firstId) firstDecoded
      have every : ∀ address ∈ run.2, ∃ item, decodeAddress address = some (inst,.item item) := by
        intro address inside
        obtain ⟨actual,item,decoded⟩ := decodes address (inRun address inside)
        have actualBlock := decode_block address actual (.item item) decoded
        rw [runs_key _ run runMember address inside,runBlock] at actualBlock
        have actualEq : actual = inst := (Option.some.inj actualBlock).symm
        exact ⟨item,actualEq ▸ decoded⟩
      obtain ⟨ids,decoded,lengthIds⟩ := target_mapM inst run.2 every
      refine ⟨(inst,NotionCoreRanges.sorted ids),?_,?_⟩
      · simp [prepareGroup,runBlock,decoded,NotionCoreRanges.expand_compress]
      · intro empty
        have lengths := (NotionCoreRanges.sorted_perm ids).length_eq
        simp only at empty
        rw [empty,List.length_nil,lengthIds,runEq] at lengths
        simp at lengths
    obtain ⟨groups,grouped⟩ := mapM_success prepareGroup (runs (selected.map Atom.address))
      (fun run member => by
        obtain ⟨group,prepared,_⟩ := groupsSome run member
        exact ⟨group,prepared⟩)
    refine ⟨groups,?_,?_,?_⟩
    · simp [selectErase,addresses,grouped]
    · intro empty
      subst groups
      have runsEmpty : runs (selected.map Atom.address) = [] := by
        cases h : runs (selected.map Atom.address) with
        | nil => rfl
        | cons run rest =>
          rw [h,List.mapM_cons] at grouped
          cases hp : prepareGroup run <;> cases hr : List.mapM prepareGroup rest <;>
            simp [hp, hr] at grouped
      have flat := runs_flatten (selected.map Atom.address)
      rw [runsEmpty] at flat
      simp only [List.flatMap_nil] at flat
      have : selected = [] := by simpa using flat.symm
      exact positive this
    · intro group member
      obtain ⟨run,runMember,prepared⟩ := mapM_source _ _ _ grouped group member
      obtain ⟨other,otherPrepared,nonemptyGroup⟩ := groupsSome run runMember
      rw [prepared] at otherPrepared
      cases otherPrepared
      exact nonemptyGroup

#print axioms materialize_total
#print axioms visible_live_instance
#print axioms selectErase_total

/-- Honest reconstruction supplies coverage and physical uniqueness. The
remaining request premises are precisely an existing block and a valid
nonempty range of its displayed iterator atoms. -/
theorem honest_selectErase_total (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (state : State) (reconstructed : NotionCoreReconstruction.reconstruct network peer = some state)
    (block : BlockKey) (stored : ∃ found ∈ state.forest, found.id = blockName block)
    (start stop : Nat) (nonempty : start < stop) (bounded : stop ≤ visibleLength state block) :
    ∃ groups, selectErase state block start stop = some (.erase block groups) ∧
      groups ≠ [] ∧ ∀ group ∈ groups, group.2 ≠ [] := by
  obtain ⟨checked,accepted,part,_,_⟩ := NotionCoreMachineHonestReplay.honest_reconstruct network reachable peer
  have equal : checked = state := Option.some.inj (accepted.symm.trans reconstructed)
  subst checked
  have actual : replay {} (NotionCoreReconstruction.transactions network peer) = some state := reconstructed
  have unique := NotionCoreMachineMarkerProgress.canonical_physical_unique_all network
    (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))
    peer (NotionCoreReconstruction.transactions network peer) [] (by simp) state actual
  exact selectErase_total _ state actual part unique block stored start stop nonempty bounded

namespace SPOT
private def first : NotionRunAllocation.Id := ⟨1,[65]⟩
private def second : NotionRunAllocation.Id := ⟨2,[65]⟩
private def cut : Transaction := ⟨⟨3,[66]⟩,.split .initial .initial (.item first)⟩
/-- The inherited leaf displays b and deletes its original-instance ID. The
new block's empty dead title is not the text instance, and empty ranges emit none. -/
theorem inherited_delete_control :
    (replay {} [NotionCorePayload.bootstrap [97,98],cut] >>= fun state =>
      selectErase state (.issued cut.id) 0 1) = some (.erase (.issued cut.id) [(.initial,[second])]) ∧
    (replay {} [NotionCorePayload.bootstrap [97,98],cut] >>= fun state =>
      selectErase state (.issued cut.id) 0 1) ≠ some (.erase (.issued cut.id) [(.issued cut.id,[second])]) ∧
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
    ∃ state groups, NotionCoreReconstruction.reconstruct network peer = some state ∧
      selectErase state block start stop = some (.erase block groups) ∧
      groups ≠ [] ∧ ∀ group ∈ groups, group.2 ≠ [] := by
  obtain ⟨state,accepted,_,_,_⟩ := NotionCoreMachineHonestReplay.honest_reconstruct network reachable peer
  rw [accepted] at stored bounded
  obtain ⟨groups,prepared,nonemptyGroups,nonemptyTargets⟩ := honest_selectErase_total network reachable peer
    state accepted block stored start stop nonempty bounded
  exact ⟨state,groups,accepted,prepared,nonemptyGroups,nonemptyTargets⟩

#print axioms honest_erase_request_total
end Sal.MRDTs.Instances.NotionCoreMachineDeleteTotal
