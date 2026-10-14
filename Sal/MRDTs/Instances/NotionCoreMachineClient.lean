import Sal.MRDTs.Instances.NotionCoreMachineSlices
import Sal.MRDTs.Instances.NotionCorePreparation
import Sal.MRDTs.Instances.NotionCoreMachineCreators
import Sal.MRDTs.Instances.NotionCoreMachineBirths

/-! Client selection from the actual combined interpreter's slice forest.
Indices here are nonnegative character indices, not UTF-16 string offsets.
Delete selection follows nonnegative JS slice clamping; message range encoding
and grouping multiple text instances are separate from selection. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineClient
open NotionCoreSpec (Address LocalId)
open NotionCoreSource (Atom Slice)
open NotionCorePayload (BlockKey Payload)
open NotionCoreMachine
open NotionCorePreparation (characters zeroOrigin)

/-- Extract every actual stored slice in tree preorder, retaining tombstones
for endpoint selection and filtering them only when selecting characters. -/
def materialize (state : State) (tree : NotionCoreSliceForest.Tree) : Option (List Slice) :=
  (NotionCoreSliceForest.preorderTree tree).mapM fun ref => do
    pure ⟨ref.start, ← sliceAtoms state ref⟩

def blockSlices (state : State) (block : BlockKey) : Option (List Slice) := do
  let found ← state.forest.find? (fun entry => entry.id == blockName block)
  materialize state found.title

def locateSlices (slices : List Slice) (index : Nat) : Option Address :=
  let visible := slices.flatMap characters
  if index ≤ visible.length then
    match index with
    | 0 => zeroOrigin slices
    | n + 1 => visible[n]?.map Atom.address
  else none

def locateAddress (state : State) (block : BlockKey) (index : Nat) : Option Address := do
  locateSlices (← blockSlices state block) index

/-- Decode only the internal injective semantic names used by this Lean
interpreter. This is not the demo's string/name wire decoder. -/
def decodeBlock : Nat → Option BlockKey
  | 0 => some .initial
  | n + 1 => (Encodable.decode (α := Nat × List Nat) n).map fun id => .issued ⟨id.1,id.2⟩
def decodeOrigin : LocalId → Option NotionCoreOriginTree.Origin
  | .start => some .start
  | .event id => (Encodable.decode (α := List Nat) id.1).map fun session => .item ⟨id.2,session⟩
def decodeAddress (address : Address) : Option (BlockKey × NotionCoreOriginTree.Origin) := do
  pure (← decodeBlock address.1, ← decodeOrigin address.2)

@[simp] theorem decode_blockName (block : BlockKey) : decodeBlock (blockName block) = some block := by
  cases block with
  | initial => rfl
  | issued id => cases id; simp [blockName, Nat.add_comm, decodeBlock]

@[simp] theorem decode_originAddress (block : BlockKey) (origin : NotionCoreOriginTree.Origin) :
    decodeAddress (NotionCorePhysicalReplay.originAddress (blockName block) origin) =
      some (block, origin) := by
  cases origin <;> simp [decodeAddress, decodeOrigin, NotionCorePhysicalReplay.originAddress,
    NotionCorePhysicalReplay.address, NotionCorePhysicalReplay.localId]

def prepareInsert (state : State) (block : BlockKey) (index : Nat) (atoms : List Nat) : Option Payload := do
  if atoms.isEmpty then none else do
    let (inst, origin) ← decodeAddress (← locateAddress state block index)
    pure (.insert block inst origin atoms)

def prepareSplit (state : State) (block : BlockKey) (index : Nat) : Option Payload := do
  let (inst, origin) ← decodeAddress (← locateAddress state block index)
  pure (.split block inst origin)

def prepareCreate (state : State) (after : Option BlockKey) : Option Payload :=
  match after with
  | none => some (.create none)
  | some block => if state.forest.any (fun entry => entry.id == blockName block) then
      some (.create after) else none

/-- Visible deletion targets before per-instance grouping and ID-range
compression. Empty ranges are skipped before block lookup, as in the source. -/
def deleteAddresses (state : State) (block : BlockKey) (start stop : Nat) : Option (List Address) := do
  if start = stop then none else do
    let slices ← blockSlices state block
    let targets := ((slices.flatMap characters).drop start |>.take (stop - start)).map Atom.address
    if targets.isEmpty then none else some targets

theorem locate_normal (block : NotionCoreSource.Block) (index : Nat) :
    locateSlices (NotionCorePreparation.nodes block) index = NotionCorePreparation.locate block index := rfl

theorem materialize_leaf (state : State) (before after : List NotionCorePartition.Cell)
    (cell : NotionCorePartition.Cell)
    (existsInstance : state.instances.any (fun entry => entry.1 == cell.slice.start.1) = true)
    (physicalEq : physical state cell.slice.start.1 = NotionCorePartition.flatten (before ++ cell :: after))
    (unique : ((physical state cell.slice.start.1).map Atom.address).Nodup) :
    materialize state (.node ⟨cell.slice.start, after.head?.map (fun next => next.slice.start)⟩ .nil) =
      some [cell.slice] := by
  have extracted := NotionCoreMachineSlices.sliceAtoms_cell state before after cell existsInstance physicalEq unique
  simp [materialize, NotionCoreSliceForest.preorderTree, NotionCoreSliceForest.preorderChildren, extracted]

theorem materialize_attached (state : State) (bid : Nat)
    (before after : List NotionCorePartition.Cell) (cell : NotionCorePartition.Cell)
    (titleExists : state.instances.any (fun entry => entry.1 == bid) = true)
    (titleEmpty : physical state bid = [NotionCorePartition.boundary (bid,.start)])
    (activeExists : state.instances.any (fun entry => entry.1 == cell.slice.start.1) = true)
    (physicalEq : physical state cell.slice.start.1 = NotionCorePartition.flatten (before ++ cell :: after))
    (unique : ((physical state cell.slice.start.1).map Atom.address).Nodup) :
    materialize state (.node (NotionCoreSliceForest.titleRef bid)
      (.cons (.node ⟨cell.slice.start, after.head?.map (fun next => next.slice.start)⟩ .nil) .nil)) =
      some [⟨(bid,.start),[]⟩,cell.slice] := by
  have root := NotionCoreMachineSlices.empty_title_atoms state bid titleExists titleEmpty
  simp only [NotionCoreSliceForest.titleRef] at root
  have leaf := NotionCoreMachineSlices.sliceAtoms_cell state before after cell activeExists physicalEq unique
  simp [materialize, NotionCoreSliceForest.preorderTree, NotionCoreSliceForest.preorderChildren, root, leaf,
    NotionCoreSliceForest.titleRef]

theorem find_block_member (forest : NotionCoreSliceForest.Forest)
    (unique : (forest.map (·.id)).Nodup) (block : NotionCoreSliceForest.Block)
    (member : block ∈ forest) :
    forest.find? (fun entry => entry.id == block.id) = some block := by
  induction forest with
  | nil => simp at member
  | cons head rest ih =>
      have nd := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with rfl | member
      · simp
      · have different : head.id ≠ block.id := by
          intro same
          exact nd.1 (List.mem_map.mpr ⟨block, member, same.symm⟩)
        simpa [different] using ih nd.2 member

/-- A positive index selects a visible atom; zero selects an existing stored
start boundary. Neither case can invent an address outside the extracted tree. -/
theorem zero_member (slices : List Slice) (origin : Address)
    (selected : zeroOrigin slices = some origin) :
    ∃ slice ∈ slices, origin = slice.start := by
  induction slices with
  | nil => simp [zeroOrigin] at selected
  | cons slice rest ih =>
      cases rest with
      | nil => simpa [zeroOrigin] using selected.symm
      | cons next rest =>
          by_cases empty : (characters slice).isEmpty = true
          · have tail : zeroOrigin (next :: rest) = some origin := by
              simpa [zeroOrigin, empty] using selected
            obtain ⟨found, member, same⟩ := ih tail
            exact ⟨found, List.mem_cons_of_mem _ member, same⟩
          · have same : slice.start = origin := by simpa [zeroOrigin, empty] using selected
            exact ⟨slice, by simp, same.symm⟩

theorem locate_member (slices : List Slice) (index : Nat) (origin : Address)
    (selected : locateSlices slices index = some origin) :
    ∃ slice ∈ slices, origin = slice.start ∨ origin ∈ slice.atoms.map Atom.address := by
  simp only [locateSlices] at selected
  by_cases bound : index ≤ (slices.flatMap characters).length
  · rw [if_pos bound] at selected
    cases index with
    | zero =>
        obtain ⟨slice, member, same⟩ := zero_member slices origin selected
        exact ⟨slice, member, Or.inl same⟩
    | succ n =>
        obtain ⟨atom, found, equal⟩ := Option.map_eq_some_iff.mp selected
        have member := List.mem_of_getElem? found
        obtain ⟨slice, inside, visible⟩ := List.mem_flatMap.mp member
        exact ⟨slice, inside, Or.inr (List.mem_map.mpr
          ⟨atom, (List.mem_filter.mp visible).1, equal⟩)⟩
  · rw [if_neg bound] at selected
    contradiction

private theorem extract_member (physical : List Atom) (start : Address) (stop : Option Address)
    (atom : Atom) (member : atom ∈ NotionCorePartition.extract physical start stop) :
    atom ∈ physical := by
  obtain ⟨address, _, found⟩ := List.mem_filterMap.mp member
  cases address with
  | none => simp at found
  | some id => exact List.mem_of_find?_eq_some found

theorem slice_storage (state : State) (ref : NotionCoreSliceForest.Ref) (atoms : List Atom)
    (extracted : sliceAtoms state ref = some atoms) :
    (∃ entry ∈ state.instances, entry.1 = ref.start.1) ∧
      ∀ atom ∈ atoms, atom.address.1 = ref.start.1 := by
  have existsInstance : state.instances.any (fun entry => entry.1 == ref.start.1) = true := by
    by_contra absent
    have no := Bool.eq_false_iff.mpr absent
    simp [sliceAtoms, no] at extracted
  refine ⟨by simpa using existsInstance, ?_⟩
  have same : atoms = NotionCorePartition.extract (physical state ref.start.1) ref.start ref.stop := by
    cases stopEq : ref.stop <;> simp [sliceAtoms, stopEq, existsInstance] at extracted
    all_goals simp_all
  intro atom member
  have present := extract_member (physical state ref.start.1) ref.start ref.stop atom (same ▸ member)
  simp only [physical, NotionCorePhysicalReplay.physical, List.mem_cons, List.mem_map] at present
  rcases present with rfl | ⟨item, _, rfl⟩ <;> rfl

/-- Successful extraction retains a physically stored start and only physical atoms. -/
theorem slice_physical (state : State) (ref : NotionCoreSliceForest.Ref) (atoms : List Atom)
    (extracted : sliceAtoms state ref = some atoms) :
    ref.start ∈ (physical state ref.start.1).map Atom.address ∧
      ∀ atom ∈ atoms, atom ∈ physical state ref.start.1 := by
  have existsInstance : state.instances.any (fun entry => entry.1 == ref.start.1) = true := by
    simpa using (slice_storage state ref atoms extracted).1
  have startMember : ref.start ∈ (physical state ref.start.1).map Atom.address := by
    cases stopEq : ref.stop <;> simp [sliceAtoms, stopEq, existsInstance] at extracted
    all_goals simp_all
  have same : atoms = NotionCorePartition.extract (physical state ref.start.1) ref.start ref.stop := by
    cases stopEq : ref.stop <;> simp [sliceAtoms, stopEq, existsInstance] at extracted
    all_goals simp_all
  exact ⟨startMember, fun atom member => extract_member _ _ _ atom (same ▸ member)⟩

private theorem mapM_member {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (mapped : xs.mapM f = some ys) (y : β) (member : y ∈ ys) :
    ∃ x ∈ xs, f x = some y := by
  induction xs generalizing ys with
  | nil => simp at mapped; subst ys; simp at member
  | cons x rest ih =>
      cases head : f x with
      | none => simp [head] at mapped
      | some value =>
          cases tail : rest.mapM f with
          | none => simp [head, tail] at mapped
          | some values =>
              have same : value :: values = ys := by simpa [head, tail] using mapped
              subst ys
              rcases List.mem_cons.mp member with rfl | member
              · exact ⟨x, by simp, head⟩
              · obtain ⟨old, inside, found⟩ := ih values tail member
                exact ⟨old, List.mem_cons_of_mem _ inside, found⟩

theorem materialized_storage (state : State) (tree : NotionCoreSliceForest.Tree) (slices : List Slice)
    (materialized : materialize state tree = some slices) (slice : Slice) (member : slice ∈ slices) :
    (∃ entry ∈ state.instances, entry.1 = slice.start.1) ∧
      ∀ atom ∈ slice.atoms, atom.address.1 = slice.start.1 := by
  obtain ⟨ref, _, extracted⟩ := mapM_member _ _ _ materialized slice member
  cases selected : sliceAtoms state ref with
  | none => simp [selected] at extracted
  | some atoms =>
      have same : (⟨ref.start, atoms⟩ : Slice) = slice := by simpa [selected] using extracted
      subst slice
      exact slice_storage state ref atoms selected

theorem materialized_physical (state : State) (tree : NotionCoreSliceForest.Tree) (slices : List Slice)
    (materialized : materialize state tree = some slices) (slice : Slice) (member : slice ∈ slices) :
    slice.start ∈ (physical state slice.start.1).map Atom.address ∧
      ∀ atom ∈ slice.atoms, atom ∈ physical state slice.start.1 := by
  obtain ⟨ref, _, extracted⟩ := mapM_member _ _ _ materialized slice member
  cases selected : sliceAtoms state ref with
  | none => simp [selected] at extracted
  | some atoms =>
      have same : (⟨ref.start, atoms⟩ : Slice) = slice := by simpa [selected] using extracted
      subst slice
      exact slice_physical state ref atoms selected

theorem locate_physical (state : State) (block : BlockKey) (index : Nat) (address : Address)
    (selected : locateAddress state block index = some address) :
    address ∈ (physical state address.1).map Atom.address := by
  cases found : state.forest.find? (fun entry => entry.id == blockName block) with
  | none => simp [locateAddress, blockSlices, found] at selected
  | some tree =>
      cases extracted : materialize state tree.title with
      | none => simp [locateAddress, blockSlices, found, extracted] at selected
      | some slices =>
          have location : locateSlices slices index = some address := by
            simpa [locateAddress, blockSlices, found, extracted] using selected
          obtain ⟨slice, member, placement⟩ := locate_member slices index address location
          have stored := materialized_physical state tree.title slices extracted slice member
          rcases placement with rfl | member
          · exact stored.1
          · obtain ⟨atom, member, same⟩ := List.mem_map.mp member
            have frame := (materialized_storage state tree.title slices extracted slice
              (by assumption)).2 atom member
            have name : address.1 = slice.start.1 := (congrArg Prod.fst same).symm.trans frame
            rw [name]
            exact List.mem_map.mpr ⟨atom, stored.2 atom member, same⟩

/-- Successful actual location witnesses both the requested block and the
selected instance in interpreter storage; creator provenance can then be
derived from execution rather than supplied as a client guard. -/
theorem locate_storage (state : State) (block : BlockKey) (index : Nat) (origin : Address)
    (selected : locateAddress state block index = some origin) :
    (∃ found ∈ state.forest, found.id = blockName block) ∧
      ∃ entry ∈ state.instances, entry.1 = origin.1 := by
  cases found : state.forest.find? (fun entry => entry.id == blockName block) with
  | none => simp [locateAddress, blockSlices, found] at selected
  | some tree =>
      refine ⟨⟨tree, List.mem_of_find?_eq_some found, by simpa using List.find?_some found⟩, ?_⟩
      cases extracted : materialize state tree.title with
      | none => simp [locateAddress, blockSlices, found, extracted] at selected
      | some slices =>
          have location : locateSlices slices index = some origin := by
            simpa [locateAddress, blockSlices, found, extracted] using selected
          obtain ⟨slice, member, placement⟩ := locate_member slices index origin location
          obtain ⟨⟨entry, stored, name⟩, atoms⟩ := materialized_storage state tree.title slices extracted slice member
          refine ⟨entry, stored, ?_⟩
          rcases placement with rfl | member
          · exact name
          · obtain ⟨atom, member, same⟩ := List.mem_map.mp member
            exact name.trans ((atoms atom member).symm.trans (congrArg Prod.fst same))

/-- Canonical internal decoding succeeds for every physically selected item
or boundary of an instance actually stored by accepted replay. -/
theorem physical_decode_progress (txs : List NotionCorePayload.Transaction) (state : State)
    (accepted : replay {} txs = some state) (address : Address)
    (instanceMember : address.1 ∈ NotionCoreMachineCreators.instanceKeys state)
    (member : address ∈ (physical state address.1).map Atom.address) :
    ∃ inst origin, decodeAddress address = some (inst,origin) := by
  obtain ⟨_, _, key, _, name⟩ := NotionCoreMachineCreators.replay_instance_used
    txs state accepted address.1 instanceMember
  simp only [physical, NotionCorePhysicalReplay.physical, List.map_cons, List.mem_cons,
    List.mem_map] at member
  rcases member with start | ⟨atom, ⟨item, _, same⟩, addressEq⟩
  · refine ⟨key, .start, ?_⟩
    have equal : NotionCorePhysicalReplay.originAddress (blockName key) .start = address := by
      simpa [NotionCorePhysicalReplay.originAddress, name] using start.symm
    rw [← equal]
    exact decode_originAddress key .start
  · subst atom
    refine ⟨key, .item item.id, ?_⟩
    have equal : NotionCorePhysicalReplay.originAddress (blockName key) (.item item.id) = address := by
      simpa [NotionCorePhysicalReplay.originAddress, name] using addressEq
    rw [← equal]
    exact decode_originAddress key (.item item.id)

theorem located_decode_progress (txs : List NotionCorePayload.Transaction) (state : State)
    (accepted : replay {} txs = some state) (block : BlockKey) (index : Nat) (address : Address)
    (located : locateAddress state block index = some address) :
    ∃ inst origin, decodeAddress address = some (inst,origin) := by
  obtain ⟨_, entry, stored, name⟩ := locate_storage state block index address located
  exact physical_decode_progress txs state accepted address
    (List.mem_map.mpr ⟨entry, stored, name⟩) (locate_physical state block index address located)

/-- An actual physical non-START address decodes to an item born in a received
transaction in precisely the selected instance. No network reachability or
client item-knowledge guard is needed for this storage provenance statement. -/
theorem physical_decoded_known (network : NotionCorePayloadNetwork.State)
    (session : NotionRunAllocation.Session) (txs : List NotionCorePayload.Transaction) (state : State)
    (received : ∀ tx ∈ txs, ∃ entry ∈ network.entries, entry.tx = tx ∧
      NotionCorePayload.reservation tx ∈ (network.allocation.peers session).received)
    (accepted : replay {} txs = some state) (address : Address)
    (member : address ∈ (physical state address.1).map Atom.address)
    (inst : BlockKey) (id : NotionRunAllocation.Id)
    (decoded : decodeAddress address = some (inst,.item id)) :
    NotionCorePayloadNetwork.Known network session (inst,id) := by
  simp only [physical, NotionCorePhysicalReplay.physical, List.map_cons, List.mem_cons,
    List.mem_map] at member
  rcases member with start | ⟨atom, ⟨item, present, same⟩, addressEq⟩
  · have startId : address.2 = .start := congrArg Prod.snd start
    simp [decodeAddress, startId, decodeOrigin] at decoded
    cases blockDecoded : decodeBlock address.1 <;> simp [blockDecoded] at decoded
  · subst atom
    obtain ⟨row, rowMember, itemEq⟩ := NotionCoreMachineBirths.traversal_row_member
      _ _ _ item present
    obtain ⟨tx, txMember, key, keyName, born⟩ := NotionCoreMachineBirths.replay_row_birth
      txs state accepted address.1 row rowMember
    have encoded : NotionCorePhysicalReplay.originAddress (blockName key) (.item item.id) = address := by
      simpa [NotionCorePhysicalReplay.originAddress, keyName] using addressEq
    have decodeSame := decode_originAddress key (.item item.id)
    rw [encoded, decoded] at decodeSame
    have pairEq : (inst, NotionCoreOriginTree.Origin.item id) = (key, .item item.id) :=
      Option.some.inj decodeSame
    have instEq : inst = key := congrArg Prod.fst pairEq
    have idEq : id = item.id := NotionCoreOriginTree.Origin.item.inj (congrArg Prod.snd pairEq)
    obtain ⟨entry, entryMember, txEq, receipt⟩ := received tx txMember
    refine ⟨entry, entryMember, txEq ▸ receipt, ?_⟩
    simpa only [txEq, instEq, idEq, itemEq] using born

theorem located_item_known (network : NotionCorePayloadNetwork.State)
    (session : NotionRunAllocation.Session) (txs : List NotionCorePayload.Transaction) (state : State)
    (received : ∀ tx ∈ txs, ∃ entry ∈ network.entries, entry.tx = tx ∧
      NotionCorePayload.reservation tx ∈ (network.allocation.peers session).received)
    (accepted : replay {} txs = some state) (block : BlockKey) (index : Nat) (address : Address)
    (located : locateAddress state block index = some address)
    (inst : BlockKey) (id : NotionRunAllocation.Id)
    (decoded : decodeAddress address = some (inst,.item id)) :
    NotionCorePayloadNetwork.Known network session (inst,id) :=
  physical_decoded_known network session txs state received accepted address
    (locate_physical state block index address located) inst id decoded

/-- Metadata admission for the requested block and the selected text instance
is derived from actual client selection and received replay provenance. The
accepted replay is the client's current reconstructed document, not a premise
that its new edit or a future merged replay succeeds. -/
theorem located_creators (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network)
    (session : NotionRunAllocation.Session) (txs : List NotionCorePayload.Transaction) (state : State)
    (received : ∀ tx ∈ txs, ∃ entry ∈ network.entries, entry.tx = tx ∧
      NotionCorePayload.reservation tx ∈ (network.allocation.peers session).received)
    (accepted : replay {} txs = some state) (block : BlockKey) (index : Nat) (address : Address)
    (located : locateAddress state block index = some address)
    (inst : BlockKey) (origin : NotionCoreOriginTree.Origin)
    (decoded : decodeAddress address = some (inst,origin)) :
    NotionCoreCreatorNetwork.KnownCreator network session block ∧
      NotionCoreCreatorNetwork.KnownCreator network session inst := by
  obtain ⟨⟨found, member, name⟩, ⟨entry, stored, instName⟩⟩ := locate_storage state block index address located
  obtain ⟨key, keyName, known⟩ := NotionCoreMachineCreators.replay_known_creator
    network session txs state received accepted found member
  have same : block = key := blockName_injective (name.symm.trans keyName)
  refine ⟨same ▸ known, ?_⟩
  obtain ⟨key, encoded, known⟩ := NotionCoreMachineCreators.replay_known_instance_creator
    network reachable session txs state received accepted address.1
      (List.mem_map.mpr ⟨entry, stored, instName⟩)
  have blockDecoded : decodeBlock address.1 = some key := by rw [← encoded]; exact decode_blockName key
  have same : key = inst := by
    cases selected : decodeOrigin address.2 with
    | none => simp [decodeAddress, blockDecoded, selected] at decoded
    | some old =>
        have equal : (key,old) = (inst,origin) := by simpa [decodeAddress, blockDecoded, selected] using decoded
        exact congrArg Prod.fst equal
  exact same ▸ known

theorem prepared_split_creators (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network)
    (session : NotionRunAllocation.Session) (txs : List NotionCorePayload.Transaction) (state : State)
    (received : ∀ tx ∈ txs, ∃ entry ∈ network.entries, entry.tx = tx ∧
      NotionCorePayload.reservation tx ∈ (network.allocation.peers session).received)
    (accepted : replay {} txs = some state) (block : BlockKey) (index : Nat) (payload : Payload)
    (prepared : prepareSplit state block index = some payload) :
    ∀ key ∈ NotionCoreCreatorNetwork.requiredBlocks payload,
      NotionCoreCreatorNetwork.KnownCreator network session key := by
  cases selected : locateAddress state block index with
  | none => simp [prepareSplit, selected] at prepared
  | some address =>
      cases decoded : decodeAddress address with
      | none => simp [prepareSplit, selected, decoded] at prepared
      | some location =>
          obtain ⟨inst,origin⟩ := location
          have same : Payload.split block inst origin = payload := by
            simpa [prepareSplit, selected, decoded] using prepared
          subst payload
          have known := located_creators network reachable session txs state received accepted
            block index address selected inst origin decoded
          simpa [NotionCoreCreatorNetwork.requiredBlocks] using known

theorem prepared_insert_creators (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network)
    (session : NotionRunAllocation.Session) (txs : List NotionCorePayload.Transaction) (state : State)
    (received : ∀ tx ∈ txs, ∃ entry ∈ network.entries, entry.tx = tx ∧
      NotionCorePayload.reservation tx ∈ (network.allocation.peers session).received)
    (accepted : replay {} txs = some state) (block : BlockKey) (index : Nat) (atoms : List Nat) (payload : Payload)
    (prepared : prepareInsert state block index atoms = some payload) :
    ∀ key ∈ NotionCoreCreatorNetwork.requiredBlocks payload,
      NotionCoreCreatorNetwork.KnownCreator network session key := by
  cases empty : atoms.isEmpty with
  | true => simp [prepareInsert, empty] at prepared
  | false =>
      cases selected : locateAddress state block index with
      | none => simp [prepareInsert, empty, selected] at prepared
      | some address =>
          cases decoded : decodeAddress address with
          | none => simp [prepareInsert, empty, selected, decoded] at prepared
          | some location =>
              obtain ⟨inst,origin⟩ := location
              have same : Payload.insert block inst origin atoms = payload := by
                simpa [prepareInsert, empty, selected, decoded] using prepared
              subst payload
              have known := located_creators network reachable session txs state received accepted
                block index address selected inst origin decoded
              simpa [NotionCoreCreatorNetwork.requiredBlocks] using known

/-- Actual split preparation supplies every located item-reference guard. -/
theorem prepared_split_references (network : NotionCorePayloadNetwork.State)
    (session : NotionRunAllocation.Session) (txs : List NotionCorePayload.Transaction) (state : State)
    (received : ∀ tx ∈ txs, ∃ entry ∈ network.entries, entry.tx = tx ∧
      NotionCorePayload.reservation tx ∈ (network.allocation.peers session).received)
    (accepted : replay {} txs = some state) (block : BlockKey) (index : Nat) (payload : Payload)
    (prepared : prepareSplit state block index = some payload) :
    ∀ address ∈ NotionCorePayloadNetwork.locatedReferences payload,
      NotionCorePayloadNetwork.Known network session address := by
  cases selected : locateAddress state block index with
  | none => simp [prepareSplit, selected] at prepared
  | some address =>
      cases decoded : decodeAddress address with
      | none => simp [prepareSplit, selected, decoded] at prepared
      | some location =>
          obtain ⟨inst,origin⟩ := location
          have same : Payload.split block inst origin = payload := by
            simpa [prepareSplit, selected, decoded] using prepared
          subst payload
          cases origin with
          | start => simp [NotionCorePayloadNetwork.locatedReferences, NotionCorePayload.originReference]
          | item id =>
              have known := located_item_known network session txs state received accepted
                block index address selected inst id decoded
              simpa [NotionCorePayloadNetwork.locatedReferences, NotionCorePayload.originReference] using known

/-- Actual insert preparation supplies every located item-reference guard. -/
theorem prepared_insert_references (network : NotionCorePayloadNetwork.State)
    (session : NotionRunAllocation.Session) (txs : List NotionCorePayload.Transaction) (state : State)
    (received : ∀ tx ∈ txs, ∃ entry ∈ network.entries, entry.tx = tx ∧
      NotionCorePayload.reservation tx ∈ (network.allocation.peers session).received)
    (accepted : replay {} txs = some state) (block : BlockKey) (index : Nat) (atoms : List Nat) (payload : Payload)
    (prepared : prepareInsert state block index atoms = some payload) :
    ∀ address ∈ NotionCorePayloadNetwork.locatedReferences payload,
      NotionCorePayloadNetwork.Known network session address := by
  cases empty : atoms.isEmpty with
  | true => simp [prepareInsert, empty] at prepared
  | false =>
      cases selected : locateAddress state block index with
      | none => simp [prepareInsert, selected, empty] at prepared
      | some address =>
          cases decoded : decodeAddress address with
          | none => simp [prepareInsert, selected, decoded, empty] at prepared
          | some location =>
              obtain ⟨inst,origin⟩ := location
              have same : Payload.insert block inst origin atoms = payload := by
                simpa [prepareInsert, selected, decoded, empty] using prepared
              subst payload
              cases origin with
              | start => simp [NotionCorePayloadNetwork.locatedReferences, NotionCorePayload.originReference]
              | item id =>
                  have known := located_item_known network session txs state received accepted
                    block index address selected inst id decoded
                  simpa [NotionCorePayloadNetwork.locatedReferences, NotionCorePayload.originReference] using known

theorem prepared_create_creators (network : NotionCorePayloadNetwork.State)
    (session : NotionRunAllocation.Session) (txs : List NotionCorePayload.Transaction) (state : State)
    (received : ∀ tx ∈ txs, ∃ entry ∈ network.entries, entry.tx = tx ∧
      NotionCorePayload.reservation tx ∈ (network.allocation.peers session).received)
    (accepted : replay {} txs = some state) (after : Option BlockKey) (payload : Payload)
    (prepared : prepareCreate state after = some payload) :
    ∀ key ∈ NotionCoreCreatorNetwork.requiredBlocks payload,
      NotionCoreCreatorNetwork.KnownCreator network session key := by
  cases after with
  | none => simp [prepareCreate] at prepared; subst payload; simp [NotionCoreCreatorNetwork.requiredBlocks]
  | some block =>
      by_cases present : state.forest.any (fun entry => entry.id == blockName block) = true
      · have same : Payload.create (some block) = payload := by simpa [prepareCreate, present] using prepared
        subst payload
        obtain ⟨found, member, name⟩ : ∃ found ∈ state.forest, found.id = blockName block := by simpa using present
        obtain ⟨key, encoded, known⟩ := NotionCoreMachineCreators.replay_known_creator
          network session txs state received accepted found member
        have equal : block = key := blockName_injective (name.symm.trans encoded)
        simpa [NotionCoreCreatorNetwork.requiredBlocks, equal] using known
      · simp [prepareCreate, present] at prepared

/-- Root-only core blocks use the same source selector and prepare the
independent visible gap from an actual stored physical partition. -/
theorem own_selection_prepared (state : State) (block : BlockKey)
    (before after : List NotionCorePartition.Cell) (cell : NotionCorePartition.Cell)
    (uniqueBlocks : (state.forest.map (·.id)).Nodup)
    (member : (⟨blockName block,
      .node ⟨cell.slice.start, after.head?.map (fun next => next.slice.start)⟩ .nil⟩ :
      NotionCoreSliceForest.Block) ∈ state.forest)
    (existsInstance : state.instances.any (fun entry => entry.1 == cell.slice.start.1) = true)
    (physicalEq : physical state cell.slice.start.1 = NotionCorePartition.flatten (before ++ cell :: after))
    (unique : ((physical state cell.slice.start.1).map Atom.address).Nodup)
    (index : Nat) (bound : index ≤ (characters cell.slice).length) :
    ∃ origin, locateAddress state block index = some origin ∧
      NotionCoreSpec.PreparedGap cell.slice.slots origin index := by
  let source : NotionCoreSource.Block := ⟨blockName block, .own, cell.slice⟩
  have found := find_block_member state.forest uniqueBlocks _ member
  have extracted := materialize_leaf state before after cell existsInstance physicalEq unique
  obtain ⟨origin, selected⟩ := NotionCorePreparation.locate_progress source index bound
  refine ⟨origin, ?_, NotionCorePreparation.locate_active_prepared source index origin selected⟩
  simpa [locateAddress, blockSlices, found, extracted, locateSlices,
    NotionCorePreparation.locate, NotionCorePreparation.nodes, source] using selected

/-- Physical partition and real forest membership derive successful source
selection and the independent semantic gap, including an all-deleted leaf. -/
theorem attached_selection_prepared (state : State) (block : BlockKey)
    (before after : List NotionCorePartition.Cell) (cell : NotionCorePartition.Cell)
    (uniqueBlocks : (state.forest.map (·.id)).Nodup)
    (member : (⟨blockName block, .node (NotionCoreSliceForest.titleRef (blockName block))
      (.cons (.node ⟨cell.slice.start, after.head?.map (fun next => next.slice.start)⟩ .nil) .nil)⟩ :
      NotionCoreSliceForest.Block) ∈ state.forest)
    (titleExists : state.instances.any (fun entry => entry.1 == blockName block) = true)
    (titleEmpty : physical state (blockName block) = [NotionCorePartition.boundary (blockName block,.start)])
    (activeExists : state.instances.any (fun entry => entry.1 == cell.slice.start.1) = true)
    (physicalEq : physical state cell.slice.start.1 = NotionCorePartition.flatten (before ++ cell :: after))
    (unique : ((physical state cell.slice.start.1).map Atom.address).Nodup)
    (index : Nat) (bound : index ≤ (characters cell.slice).length) :
    ∃ origin, locateAddress state block index = some origin ∧
      NotionCoreSpec.PreparedGap
        (NotionCoreSource.Block.project ⟨blockName block, .attached (blockName block), cell.slice⟩).slots
        origin index := by
  let source : NotionCoreSource.Block := ⟨blockName block, .attached (blockName block), cell.slice⟩
  have found := find_block_member state.forest uniqueBlocks _ member
  have extracted := materialize_attached state (blockName block) before after cell
    titleExists titleEmpty activeExists physicalEq unique
  obtain ⟨origin, selected⟩ := NotionCorePreparation.locate_progress source index bound
  refine ⟨origin, ?_, NotionCorePreparation.locate_prepared source index origin selected⟩
  simpa [locateAddress, blockSlices, found, extracted, locateSlices,
    NotionCorePreparation.locate, NotionCorePreparation.nodes, source] using selected

private def a : NotionRunAllocation.Id := ⟨1,[65]⟩
private def b : NotionRunAllocation.Id := ⟨3,[66]⟩
private def seed : NotionCorePayload.Transaction := NotionCorePayload.bootstrap [97,98]
private def cut : NotionCorePayload.Transaction := ⟨b,.split .initial .initial (.item a)⟩
private def splitState : Option State := replay {} [seed,cut]
private def deadState : Option State := replay {} [seed,cut,
  ⟨⟨4,[66]⟩,.erase (.issued b) .initial [⟨2,[65]⟩]⟩]

/-- Both a live inherited leaf and its all-deleted continuation select the
split marker at zero, not the unused destination title's START boundary. -/
theorem inherited_zero_control :
    (splitState >>= fun state => prepareInsert state (.issued b) 0 [88]) =
      some (.insert (.issued b) .initial (.item b) [88]) ∧
    (deadState >>= fun state => prepareSplit state (.issued b) 0) =
      some (.split (.issued b) .initial (.item b)) ∧
    (deadState >>= fun state => prepareSplit state (.issued b) 0) ≠
      some (.split (.issued b) (.issued b) .start) := by decide +kernel

/-- Positive positions count live atoms. Empty insertion and invalid block
selection do not manufacture payloads; create checks its real predecessor. -/
theorem client_boundaries_control :
    (splitState >>= fun state => prepareInsert state (.issued b) 1 [88]) =
      some (.insert (.issued b) .initial (.item ⟨2,[65]⟩) [88]) ∧
    prepareInsert {} .initial 0 [] = none ∧
    prepareSplit {} .initial 0 ≠ some (.split .initial .initial .start) ∧
    prepareCreate {} none = some (.create none) ∧
    prepareCreate {} (some (.issued b)) ≠ some (.create (some (.issued b))) := by decide +kernel

theorem deletion_selection_control :
    (splitState >>= fun state => deleteAddresses state (.issued b) 0 10) =
      some [NotionCorePhysicalReplay.address 0 ⟨2,[65]⟩] ∧
    (deadState >>= fun state => deleteAddresses state (.issued b) 0 10) ≠
      some [NotionCorePhysicalReplay.address 0 ⟨2,[65]⟩] ∧
    deleteAddresses {} .initial 1 1 = none := by decide +kernel

#print axioms decode_originAddress
#print axioms materialize_attached
#print axioms attached_selection_prepared
#print axioms locate_member
#print axioms locate_physical
#print axioms physical_decode_progress
#print axioms physical_decoded_known
#print axioms prepared_insert_references
#print axioms prepared_split_references
#print axioms locate_storage
#print axioms prepared_insert_creators
#print axioms prepared_split_creators
#print axioms prepared_create_creators
#print axioms own_selection_prepared
#print axioms inherited_zero_control
#print axioms client_boundaries_control
#print axioms deletion_selection_control
end Sal.MRDTs.Instances.NotionCoreMachineClient
