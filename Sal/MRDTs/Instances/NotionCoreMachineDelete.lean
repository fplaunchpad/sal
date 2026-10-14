import Sal.MRDTs.Instances.NotionCoreMachineClient
import Sal.MRDTs.Instances.NotionCoreRanges

/-! Single-instance core deletion preparation from actual client selection.
Every selected address must decode in the supplied instance; mixed selections
fail, rather than being truncated. General source multi-instance grouping is
outside this partial preparation. Targets are source-codec sorted, not physical
selection order. Success is not claimed for arbitrary machine states. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineDelete
open NotionRunAllocation (Id)
open NotionCoreSpec (Address)
open NotionCoreSource (Atom Slice)
open NotionCorePayload (BlockKey Payload Transaction)
open NotionCoreMachine
open NotionCoreMachineClient

def decodeTarget (inst : BlockKey) (address : Address) : Option Id :=
  match decodeAddress address with
  | some (actual, .item id) => if actual = inst then some id else none
  | _ => none

def decodeTargets (inst : BlockKey) (addresses : List Address) : Option (List Id) :=
  addresses.mapM (decodeTarget inst)

def prepareErase (state : State) (block inst : BlockKey) (start stop : Nat) : Option Payload := do
  let addresses ← deleteAddresses state block start stop
  let ids ← decodeTargets inst addresses
  pure (.erase block inst (NotionCoreRanges.expand (NotionCoreRanges.compress ids)))

private theorem decoded_member (inst : BlockKey) (addresses : List Address) (ids : List Id)
    (decoded : decodeTargets inst addresses = some ids) (id : Id) (member : id ∈ ids) :
    ∃ address ∈ addresses, decodeAddress address = some (inst,.item id) := by
  induction addresses generalizing ids with
  | nil => simp [decodeTargets] at decoded; subst ids; simp at member
  | cons address rest ih =>
      cases first : decodeTarget inst address with
      | none => simp [decodeTargets, first] at decoded
      | some selected =>
        cases later : decodeTargets inst rest with
        | none =>
          simp only [decodeTargets] at later
          simp [decodeTargets, first, later] at decoded
        | some tail =>
          have laterMap := later
          simp only [decodeTargets] at laterMap
          have equal : selected :: tail = ids := by simpa [decodeTargets, first, laterMap] using decoded
          subst ids
          rcases List.mem_cons.mp member with rfl | member
          · refine ⟨address, by simp, ?_⟩
            unfold decodeTarget at first
            split at first <;> try contradiction
            split at first <;> simp_all
          · obtain ⟨origin, present, source⟩ := ih tail later member
            exact ⟨origin, List.mem_cons_of_mem _ present, source⟩

private theorem selection_slices (state : State) (block : BlockKey) (start stop : Nat)
    (addresses : List Address) (selected : deleteAddresses state block start stop = some addresses) :
    ∃ found ∈ state.forest, found.id = blockName block ∧
      ∃ slices, materialize state found.title = some slices ∧
        addresses = (((slices.flatMap NotionCorePreparation.characters).drop start).take (stop-start)).map Atom.address := by
  unfold deleteAddresses at selected
  split at selected
  · contradiction
  · cases found : state.forest.find? (fun entry => entry.id == blockName block) with
    | none => simp [blockSlices, found] at selected
    | some tree =>
      cases extracted : materialize state tree.title with
      | none => simp [blockSlices, found, extracted] at selected
      | some slices =>
        refine ⟨tree, List.mem_of_find?_eq_some found, by simpa using List.find?_some found,
          slices, extracted, ?_⟩
        simp [blockSlices, found, extracted] at selected
        simpa only [List.map_take, List.map_drop] using selected.2.symm

/-- Every actual deletion target is physically stored in its own instance. -/
theorem delete_physical_member (state : State) (block : BlockKey) (start stop : Nat)
    (addresses : List Address) (selected : deleteAddresses state block start stop = some addresses)
    (address : Address) (member : address ∈ addresses) :
    address ∈ (physical state address.1).map Atom.address := by
  obtain ⟨found, stored, name, slices, extracted, equal⟩ := selection_slices state block start stop addresses selected
  rw [equal] at member
  obtain ⟨atom, present, same⟩ := List.mem_map.mp member
  have visible := List.mem_of_mem_drop (List.mem_of_mem_take present)
  obtain ⟨slice, inside, character⟩ := List.mem_flatMap.mp visible
  have atomMember := (List.mem_filter.mp character).1
  have belongs := (materialized_physical state found.title slices extracted slice inside).2 atom atomMember
  have storedInst := (materialized_storage state found.title slices extracted slice inside).2 atom atomMember
  have instEq : slice.start.1 = address.1 := storedInst.symm.trans (congrArg Prod.fst same)
  rw [instEq] at belongs
  exact List.mem_map.mpr ⟨atom, belongs, same⟩

private theorem preparation_data (state : State) (block inst : BlockKey) (start stop : Nat)
    (payload : Payload) (prepared : prepareErase state block inst start stop = some payload) :
    ∃ addresses ids, deleteAddresses state block start stop = some addresses ∧
      decodeTargets inst addresses = some ids ∧
      payload = .erase block inst (NotionCoreRanges.expand (NotionCoreRanges.compress ids)) := by
  cases selected : deleteAddresses state block start stop with
  | none => simp [prepareErase, selected] at prepared
  | some addresses =>
    cases decoded : decodeTargets inst addresses with
    | none => simp [prepareErase, selected, decoded] at prepared
    | some ids =>
      simp [prepareErase, selected, decoded] at prepared
      exact ⟨addresses, ids, rfl, decoded, prepared.symm⟩

theorem prepared_known (network : NotionCorePayloadNetwork.State)
    (session : NotionRunAllocation.Session) (txs : List Transaction) (state : State)
    (received : ∀ tx ∈ txs, ∃ entry ∈ network.entries, entry.tx = tx ∧
      NotionCorePayload.reservation tx ∈ (network.allocation.peers session).received)
    (accepted : replay {} txs = some state) (block inst : BlockKey) (start stop : Nat) (payload : Payload)
    (prepared : prepareErase state block inst start stop = some payload) :
    ∀ address ∈ NotionCorePayloadNetwork.locatedReferences payload,
      NotionCorePayloadNetwork.Known network session address := by
  obtain ⟨addresses, ids, selected, decoded, equal⟩ := preparation_data state block inst start stop payload prepared
  subst payload
  intro reference member
  simp only [NotionCorePayloadNetwork.locatedReferences, List.mem_map] at member
  obtain ⟨id, present, rfl⟩ := member
  rw [NotionCoreRanges.expand_compress] at present
  have original := (NotionCoreRanges.sorted_perm ids).mem_iff.mp present
  obtain ⟨address, member, source⟩ := decoded_member inst addresses ids decoded id original
  exact physical_decoded_known network session txs state received accepted address
    (delete_physical_member state block start stop addresses selected address member) inst id source

/-- Public positional request: infer the instance from the first actual
selected item, then validate the entire selection in that instance. -/
def selectErase (state : State) (block : BlockKey) (start stop : Nat) : Option Payload := do
  let addresses ← deleteAddresses state block start stop
  let first ← addresses.head?
  let (inst, origin) ← decodeAddress first
  match origin with
  | .start => none
  | .item _ => prepareErase state block inst start stop

private theorem selection_data (state : State) (block : BlockKey) (start stop : Nat)
    (payload : Payload) (prepared : selectErase state block start stop = some payload) :
    ∃ addresses first inst id, deleteAddresses state block start stop = some addresses ∧
      addresses.head? = some first ∧ decodeAddress first = some (inst,.item id) ∧
        prepareErase state block inst start stop = some payload := by
  cases selected : deleteAddresses state block start stop with
  | none => simp [selectErase, selected] at prepared
  | some addresses =>
    cases head : addresses.head? with
    | none => simp [selectErase, selected, head] at prepared
    | some first =>
      cases decoded : decodeAddress first with
      | none => simp [selectErase, selected, head, decoded] at prepared
      | some pair =>
        rcases pair with ⟨inst, origin⟩
        cases origin with
        | start => simp [selectErase, selected, head, decoded] at prepared
        | item id =>
          simp [selectErase, selected, head, decoded] at prepared
          exact ⟨addresses, first, inst, id, rfl, head, decoded, prepared⟩

/-- Successful deletion preparation emits only an erase payload; no
insert/split instance-selection obligation is hidden in this request case. -/
theorem selectErase_kind (state : State) (block : BlockKey) (start stop : Nat) (payload : Payload)
    (prepared : selectErase state block start stop = some payload) :
    ∃ inst ids, payload = .erase block inst ids := by
  obtain ⟨_,_,inst,_,_,_,_,preparedInst⟩ := selection_data state block start stop payload prepared
  obtain ⟨_,ids,_,_,equal⟩ := preparation_data state block inst start stop payload preparedInst
  exact ⟨inst,_,equal⟩

theorem selectErase_references (network : NotionCorePayloadNetwork.State)
    (session : NotionRunAllocation.Session) (txs : List Transaction) (state : State)
    (received : ∀ tx ∈ txs, ∃ entry ∈ network.entries, entry.tx = tx ∧
      NotionCorePayload.reservation tx ∈ (network.allocation.peers session).received)
    (accepted : replay {} txs = some state) (block : BlockKey) (start stop : Nat) (payload : Payload)
    (prepared : selectErase state block start stop = some payload) :
    ∀ address ∈ NotionCorePayloadNetwork.locatedReferences payload,
      NotionCorePayloadNetwork.Known network session address := by
  obtain ⟨addresses, first, inst, id, selected, head, decoded, preparedInst⟩ :=
    selection_data state block start stop payload prepared
  exact prepared_known network session txs state received accepted block inst start stop payload preparedInst

private theorem delete_instance_member (state : State) (block : BlockKey) (start stop : Nat)
    (addresses : List Address) (selected : deleteAddresses state block start stop = some addresses)
    (address : Address) (member : address ∈ addresses) :
    address.1 ∈ NotionCoreMachineCreators.instanceKeys state := by
  obtain ⟨found, stored, name, slices, extracted, equal⟩ := selection_slices state block start stop addresses selected
  rw [equal] at member
  obtain ⟨atom, present, same⟩ := List.mem_map.mp member
  have visible := List.mem_of_mem_drop (List.mem_of_mem_take present)
  obtain ⟨slice, inside, character⟩ := List.mem_flatMap.mp visible
  have atomMember := (List.mem_filter.mp character).1
  obtain ⟨⟨entry, stored, name⟩, sameInstance⟩ := materialized_storage state found.title slices extracted slice inside
  have key : entry.1 = address.1 := name.trans ((sameInstance atom atomMember).symm.trans (congrArg Prod.fst same))
  exact List.mem_map.mpr ⟨entry, stored, key⟩

private theorem decoded_block (address : Address) (inst : BlockKey) (origin : NotionCoreOriginTree.Origin)
    (decoded : decodeAddress address = some (inst,origin)) : decodeBlock address.1 = some inst := by
  cases block : decodeBlock address.1 with
  | none => simp [decodeAddress, block] at decoded
  | some actual =>
    cases item : decodeOrigin address.2 with
    | none => simp [decodeAddress, block, item] at decoded
    | some value =>
      simp [decodeAddress, block, item] at decoded
      exact congrArg some decoded.1

theorem selectErase_creators (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network)
    (session : NotionRunAllocation.Session) (txs : List Transaction) (state : State)
    (received : ∀ tx ∈ txs, ∃ entry ∈ network.entries, entry.tx = tx ∧
      NotionCorePayload.reservation tx ∈ (network.allocation.peers session).received)
    (accepted : replay {} txs = some state) (block : BlockKey) (start stop : Nat) (payload : Payload)
    (prepared : selectErase state block start stop = some payload) :
    ∀ key ∈ NotionCoreCreatorNetwork.requiredBlocks payload,
      NotionCoreCreatorNetwork.KnownCreator network session key := by
  obtain ⟨addresses, first, inst, id, selected, head, decoded, preparedInst⟩ :=
    selection_data state block start stop payload prepared
  obtain ⟨found, foundMember, name, slices, extracted, equal⟩ := selection_slices state block start stop addresses selected
  obtain ⟨key, keyName, knownBlock⟩ := NotionCoreMachineCreators.replay_known_creator
    network session txs state received accepted found foundMember
  have sameBlock : block = key := blockName_injective (name.symm.trans keyName)
  have firstMember := List.mem_of_mem_head? head
  obtain ⟨key, encoded, knownInst⟩ := NotionCoreMachineCreators.replay_known_instance_creator
    network reachable session txs state received accepted first.1
      (delete_instance_member state block start stop addresses selected first firstMember)
  have blockDecoded : decodeBlock first.1 = some key := by rw [← encoded]; exact decode_blockName key
  have sameInst : key = inst := Option.some.inj (blockDecoded.symm.trans (decoded_block first inst (.item id) decoded))
  obtain ⟨addresses', ids, selected', decoded', equalPayload⟩ := preparation_data state block inst start stop payload preparedInst
  subst payload
  intro requested member
  simp [NotionCoreCreatorNetwork.requiredBlocks] at member
  rcases member with rfl | rfl
  · exact sameBlock ▸ knownBlock
  · exact sameInst ▸ knownInst

private def a : Id := ⟨1,[65]⟩
private def b : Id := ⟨2,[65]⟩
private def x : Id := ⟨3,[66]⟩
private def seed : Transaction := NotionCorePayload.bootstrap [97,98]
private def insertion : Transaction := ⟨x,.insert .initial .initial .start [88]⟩
private def cut : Transaction := ⟨x,.split .initial .initial (.item a)⟩

private def insertedState : State :=
  ⟨[(blockName .initial, ⟨[⟨⟨a,.text 97 false⟩,.start⟩,
    ⟨⟨b,.text 98 false⟩,.item a⟩,⟨⟨x,.text 88 false⟩,.start⟩],[]⟩)],
    [⟨blockName .initial,NotionCoreSliceForest.freshTitle (blockName .initial)⟩],[blockName .initial]⟩
private def splitState : State :=
  ⟨[(blockName .initial, ⟨[⟨⟨a,.text 97 false⟩,.start⟩,
    ⟨⟨b,.text 98 false⟩,.item a⟩,⟨⟨x,.split⟩,.item a⟩],[]⟩), (blockName (.issued x),{})],
    [⟨blockName .initial,.node ⟨(blockName .initial,.start),some (NotionCorePhysicalReplay.address (blockName .initial) x)⟩ .nil⟩,
     ⟨blockName (.issued x),.node (NotionCoreSliceForest.titleRef (blockName (.issued x)))
       (.cons (.node ⟨NotionCorePhysicalReplay.address (blockName .initial) x,none⟩ .nil) .nil)⟩],
    [blockName .initial,blockName (.issued x)]⟩

/-- PASS+FAIL: deleting X then a in physical order emits source-codec sorted
IDs a then X. It does not silently use the visible selection order. -/
theorem sorted_delete_control :
    ((replay {} [seed,insertion]).bind fun state => selectErase state .initial 0 2) =
      some (.erase .initial .initial [a,x]) ∧
    ((replay {} [seed,insertion]).bind fun state => selectErase state .initial 0 2) ≠
      some (.erase .initial .initial [x,a]) := by
  have run : replay {} [seed,insertion] = some insertedState := by decide
  have selected : deleteAddresses insertedState .initial 0 2 =
      some [NotionCorePhysicalReplay.originAddress (blockName .initial) (.item x),
        NotionCorePhysicalReplay.originAddress (blockName .initial) (.item a)] := by decide
  simp [run, selectErase, prepareErase, selected, decodeTargets, decodeTarget,
    decode_originAddress, NotionCoreRanges.expand_compress,
    NotionCoreRanges.sorted, List.mergeSort, NotionCoreRanges.Asc,
    NotionCoreSourceInvariant.Desc, NotionRunAllocation.Before, a, x]

/-- PASS+FAIL: an attached leaf deletes in its inherited text instance; the
empty destination title is not substituted as the target instance. -/
theorem inherited_delete_control :
    ((replay {} [seed,cut]).bind fun state => selectErase state (.issued x) 0 1) =
      some (.erase (.issued x) .initial [b]) ∧
    ((replay {} [seed,cut]).bind fun state => selectErase state (.issued x) 0 1) ≠
      some (.erase (.issued x) (.issued x) [b]) := by
  have run : replay {} [seed,cut] = some splitState := by decide
  have selected : deleteAddresses splitState (.issued x) 0 1 =
    some [NotionCorePhysicalReplay.originAddress (blockName .initial) (.item b)] := by decide
  simp [run, selectErase, prepareErase, selected, decodeTargets, decodeTarget,
    decode_originAddress, NotionCoreRanges.expand_compress,
    NotionCoreRanges.sorted]

/-- PASS+FAIL: the validator accepts both item IDs in one instance and rejects
mixed instances instead of deleting just the matching prefix. -/
theorem mixed_instance_control :
    decodeTargets .initial [NotionCorePhysicalReplay.address (blockName .initial) a,
      NotionCorePhysicalReplay.address (blockName .initial) b] = some [a,b] ∧
    decodeTargets .initial [NotionCorePhysicalReplay.address (blockName .initial) a,
      NotionCorePhysicalReplay.address (blockName (.issued x)) b] = none ∧
    decodeTargets .initial [NotionCorePhysicalReplay.address (blockName .initial) a,
      NotionCorePhysicalReplay.address (blockName (.issued x)) b] ≠ some [a] := by
  change decodeTargets .initial [NotionCorePhysicalReplay.originAddress (blockName .initial) (.item a),
      NotionCorePhysicalReplay.originAddress (blockName .initial) (.item b)] = some [a,b] ∧
    decodeTargets .initial [NotionCorePhysicalReplay.originAddress (blockName .initial) (.item a),
      NotionCorePhysicalReplay.originAddress (blockName (.issued x)) (.item b)] = none ∧
    decodeTargets .initial [NotionCorePhysicalReplay.originAddress (blockName .initial) (.item a),
      NotionCorePhysicalReplay.originAddress (blockName (.issued x)) (.item b)] ≠ some [a]
  simp [decodeTargets, decodeTarget, decode_originAddress]

#print axioms selectErase_references
#print axioms selectErase_creators
end Sal.MRDTs.Instances.NotionCoreMachineDelete
