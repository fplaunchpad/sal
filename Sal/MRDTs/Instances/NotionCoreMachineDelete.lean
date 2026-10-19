import Sal.MRDTs.Instances.NotionCoreMachineClient
import Sal.MRDTs.Instances.NotionCoreRanges

/-! Core deletion preparation from actual client selection. The selected
visible range is grouped into runs of one text instance in display order, and
every address of a run must decode as an item of that run's instance; a run
that does not decode fails the whole request rather than being dropped.
Targets within a run are source-codec sorted, not physical selection order.
Success is not claimed for arbitrary machine states. -/
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

/-- Consecutive selected addresses of one text instance, in display order. -/
def runs : List Address → List (Nat × List Address)
  | [] => []
  | address :: rest =>
      match runs rest with
      | (key, members) :: later =>
          if key = address.1 then (key, address :: members) :: later
          else (address.1, [address]) :: (key, members) :: later
      | [] => [(address.1, [address])]

theorem runs_flatten (addresses : List Address) : (runs addresses).flatMap Prod.snd = addresses := by
  induction addresses with
  | nil => rfl
  | cons address rest ih =>
    simp only [runs]
    split
    · rename_i key members later found
      rw [found] at ih
      split <;> simp_all
    · rename_i found
      rw [found] at ih
      simp_all

theorem runs_key (addresses : List Address) :
    ∀ group ∈ runs addresses, ∀ address ∈ group.2, address.1 = group.1 := by
  induction addresses with
  | nil => simp [runs]
  | cons address rest ih =>
    simp only [runs]
    split
    · rename_i key members later found
      rw [found] at ih
      split
      · rename_i same
        intro group member address inside
        rcases List.mem_cons.mp member with rfl | member
        · rcases List.mem_cons.mp inside with rfl | inside
          · exact same.symm
          · exact ih (key, members) (by simp) _ inside
        · exact ih _ (List.mem_cons_of_mem _ member) _ inside
      · intro group member address inside
        rcases List.mem_cons.mp member with rfl | member
        · simp_all
        · exact ih _ member _ inside
    · intro group member address inside
      simp_all

theorem runs_nonempty (addresses : List Address) : ∀ group ∈ runs addresses, group.2 ≠ [] := by
  induction addresses with
  | nil => simp [runs]
  | cons address rest ih =>
    simp only [runs]
    split
    · rename_i key members later found
      rw [found] at ih
      split
      · intro group member
        rcases List.mem_cons.mp member with rfl | member
        · simp
        · exact ih _ (List.mem_cons_of_mem _ member)
      · intro group member
        rcases List.mem_cons.mp member with rfl | member
        · simp
        · exact ih _ member
    · intro group member
      simp_all

/-- Decode one run of selected addresses into its instance and its
source-codec sorted item IDs. -/
def prepareGroup (group : Nat × List Address) : Option (BlockKey × List Id) := do
  let inst ← decodeBlock group.1
  let ids ← decodeTargets inst group.2
  pure (inst, NotionCoreRanges.expand (NotionCoreRanges.compress ids))

/-- Public positional request: select the visible range, group it into runs of
one text instance in display order, and decode every run in its instance. -/
def selectErase (state : State) (block : BlockKey) (start stop : Nat) : Option Payload := do
  let addresses ← deleteAddresses state block start stop
  let groups ← (runs addresses).mapM prepareGroup
  pure (.erase block groups)

theorem mapM_source {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (accepted : xs.mapM f = some ys) (value : β) (member : value ∈ ys) :
    ∃ x ∈ xs, f x = some value := by
  induction xs generalizing ys with
  | nil => simp at accepted; subst ys; simp at member
  | cons first rest ih =>
    cases one : f first with
    | none => simp [List.mapM_cons, one] at accepted
    | some head =>
      cases later : rest.mapM f with
      | none => simp [List.mapM_cons, one, later] at accepted
      | some tail =>
        have equal : head :: tail = ys := by simpa [List.mapM_cons, one, later] using accepted
        subst ys
        rcases List.mem_cons.mp member with rfl | inside
        · exact ⟨first, by simp, one⟩
        · obtain ⟨x, present, found⟩ := ih tail later inside
          exact ⟨x, List.mem_cons_of_mem _ present, found⟩

theorem group_data (group : Nat × List Address) (inst : BlockKey) (sorted : List Id)
    (prepared : prepareGroup group = some (inst, sorted)) :
    decodeBlock group.1 = some inst ∧ ∃ ids, decodeTargets inst group.2 = some ids ∧
      sorted = NotionCoreRanges.sorted ids := by
  cases block : decodeBlock group.1 with
  | none => simp [prepareGroup, block] at prepared
  | some key =>
    cases decoded : decodeTargets key group.2 with
    | none => simp [prepareGroup, block, decoded] at prepared
    | some ids =>
      have equal : (key, NotionCoreRanges.sorted ids) = (inst, sorted) := by
        simpa [prepareGroup, block, decoded, NotionCoreRanges.expand_compress] using prepared
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
      exact ⟨rfl, ids, decoded, rfl⟩

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

theorem selection_groups (state : State) (block : BlockKey) (start stop : Nat)
    (payload : Payload) (prepared : selectErase state block start stop = some payload) :
    ∃ addresses groups, deleteAddresses state block start stop = some addresses ∧
      (runs addresses).mapM prepareGroup = some groups ∧ payload = .erase block groups := by
  cases selected : deleteAddresses state block start stop with
  | none => simp [selectErase, selected] at prepared
  | some addresses =>
    cases grouped : (runs addresses).mapM prepareGroup with
    | none => simp [selectErase, selected, grouped] at prepared
    | some groups =>
      simp [selectErase, selected, grouped] at prepared
      exact ⟨addresses, groups, rfl, grouped, prepared.symm⟩

/-- Every prepared group comes from one run of the selection, decoded in its instance. -/
theorem prepared_group_source (addresses : List Address) (groups : List (BlockKey × List Id))
    (grouped : (runs addresses).mapM prepareGroup = some groups)
    (group : BlockKey × List Id) (member : group ∈ groups) :
    ∃ run ∈ runs addresses, prepareGroup run = some group := by
  exact mapM_source _ _ _ grouped group member

theorem prepared_known (network : NotionCorePayloadNetwork.State)
    (session : NotionRunAllocation.Session) (txs : List Transaction) (state : State)
    (received : ∀ tx ∈ txs, ∃ entry ∈ network.entries, entry.tx = tx ∧
      NotionCorePayload.reservation tx ∈ (network.allocation.peers session).received)
    (accepted : replay {} txs = some state) (block : BlockKey) (start stop : Nat) (payload : Payload)
    (prepared : selectErase state block start stop = some payload) :
    ∀ address ∈ NotionCorePayloadNetwork.locatedReferences payload,
      NotionCorePayloadNetwork.Known network session address := by
  obtain ⟨addresses, groups, selected, grouped, equal⟩ := selection_groups state block start stop payload prepared
  subst payload
  intro reference member
  simp only [NotionCorePayloadNetwork.locatedReferences, List.mem_flatMap, List.mem_map] at member
  obtain ⟨group, groupMember, id, present, rfl⟩ := member
  obtain ⟨run, runMember, preparedRun⟩ := prepared_group_source addresses groups grouped group groupMember
  obtain ⟨_, ids, decoded, sortedEq⟩ := group_data run group.1 group.2 preparedRun
  rw [sortedEq] at present
  have original := (NotionCoreRanges.sorted_perm ids).mem_iff.mp present
  obtain ⟨address, inRun, source⟩ := decoded_member group.1 run.2 ids decoded id original
  have inSelection : address ∈ addresses := by
    rw [← runs_flatten addresses]
    exact List.mem_flatMap.mpr ⟨run, runMember, inRun⟩
  exact physical_decoded_known network session txs state received accepted address
    (delete_physical_member state block start stop addresses selected address inSelection) group.1 id source

/-- A prepared erase names a stored block. -/
theorem selectErase_stored (state : State) (block : BlockKey) (start stop : Nat) (payload : Payload)
    (prepared : selectErase state block start stop = some payload) :
    ∃ found ∈ state.forest, found.id = blockName block := by
  obtain ⟨addresses, _, selected, _, _⟩ := selection_groups state block start stop payload prepared
  obtain ⟨found, member, name, _⟩ := selection_slices state block start stop addresses selected
  exact ⟨found, member, name⟩

/-- Successful deletion preparation emits only an erase payload; no
insert/split instance-selection obligation is hidden in this request case. -/
theorem selectErase_kind (state : State) (block : BlockKey) (start stop : Nat) (payload : Payload)
    (prepared : selectErase state block start stop = some payload) :
    ∃ groups, payload = .erase block groups := by
  obtain ⟨_, groups, _, _, equal⟩ := selection_groups state block start stop payload prepared
  exact ⟨groups, equal⟩

theorem selectErase_references (network : NotionCorePayloadNetwork.State)
    (session : NotionRunAllocation.Session) (txs : List Transaction) (state : State)
    (received : ∀ tx ∈ txs, ∃ entry ∈ network.entries, entry.tx = tx ∧
      NotionCorePayload.reservation tx ∈ (network.allocation.peers session).received)
    (accepted : replay {} txs = some state) (block : BlockKey) (start stop : Nat) (payload : Payload)
    (prepared : selectErase state block start stop = some payload) :
    ∀ address ∈ NotionCorePayloadNetwork.locatedReferences payload,
      NotionCorePayloadNetwork.Known network session address :=
  prepared_known network session txs state received accepted block start stop payload prepared

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

theorem selectErase_creators (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network)
    (session : NotionRunAllocation.Session) (txs : List Transaction) (state : State)
    (received : ∀ tx ∈ txs, ∃ entry ∈ network.entries, entry.tx = tx ∧
      NotionCorePayload.reservation tx ∈ (network.allocation.peers session).received)
    (accepted : replay {} txs = some state) (block : BlockKey) (start stop : Nat) (payload : Payload)
    (prepared : selectErase state block start stop = some payload) :
    ∀ key ∈ NotionCoreCreatorNetwork.requiredBlocks payload,
      NotionCoreCreatorNetwork.KnownCreator network session key := by
  obtain ⟨addresses, groups, selected, grouped, equalPayload⟩ :=
    selection_groups state block start stop payload prepared
  obtain ⟨found, foundMember, name, slices, extracted, equal⟩ := selection_slices state block start stop addresses selected
  obtain ⟨key, keyName, knownBlock⟩ := NotionCoreMachineCreators.replay_known_creator
    network session txs state received accepted found foundMember
  have sameBlock : block = key := blockName_injective (name.symm.trans keyName)
  subst payload
  intro requested member
  simp only [NotionCoreCreatorNetwork.requiredBlocks, List.mem_cons, List.mem_map] at member
  rcases member with rfl | ⟨group, groupMember, rfl⟩
  · exact sameBlock ▸ knownBlock
  · obtain ⟨run, runMember, preparedRun⟩ := prepared_group_source addresses groups grouped group groupMember
    obtain ⟨runDecoded, _⟩ := group_data run group.1 group.2 preparedRun
    obtain ⟨first, rest, runEq⟩ := List.exists_cons_of_ne_nil (runs_nonempty addresses run runMember)
    have firstRun : first ∈ run.2 := by simp [runEq]
    have firstKey : first.1 = run.1 := runs_key addresses run runMember first firstRun
    have firstSelected : first ∈ addresses := by
      rw [← runs_flatten addresses]
      exact List.mem_flatMap.mpr ⟨run, runMember, firstRun⟩
    obtain ⟨instKey, encoded, knownInst⟩ := NotionCoreMachineCreators.replay_known_instance_creator
      network reachable session txs state received accepted first.1
        (delete_instance_member state block start stop addresses selected first firstSelected)
    have blockDecoded : decodeBlock run.1 = some instKey := by
      rw [← firstKey, ← encoded]; exact decode_blockName instKey
    have sameInst : instKey = group.1 := Option.some.inj (blockDecoded.symm.trans runDecoded)
    exact sameInst ▸ knownInst

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
      some (.erase .initial [(.initial,[a,x])]) ∧
    ((replay {} [seed,insertion]).bind fun state => selectErase state .initial 0 2) ≠
      some (.erase .initial [(.initial,[x,a])]) := by
  have run : replay {} [seed,insertion] = some insertedState := by decide
  have selected : deleteAddresses insertedState .initial 0 2 =
      some [NotionCorePhysicalReplay.originAddress (blockName .initial) (.item x),
        NotionCorePhysicalReplay.originAddress (blockName .initial) (.item a)] := by decide
  have key : ∀ k o, (NotionCorePhysicalReplay.originAddress k o).1 = k := by
    intro k o; cases o <;> rfl
  simp [run, selectErase, prepareGroup, runs, selected, decodeTargets, decodeTarget, key,
    decode_originAddress, NotionCoreRanges.expand_compress,
    NotionCoreRanges.sorted, List.mergeSort, NotionCoreRanges.Asc,
    NotionCoreSourceInvariant.Desc, NotionRunAllocation.Before, a, x]

/-- PASS+FAIL: a split destination deletes in its inherited text instance; the
empty destination title is not substituted as the target instance. -/
theorem inherited_delete_control :
    ((replay {} [seed,cut]).bind fun state => selectErase state (.issued x) 0 1) =
      some (.erase (.issued x) [(.initial,[b])]) ∧
    ((replay {} [seed,cut]).bind fun state => selectErase state (.issued x) 0 1) ≠
      some (.erase (.issued x) [(.issued x,[b])]) := by
  have run : replay {} [seed,cut] = some splitState := by decide
  have selected : deleteAddresses splitState (.issued x) 0 1 =
    some [NotionCorePhysicalReplay.originAddress (blockName .initial) (.item b)] := by decide
  have key : ∀ k o, (NotionCorePhysicalReplay.originAddress k o).1 = k := by
    intro k o; cases o <;> rfl
  simp [run, selectErase, prepareGroup, runs, selected, decodeTargets, decodeTarget, key,
    decode_originAddress, NotionCoreRanges.expand_compress, NotionCoreRanges.sorted]

private def y : Id := ⟨4,[66]⟩
private def z : Id := ⟨5,[66]⟩
private def merged : List Transaction :=
  [NotionCorePayload.bootstrap [97], ⟨x,.create (some .initial)⟩,
    ⟨y,.insert (.issued x) (.issued x) .start [98]⟩, ⟨z,.merge (.issued x) .initial none⟩]

/-- PASS+FAIL: after the block holding b is merged into the block holding a,
a range crossing the merged boundary yields one group per text instance, in
display order. It is neither rejected nor collapsed into one instance. -/
theorem merged_boundary_control :
    ((replay {} merged).bind fun state => selectErase state .initial 0 2) =
      some (.erase .initial [(.initial,[a]),(.issued x,[y])]) ∧
    ((replay {} merged).bind fun state => selectErase state .initial 0 2) ≠
      some (.erase .initial [(.initial,[a,y])]) ∧
    ((replay {} merged).bind fun state => selectErase state .initial 0 2) ≠ none := by
  decide +kernel

#print axioms selectErase_references
#print axioms selectErase_creators
end Sal.MRDTs.Instances.NotionCoreMachineDelete
