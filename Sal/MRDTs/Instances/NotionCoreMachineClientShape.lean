import Sal.MRDTs.Instances.NotionCoreMachineClient
import Sal.MRDTs.Instances.NotionCoreSliceForest

/-! Honest insertion/split selection uses an active instance whenever the
actual forest has normal shape and physically empty inactive titles. This
is a local selection theorem; transporting that instance through another
canonical replay prefix remains a separate provenance obligation. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineClientShape
open NotionCoreMachine
open NotionCoreMachineClient
open NotionCoreSpec (Address)
open NotionCoreSource (Atom Slice)
open NotionCoreSliceForest (Normal NormalForest EmptyInactive profile active)

private theorem locate_single_instance (slice : Slice) (index : Nat) (address : Address)
    (stored : ∀ atom ∈ slice.atoms, atom.address.1 = slice.start.1)
    (selected : locateSlices [slice] index = some address) : address.1 = slice.start.1 := by
  obtain ⟨found,member,placement⟩ := locate_member [slice] index address selected
  have same := List.mem_singleton.mp member
  subst found
  rcases placement with rfl | member
  · rfl
  · obtain ⟨atom,member,equal⟩ := List.mem_map.mp member
    exact (congrArg Prod.fst equal).symm.trans (stored atom member)

private theorem locate_empty_title (bid : Nat) (slice : Slice) (index : Nat) :
    locateSlices [⟨(bid,.start),[]⟩,slice] index = locateSlices [slice] index := by
  cases index <;> simp [locateSlices,NotionCorePreparation.characters,NotionCorePreparation.zeroOrigin]

/-- Even an all-deleted inherited leaf supplies the zero-gap origin. The
empty own-title root never supplies a selected insertion/split instance. -/
theorem normal_tree_selected_instance (state : State) (bid : Nat)
    (tree : NotionCoreSliceForest.Tree) (normal : Normal bid tree)
    (empty : NotionCoreSliceForest.attached tree = true →
      physical state bid = NotionCoreSliceForest.emptyPhysical bid)
    (index : Nat) (address : Address)
    (selected : (materialize state tree >>= fun slices => locateSlices slices index) = some address) :
    address.1 = (active tree).start.1 := by
  cases normal with
  | own stop =>
    cases extracted : sliceAtoms state ⟨(bid,.start),stop⟩ with
    | none => simp [materialize,NotionCoreSliceForest.preorderTree,
        NotionCoreSliceForest.preorderChildren,extracted] at selected
    | some atoms =>
      have located : locateSlices [⟨(bid,.start),atoms⟩] index = some address := by
        simpa [materialize,NotionCoreSliceForest.preorderTree,
          NotionCoreSliceForest.preorderChildren,extracted] using selected
      exact locate_single_instance _ index address (slice_storage state _ atoms extracted).2 located
  | attached ref =>
    cases root : sliceAtoms state (NotionCoreSliceForest.titleRef bid) with
    | none => simp [materialize,NotionCoreSliceForest.preorderTree,
        NotionCoreSliceForest.preorderChildren,root] at selected
    | some roots =>
      have existsTitle : state.instances.any (fun entry => entry.1 == bid) = true := by
        simpa [NotionCoreSliceForest.titleRef] using (slice_storage state _ roots root).1
      have rootEmpty := NotionCoreMachineSlices.empty_title_atoms state bid existsTitle (empty rfl)
      have rootsEq : roots = [] := Option.some.inj (root.symm.trans rootEmpty)
      subst roots
      cases leaf : sliceAtoms state ref with
      | none => simp [materialize,NotionCoreSliceForest.preorderTree,
          NotionCoreSliceForest.preorderChildren,root,leaf] at selected
      | some atoms =>
        have located : locateSlices [⟨(bid,.start),[]⟩,⟨ref.start,atoms⟩] index = some address := by
          simpa [materialize,NotionCoreSliceForest.preorderTree,
            NotionCoreSliceForest.preorderChildren,root,leaf] using selected
        rw [locate_empty_title] at located
        exact locate_single_instance _ index address (slice_storage state ref atoms leaf).2 located

/-- The selected actual address belongs to an active instance of the current
forest. Creator knowledge alone cannot supply this conclusion. -/
theorem located_active_instance (state : State) (block : NotionCorePayload.BlockKey)
    (normal : NormalForest state.forest)
    (empty : EmptyInactive (physical state) (profile state.forest))
    (index : Nat) (address : Address)
    (selected : locateAddress state block index = some address) :
    ∃ found ∈ state.forest, (active found.title).start.1 = address.1 := by
  cases found : state.forest.find? (fun entry => entry.id == blockName block) with
  | none => simp [locateAddress,blockSlices,found] at selected
  | some entry =>
    have member := List.mem_of_find?_eq_some found
    have titleEmpty : NotionCoreSliceForest.attached entry.title = true →
        physical state entry.id = NotionCoreSliceForest.emptyPhysical entry.id := by
      intro attached
      exact empty _ (List.mem_map.mpr ⟨entry,member,rfl⟩) attached
    have location : (materialize state entry.title >>= fun slices => locateSlices slices index) = some address := by
      simpa [locateAddress,blockSlices,found] using selected
    exact ⟨entry,member,(normal_tree_selected_instance state entry.id entry.title
      (normal entry member) titleEmpty index address location).symm⟩

/-- Storage provenance ensures internal decoding preserves the selected
instance name, even though arbitrary natural numbers are not canonical names. -/
theorem located_decode_instance (txs : List NotionCorePayload.Transaction) (state : State)
    (accepted : replay {} txs = some state) (block : NotionCorePayload.BlockKey)
    (index : Nat) (address : Address) (selected : locateAddress state block index = some address)
    (inst : NotionCorePayload.BlockKey) (origin : NotionCoreOriginTree.Origin)
    (decoded : decodeAddress address = some (inst,origin)) : address.1 = blockName inst := by
  obtain ⟨_,entry,stored,name⟩ := locate_storage state block index address selected
  obtain ⟨_,_,key,_,encoded⟩ := NotionCoreMachineCreators.replay_instance_used txs state accepted address.1
    (List.mem_map.mpr ⟨entry,stored,name⟩)
  have blockDecoded : decodeBlock address.1 = some key := by rw [encoded]; exact decode_blockName key
  have same : key = inst := by
    cases selectedOrigin : decodeOrigin address.2 with
    | none => simp [decodeAddress,blockDecoded,selectedOrigin] at decoded
    | some old =>
      have pair : (key,old) = (inst,origin) := by simpa [decodeAddress,blockDecoded,selectedOrigin] using decoded
      exact congrArg Prod.fst pair
  exact encoded.trans (congrArg blockName same)

/-- Actual split preparation supplies the active-instance guard in its own
reconstructed document. No supplied instance-selection premise remains. -/
theorem prepared_split_active (txs : List NotionCorePayload.Transaction) (state : State)
    (accepted : replay {} txs = some state)
    (normal : NormalForest state.forest)
    (empty : EmptyInactive (physical state) (profile state.forest))
    (block inst : NotionCorePayload.BlockKey) (index : Nat) (origin : NotionCoreOriginTree.Origin)
    (prepared : prepareSplit state block index = some (.split block inst origin)) :
    ∃ found ∈ state.forest, (active found.title).start.1 = blockName inst := by
  cases selected : locateAddress state block index with
  | none => simp [prepareSplit,selected] at prepared
  | some address =>
    cases decoded : decodeAddress address with
    | none => simp [prepareSplit,selected,decoded] at prepared
    | some location =>
      obtain ⟨key,oldOrigin⟩ := location
      have same : key = inst ∧ oldOrigin = origin := by simpa [prepareSplit,selected,decoded] using prepared
      obtain ⟨rfl,rfl⟩ := same
      have instanceEq := located_decode_instance txs state accepted block index address selected key oldOrigin decoded
      obtain ⟨found,member,equal⟩ := located_active_instance state block normal empty index address selected
      exact ⟨found,member,equal.trans instanceEq⟩

/-- Nonempty honest insertion selects an active instance as well. -/
theorem prepared_insert_active (txs : List NotionCorePayload.Transaction) (state : State)
    (accepted : replay {} txs = some state)
    (normal : NormalForest state.forest)
    (empty : EmptyInactive (physical state) (profile state.forest))
    (block inst : NotionCorePayload.BlockKey) (index : Nat) (atoms : List Nat)
    (origin : NotionCoreOriginTree.Origin)
    (prepared : prepareInsert state block index atoms = some (.insert block inst origin atoms)) :
    ∃ found ∈ state.forest, (active found.title).start.1 = blockName inst := by
  cases skipped : atoms.isEmpty with
  | true => simp [prepareInsert,skipped] at prepared
  | false =>
    cases selected : locateAddress state block index with
    | none => simp [prepareInsert,skipped,selected] at prepared
    | some address =>
      cases decoded : decodeAddress address with
      | none => simp [prepareInsert,skipped,selected,decoded] at prepared
      | some location =>
        obtain ⟨key,oldOrigin⟩ := location
        have same : key = inst ∧ oldOrigin = origin := by
          simpa [prepareInsert,skipped,selected,decoded] using prepared
        obtain ⟨rfl,rfl⟩ := same
        have instanceEq := located_decode_instance txs state accepted block index address selected key oldOrigin decoded
        obtain ⟨found,member,equal⟩ := located_active_instance state block normal empty index address selected
        exact ⟨found,member,equal.trans instanceEq⟩

#print axioms prepared_split_active
#print axioms prepared_insert_active

#print axioms normal_tree_selected_instance
#print axioms located_active_instance
end Sal.MRDTs.Instances.NotionCoreMachineClientShape
