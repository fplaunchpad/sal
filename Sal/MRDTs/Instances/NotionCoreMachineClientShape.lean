import Sal.MRDTs.Instances.NotionCoreMachineClient
import Sal.MRDTs.Instances.NotionCoreSliceForest

/-! Honest insertion/split selection uses a live instance whenever the
actual forest's dead titles are physically empty. This is a local selection
theorem; transporting that instance through another canonical replay prefix
remains a separate provenance obligation. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineClientShape
open NotionCoreMachine
open NotionCoreMachineClient
open NotionCoreSpec (Address)
open NotionCoreSource (Atom Slice)
open NotionCoreSliceForest (Normal EmptyInactive forestNodes active nodes)
open NotionCorePreparation (characters zeroOrigin)

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

private theorem zero_position (slices : List Slice) (origin : Address)
    (selected : zeroOrigin slices = some origin) :
    ∃ pre slice post, slices = pre ++ slice :: post ∧ origin = slice.start ∧
      (characters slice ≠ [] ∨ post = []) := by
  induction slices with
  | nil => simp [zeroOrigin] at selected
  | cons slice rest ih =>
      cases rest with
      | nil => exact ⟨[], slice, [], rfl, by simpa [zeroOrigin] using selected.symm, Or.inr rfl⟩
      | cons next rest =>
          by_cases empty : (characters slice).isEmpty = true
          · have tail : zeroOrigin (next :: rest) = some origin := by
              simpa [zeroOrigin, empty] using selected
            obtain ⟨pre, found, post, shape, same, kind⟩ := ih tail
            exact ⟨slice :: pre, found, post, by simp [shape], same, kind⟩
          · have same : slice.start = origin := by simpa [zeroOrigin, empty] using selected
            exact ⟨[], slice, next :: rest, rfl, same.symm, Or.inl (by simpa using empty)⟩

private theorem mapM_length {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (mapped : xs.mapM f = some ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil => simp at mapped; subst ys; rfl
  | cons head rest ih =>
    cases first : f head with
    | none => simp [first] at mapped
    | some value =>
      cases tail : rest.mapM f with
      | none => simp [first, tail] at mapped
      | some values =>
        have whole : value :: values = ys := by simpa [first, tail] using mapped
        subst ys
        simp [ih values tail]

private theorem mapM_split {α β : Type} (f : α → Option β) (xs : List α) (pre post : List β) (y : β)
    (mapped : xs.mapM f = some (pre ++ y :: post)) :
    ∃ a x b, xs = a ++ x :: b ∧ f x = some y ∧ b.length = post.length := by
  induction xs generalizing pre with
  | nil => simp at mapped
  | cons head rest ih =>
    cases first : f head with
    | none => simp [first] at mapped
    | some value =>
      cases tail : rest.mapM f with
      | none => simp [first, tail] at mapped
      | some values =>
        have whole : value :: values = pre ++ y :: post := by simpa [first, tail] using mapped
        cases pre with
        | nil =>
          obtain ⟨rfl, rfl⟩ := List.cons.inj whole
          exact ⟨[], head, rest, rfl, first, (mapM_length f rest _ tail).symm⟩
        | cons p pre =>
          obtain ⟨-, later⟩ := List.cons.inj whole
          obtain ⟨a, x, b, shape, found, lengths⟩ := ih pre (by rw [tail, later]; rfl)
          exact ⟨head :: a, x, b, by simp [shape], found, lengths⟩

/-- A node whose extracted slice holds an atom is live: dead nodes are
empty title roots. -/
private theorem nonempty_live (state : State) (empty : EmptyInactive (physical state) state.forest)
    (block : NotionCoreSliceForest.Block) (member : block ∈ state.forest)
    (ref : NotionCoreSliceForest.Ref) (inside : ref ∈ NotionCoreSliceForest.preorderTree block.title)
    (atoms : List Atom) (extracted : sliceAtoms state ref = some atoms) (nonempty : atoms ≠ []) :
    (ref, true) ∈ forestNodes state.forest := by
  have tagged : ref ∈ (nodes (NotionCoreSliceForest.preorderTree block.title)).map Prod.fst := by
    simpa [nodes, NotionCoreSliceForest.tagBefore_fst] using inside
  obtain ⟨⟨found, live⟩, taggedMember, rfl⟩ := List.mem_map.mp tagged
  have forestMember : ((found, live) : NotionCoreSliceForest.Ref × Bool) ∈ forestNodes state.forest :=
    List.mem_flatMap.mpr ⟨block, member, taggedMember⟩
  cases live with
  | true => exact forestMember
  | false =>
    obtain ⟨form, physicalEmpty, _⟩ := empty found forestMember
    have existsInstance : state.instances.any (fun entry => entry.1 == found.start.1) = true := by
      simpa using (slice_storage state found atoms extracted).1
    have none := NotionCoreMachineSlices.empty_title_atoms state found.start.1 existsInstance
      (by simpa [NotionCoreSliceForest.emptyPhysical] using physicalEmpty)
    rw [← form, extracted] at none
    exact False.elim (nonempty (Option.some.inj none))

/-- The selected actual address belongs to a live instance of the current
forest. Creator knowledge alone cannot supply this conclusion. -/
theorem located_active_instance (state : State) (block : NotionCorePayload.BlockKey)
    (empty : EmptyInactive (physical state) state.forest)
    (index : Nat) (address : Address)
    (selected : locateAddress state block index = some address) :
    ∃ live, (live,true) ∈ forestNodes state.forest ∧ live.start.1 = address.1 := by
  cases found : state.forest.find? (fun entry => entry.id == blockName block) with
  | none => simp [locateAddress,blockSlices,found] at selected
  | some entry =>
    have member := List.mem_of_find?_eq_some found
    cases materialized : materialize state entry.title with
    | none => simp [locateAddress,blockSlices,found,materialized] at selected
    | some slices =>
      have location : locateSlices slices index = some address := by
        simpa [locateAddress,blockSlices,found,materialized] using selected
      simp only [locateSlices] at location
      by_cases bound : index ≤ (slices.flatMap characters).length
      · rw [if_pos bound] at location
        cases index with
        | zero =>
          obtain ⟨pre, slice, post, shape, same, kind⟩ := zero_position slices address location
          rw [shape] at materialized
          obtain ⟨before, ref, after, refs, extracted, lengths⟩ := mapM_split _ _ pre post slice materialized
          cases sliced : sliceAtoms state ref with
          | none => simp [sliced] at extracted
          | some atoms =>
            have sliceEq : (⟨ref.start, atoms⟩ : Slice) = slice := by simpa [sliced] using extracted
            subst slice
            refine ⟨ref, ?_, by rw [same]⟩
            rcases kind with visible | last
            · apply nonempty_live state empty entry member ref (by rw [refs]; simp) atoms sliced
              intro none
              apply visible
              simp [none, characters]
            · have tail : after = [] := List.eq_nil_of_length_eq_zero (by rw [lengths, last]; rfl)
              subst after
              apply List.mem_flatMap.mpr ⟨entry, member, ?_⟩
              rw [refs]
              simp [nodes, NotionCoreSliceForest.tagBefore_append, NotionCoreSliceForest.tagBefore]
        | succ n =>
          obtain ⟨atom, chosen, equal⟩ := Option.map_eq_some_iff.mp location
          obtain ⟨slice, sliceMember, visible⟩ := List.mem_flatMap.mp (List.mem_of_getElem? chosen)
          obtain ⟨pre, post, shape⟩ := List.append_of_mem sliceMember
          rw [shape] at materialized
          obtain ⟨before, ref, after, refs, extracted, _⟩ := mapM_split _ _ pre post slice materialized
          cases sliced : sliceAtoms state ref with
          | none => simp [sliced] at extracted
          | some atoms =>
            have sliceEq : (⟨ref.start, atoms⟩ : Slice) = slice := by simpa [sliced] using extracted
            subst slice
            have atomMember : atom ∈ atoms := (List.mem_filter.mp visible).1
            refine ⟨ref, nonempty_live state empty entry member ref (by rw [refs]; simp) atoms sliced
              (List.ne_nil_of_mem atomMember), ?_⟩
            rw [← equal]
            exact ((slice_storage state ref atoms sliced).2 atom atomMember).symm
      · rw [if_neg bound] at location
        contradiction

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
    (empty : EmptyInactive (physical state) state.forest)
    (block inst : NotionCorePayload.BlockKey) (index : Nat) (origin : NotionCoreOriginTree.Origin)
    (prepared : prepareSplit state block index = some (.split block inst origin)) :
    ∃ live, (live,true) ∈ forestNodes state.forest ∧ live.start.1 = blockName inst := by
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
      obtain ⟨found,member,equal⟩ := located_active_instance state block empty index address selected
      exact ⟨found,member,equal.trans instanceEq⟩

/-- Nonempty honest insertion selects an active instance as well. -/
theorem prepared_insert_active (txs : List NotionCorePayload.Transaction) (state : State)
    (accepted : replay {} txs = some state)
    (empty : EmptyInactive (physical state) state.forest)
    (block inst : NotionCorePayload.BlockKey) (index : Nat) (atoms : List Nat)
    (origin : NotionCoreOriginTree.Origin)
    (prepared : prepareInsert state block index atoms = some (.insert block inst origin atoms)) :
    ∃ live, (live,true) ∈ forestNodes state.forest ∧ live.start.1 = blockName inst := by
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
        obtain ⟨found,member,equal⟩ := located_active_instance state block empty index address selected
        exact ⟨found,member,equal.trans instanceEq⟩

#print axioms prepared_split_active
#print axioms prepared_insert_active

#print axioms normal_tree_selected_instance
#print axioms located_active_instance
end Sal.MRDTs.Instances.NotionCoreMachineClientShape
