import Sal.MRDTs.Instances.NotionCoreMachineDocument
import Sal.MRDTs.Instances.NotionCoreSourceGuards
import Sal.MRDTs.Instances.NotionCoreMachineDocumentClient

/-! Projected semantic address uniqueness comes from the all-reference physical
partition and from anchor uniqueness. Dead title anchors participate; each
retained interval also materialises its close slot, named by the node's
anchor; tombstones hold no address, and display order only permutes the
stored blocks. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineDocumentInvariant
open NotionCoreMachine
open NotionCoreMachinePartition
open NotionCoreForestRefs (ownedRefs)
open NotionCorePartition (Cell flatten)
open NotionCoreSource (Atom)
open NotionCoreSpec (Address)
open NotionCoreSliceForest (Ref anchorOf)

/-- Addresses of one retained interval, including its semantic anchor. -/
def intervalAddresses (state : State) (ref : Ref) : List Address :=
  ref.start :: (NotionCorePartition.extract (physical state ref.start.1) ref.start ref.stop).map Atom.address

private theorem extracted_eq (state : State) (ref : Ref) (atoms : List Atom)
    (accepted : sliceAtoms state ref = some atoms) :
    atoms = NotionCorePartition.extract (physical state ref.start.1) ref.start ref.stop := by
  cases stop : ref.stop <;> simp [sliceAtoms,stop] at accepted
  all_goals simp_all

theorem interval_extracted (state : State) (ref : Ref) (atoms : List Atom)
    (accepted : sliceAtoms state ref = some atoms) :
    intervalAddresses state ref = ref.start :: atoms.map Atom.address := by
  rw [intervalAddresses,← extracted_eq state ref atoms accepted]

private theorem cell_refs_addresses (state : State) (inst : Nat) (before after : List Cell)
    (physicalEq : physical state inst = flatten (before ++ after))
    (sameInst : ∀ cell ∈ after, cell.slice.start.1 = inst)
    (unique : ((physical state inst).map Atom.address).Nodup) :
    (cellRefs after).flatMap (fun owned => intervalAddresses state owned.2) =
      (flatten after).map Atom.address := by
  induction after generalizing before with
  | nil => rfl
  | cons cell rest ih =>
    have name := sameInst cell (by simp)
    have extracted := NotionCorePartition.extract_cell before rest cell (physicalEq ▸ unique)
    have selected : intervalAddresses state ⟨cell.slice.start,rest.head?.map (fun next => next.slice.start)⟩ =
        cell.slice.start :: cell.slice.atoms.map Atom.address := by
      simp only [intervalAddresses,name,physicalEq,extracted]
    have nextPhysical : physical state inst = flatten ((before ++ [cell]) ++ rest) := by
      simpa only [List.append_assoc,List.singleton_append] using physicalEq
    have later := ih (before ++ [cell]) nextPhysical
      (fun next member => sameInst next (List.mem_cons_of_mem _ member))
    simp only [cellRefs,List.flatMap_cons,selected,later,flatten,List.flatMap_cons,List.map_append]
    rfl

/-- Physical addresses are positions: the instance start and its items. -/
theorem physical_positions (state : State) (inst : Nat) :
    ∀ address ∈ (physical state inst).map Atom.address, address.2.isEnd = false := by
  intro address member
  simp only [physical, NotionCorePhysicalReplay.physical, List.map_cons, List.mem_cons,
    List.mem_map] at member
  rcases member with rfl | ⟨atom, ⟨item, _, rfl⟩, rfl⟩
  · rfl
  · rfl

/-- Within each instance, every owned reference reconstructs exactly one
physical cell; its concatenated addresses permute the actual physical IDs. -/
theorem instance_addresses (state : State) (part : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (inst : Nat) (stored : ∃ entry ∈ state.instances, entry.1 = inst) :
    (((ownedRefs state.forest).filter (fun owned => owned.2.start.1 == inst)).flatMap
      (fun owned => intervalAddresses state owned.2)).Perm ((physical state inst).map Atom.address) := by
  obtain ⟨cells,physicalEq,permutation⟩ := part.partitions inst stored
  have sameInst : ∀ cell ∈ cells, cell.slice.start.1 = inst := by
    intro cell member
    obtain ⟨before,after,shape⟩ := List.mem_iff_append.mp member
    have belongs : (cell.owner,⟨cell.slice.start,after.head?.map (fun next => next.slice.start)⟩) ∈ cellRefs cells :=
      (cellRefs_member cells _).mpr ⟨before,cell,after,shape,rfl⟩
    have selected := (List.mem_filter.mp (permutation.mem_iff.mpr belongs)).2
    simpa using selected
  have exactCells := cell_refs_addresses state inst [] cells (by simpa using physicalEq) sameInst (unique inst)
  have p := permutation.flatMap_right (fun owned => intervalAddresses state owned.2)
  simpa [exactCells,← physicalEq] using p

private theorem interval_instance (state : State) (part : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (owned : Nat × Ref) (present : owned ∈ ownedRefs state.forest) :
    ∀ address ∈ intervalAddresses state owned.2, address.1 = owned.2.start.1 := by
  obtain ⟨atoms,extracted⟩ := ref_extracts state part unique owned present
  rw [interval_extracted state owned.2 atoms extracted]
  intro address member
  rcases List.mem_cons.mp member with rfl | member
  · rfl
  · obtain ⟨atom,inAtoms,rfl⟩ := List.mem_map.mp member
    exact (NotionCoreMachineClient.slice_storage state owned.2 atoms extracted).2 atom inAtoms

theorem interval_positions (state : State) (part : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (owned : Nat × Ref) (present : owned ∈ ownedRefs state.forest) :
    ∀ address ∈ intervalAddresses state owned.2, address.2.isEnd = false := by
  obtain ⟨atoms,extracted⟩ := ref_extracts state part unique owned present
  have stored := NotionCoreMachineClient.slice_physical state owned.2 atoms extracted
  rw [interval_extracted state owned.2 atoms extracted]
  intro address member
  rcases List.mem_cons.mp member with rfl | member
  · exact physical_positions state _ _ stored.1
  · obtain ⟨atom,inAtoms,rfl⟩ := List.mem_map.mp member
    exact physical_positions state owned.2.start.1 _ (List.mem_map.mpr ⟨atom,stored.2 atom inAtoms,rfl⟩)

/-- Every stored stop is the address of an item of the node's own instance:
the start of the next physical cell, which is never the instance start. -/
theorem stop_address (state : State) (part : Partitioned state)
    (owned : Nat × Ref) (present : owned ∈ ownedRefs state.forest) :
    ∀ stop ∈ owned.2.stop, ∃ id, stop = NotionCorePhysicalReplay.address owned.2.start.1 id := by
  obtain ⟨before,cell,after,physicalEq,equal⟩ := ref_factor state part owned present
  subst equal
  intro stop stopped
  cases after with
  | nil => simp at stopped
  | cons next rest =>
    have stopEq : stop = next.slice.start := by simpa using stopped.symm
    subst stop
    have startMember : cell.slice.start ∈ (flatten (before ++ [cell])).map Atom.address := by
      simp [flatten, NotionCorePartition.Cell.physical, NotionCorePartition.boundary]
    obtain ⟨first,rest',headEq⟩ : ∃ first rest', (flatten (before ++ [cell])).map Atom.address =
        first :: rest' := by
      cases h : (flatten (before ++ [cell])).map Atom.address with
      | nil => rw [h] at startMember; simp at startMember
      | cons first rest' => exact ⟨first,rest',rfl⟩
    have shape : (physical state cell.slice.start.1).map Atom.address =
        (flatten (before ++ [cell])).map Atom.address ++
          next.slice.start :: (next.slice.atoms ++ flatten rest).map Atom.address := by
      rw [physicalEq]
      simp [flatten, NotionCorePartition.Cell.physical, NotionCorePartition.boundary, List.append_assoc]
    have later : next.slice.start ∈ ((physical state cell.slice.start.1).map Atom.address).tail := by
      rw [shape, headEq]
      simp
    simp only [physical, NotionCorePhysicalReplay.physical, List.map_cons, List.tail_cons,
      List.map_map, List.mem_map, Function.comp_def] at later
    obtain ⟨item,_,itemEq⟩ := later
    exact ⟨item.id, itemEq.symm⟩

/-- Every stored stop is a split-marker event of the node's own instance. -/
theorem stop_event (state : State) (part : Partitioned state)
    (owned : Nat × Ref) (present : owned ∈ ownedRefs state.forest) :
    ∀ stop ∈ owned.2.stop, stop.1 = owned.2.start.1 ∧ ∃ marker, stop.2 = .event marker := by
  intro stop stopped
  obtain ⟨id,rfl⟩ := stop_address state part owned present stop stopped
  exact ⟨rfl, _, rfl⟩

/-- On nodes whose stops are items of their own instance, the close address
determines the anchor. -/
theorem close_injective {left right : Ref}
    (leftStop : ∀ stop ∈ left.stop, stop.1 = left.start.1 ∧ ∃ marker, stop.2 = .event marker)
    (rightStop : ∀ stop ∈ right.stop, stop.1 = right.start.1 ∧ ∃ marker, stop.2 = .event marker)
    (same : (anchorOf left).close = (anchorOf right).close) : anchorOf left = anchorOf right := by
  have inst : left.start.1 = right.start.1 := by
    simpa [NotionCoreSliceForest.Anchor.close, anchorOf] using congrArg Prod.fst same
  cases hl : left.stop with
  | none =>
    cases hr : right.stop with
    | none => simp [anchorOf, hl, hr, inst]
    | some stop =>
      obtain ⟨-,marker,event⟩ := rightStop stop (by simp [hr])
      obtain ⟨stopInst,stopId⟩ := stop
      simp only at event
      subst event
      simp [NotionCoreSliceForest.Anchor.close, anchorOf, hl, hr, NotionCoreSource.stopKey,
        NotionCoreSpec.closeOf, NotionCoreSpec.finishSlot, NotionCoreSpec.closeSlot] at same
  | some stop =>
    obtain ⟨leftInst,marker,event⟩ := leftStop stop (by simp [hl])
    obtain ⟨stopInst,stopId⟩ := stop
    simp only at event leftInst
    subst event
    cases hr : right.stop with
    | none =>
      simp [NotionCoreSliceForest.Anchor.close, anchorOf, hl, hr, NotionCoreSource.stopKey,
        NotionCoreSpec.closeOf, NotionCoreSpec.finishSlot, NotionCoreSpec.closeSlot] at same
    | some other =>
      obtain ⟨rightInst,otherMarker,otherEvent⟩ := rightStop other (by simp [hr])
      obtain ⟨otherInst,otherId⟩ := other
      simp only at otherEvent rightInst
      subst otherEvent
      have markers : marker = otherMarker := by
        simpa [NotionCoreSliceForest.Anchor.close, anchorOf, hl, hr, NotionCoreSource.stopKey,
          NotionCoreSpec.closeOf, NotionCoreSpec.closeSlot] using congrArg Prod.snd same
      simp [anchorOf, hl, hr, inst, markers, leftInst, rightInst]

private theorem filter_intervals (state : State) (part : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup) (inst : Nat)
    (refs : List (Nat × Ref)) (included : ∀ owned ∈ refs, owned ∈ ownedRefs state.forest) :
    ((refs.flatMap (fun owned => intervalAddresses state owned.2)).filter (fun address => address.1 == inst)) =
      (refs.filter (fun owned => owned.2.start.1 == inst)).flatMap (fun owned => intervalAddresses state owned.2) := by
  induction refs with
  | nil => rfl
  | cons owned rest ih =>
    have same := interval_instance state part unique owned (included owned (by simp))
    have later := ih (fun ref member => included ref (List.mem_cons_of_mem _ member))
    by_cases selected : owned.2.start.1 = inst
    · have keep : (intervalAddresses state owned.2).filter (fun address => address.1 == inst) = intervalAddresses state owned.2 := by
        apply List.filter_eq_self.mpr
        intro address member
        simp [same address member,selected]
      simp [List.flatMap_cons,List.filter_append,selected,keep,later]
    · have remove : (intervalAddresses state owned.2).filter (fun address => address.1 == inst) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro address member
        simp [same address member,selected]
      simp [List.flatMap_cons,List.filter_append,selected,remove,later]

private theorem nodup_of_instance_filters (addresses : List Address)
    (unique : ∀ inst, (addresses.filter (fun address => address.1 == inst)).Nodup) : addresses.Nodup := by
  induction addresses with
  | nil => simp
  | cons address rest ih =>
    have own : (address :: rest.filter (fun other => other.1 == address.1)).Nodup := by
      simpa using unique address.1
    apply List.nodup_cons.mpr
    constructor
    · intro member
      exact (List.nodup_cons.mp own).1 (List.mem_filter.mpr ⟨member,by simp⟩)
    · apply ih
      intro inst
      have whole := unique inst
      by_cases same : address.1 = inst
      · have selected : (address :: rest.filter (fun other => other.1 == inst)).Nodup := by
          simpa only [List.filter_cons,same,beq_self_eq_true,if_true] using whole
        exact (List.nodup_cons.mp selected).2
      · simpa [same] using whole

/-- No physical identity is repeated across the complete forest's retained
intervals, including inactive title boundaries. -/
theorem all_addresses_unique (state : State) (part : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup) :
    ((ownedRefs state.forest).flatMap (fun owned => intervalAddresses state owned.2)).Nodup := by
  apply nodup_of_instance_filters
  intro inst
  rw [filter_intervals state part unique inst (ownedRefs state.forest) (fun _ h => h)]
  by_cases stored : ∃ entry ∈ state.instances, entry.1 = inst
  · exact (instance_addresses state part unique inst stored).nodup_iff.mpr (unique inst)
  · have empty : (ownedRefs state.forest).filter (fun owned => owned.2.start.1 == inst) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro owned member
      have existsInst := part.refsExist owned member
      have different : owned.2.start.1 ≠ inst := fun equal => stored (equal ▸ existsInst)
      simpa using different
    simp [empty]

/-- The addresses one retained interval materialises to: its physical
interval followed by the close slot its anchor names. -/
def sliceAddresses (state : State) (ref : Ref) : List Address :=
  intervalAddresses state ref ++ [(anchorOf ref).close]

private theorem flatMap_append_perm {α β : Type} (xs : List α) (f g : α → List β) :
    (xs.flatMap fun x => f x ++ g x).Perm (xs.flatMap f ++ xs.flatMap g) := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    refine List.Perm.append_left (f x) ((List.Perm.append_left (g x) ih).trans ?_)
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm

/-- No address is repeated across the complete forest's materialised slices:
physical intervals are unique by the partition, close slots by anchor
uniqueness, and no physical position is a close slot. -/
theorem all_slice_addresses_unique (state : State) (part : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (anchors : NotionCoreSliceForest.AnchorsUnique state.forest) :
    ((ownedRefs state.forest).flatMap (fun owned => sliceAddresses state owned.2)).Nodup := by
  have anchorList : ((ownedRefs state.forest).map (fun owned => anchorOf owned.2)).Nodup := by
    have whole := anchors
    unfold NotionCoreSliceForest.AnchorsUnique at whole
    rw [← NotionCoreForestRefs.ownedRefs_refs, List.map_map] at whole
    exact whole
  have closes : ((ownedRefs state.forest).map (fun owned => (anchorOf owned.2).close)).Nodup := by
    have mapped : (ownedRefs state.forest).map (fun owned => (anchorOf owned.2).close) =
        ((ownedRefs state.forest).map (fun owned => anchorOf owned.2)).map
          NotionCoreSliceForest.Anchor.close := by
      simp [List.map_map, Function.comp_def]
    rw [mapped]
    apply anchorList.map_on
    intro x xMember y yMember same
    obtain ⟨left,leftMember,rfl⟩ := List.mem_map.mp xMember
    obtain ⟨right,rightMember,rfl⟩ := List.mem_map.mp yMember
    exact close_injective (stop_event state part left leftMember)
      (stop_event state part right rightMember) same
  have permutation := flatMap_append_perm (ownedRefs state.forest)
    (fun owned => intervalAddresses state owned.2) (fun owned => [(anchorOf owned.2).close])
  have singletons : ((ownedRefs state.forest).flatMap fun owned => [(anchorOf owned.2).close]) =
      (ownedRefs state.forest).map (fun owned => (anchorOf owned.2).close) := by
    induction ownedRefs state.forest with
    | nil => rfl
    | cons owned rest ih => simp [List.flatMap_cons, ih]
  rw [singletons] at permutation
  refine permutation.nodup_iff.mpr (List.nodup_append'.mpr ⟨all_addresses_unique state part unique,
    closes, List.disjoint_left.mpr ?_⟩)
  intro address inside closing
  obtain ⟨owned,ownedMember,held⟩ := List.mem_flatMap.mp inside
  obtain ⟨other,-,rfl⟩ := List.mem_map.mp closing
  have position := interval_positions state part unique owned ownedMember _ held
  rw [NotionCoreSliceForest.Anchor.close, NotionCoreSpec.closeOf_isEnd] at position
  exact Bool.noConfusion position

private theorem slices_addresses (state : State) (refs : List Ref) (slices : List NotionCoreSource.Slice)
    (accepted : refs.mapM (fun ref => do pure ⟨ref.start,← sliceAtoms state ref,ref.stop⟩) = some slices) :
    (slices.flatMap NotionCoreSource.Slice.slots).map NotionCoreSpec.Slot.address =
      refs.flatMap (sliceAddresses state) := by
  induction refs generalizing slices with
  | nil => simp at accepted; subst slices; rfl
  | cons ref rest ih =>
    cases extracted : sliceAtoms state ref with
    | none => simp [List.mapM_cons,extracted] at accepted
    | some atoms =>
      simp only [List.mapM_cons] at accepted
      obtain ⟨head,headRead,laterRead⟩ := Option.bind_eq_some_iff.mp accepted
      have headEq : head = (⟨ref.start,atoms,ref.stop⟩ : NotionCoreSource.Slice) := by
        simpa [extracted] using headRead.symm
      subst head
      obtain ⟨tail,following,same⟩ := Option.bind_eq_some_iff.mp laterRead
      have equal : (⟨ref.start,atoms,ref.stop⟩ : NotionCoreSource.Slice) :: tail = slices :=
        Option.some.inj same
      subst slices
      have later := ih tail following
      rw [List.flatMap_cons,List.map_append,later,List.flatMap_cons,sliceAddresses,
        interval_extracted state ref atoms extracted]
      simp [NotionCoreSource.Slice.slots,NotionCoreSource.Slice.anchor,NotionCoreSource.Slice.close,
        NotionCoreSliceForest.Anchor.close,anchorOf,List.map_map,Function.comp_def]

def blockAddresses (state : State) (block : NotionCoreSliceForest.Block) : List Address :=
  (NotionCoreSliceForest.preorderTree block.title).flatMap (sliceAddresses state)

/-- Semantic anchors, retained atoms and close slots are exactly all the
actual chain's slice addresses, including those of a dead title root. -/
theorem materialized_block_addresses (state : State)
    (block : NotionCoreSliceForest.Block) (source : NotionCoreSource.Block)
    (accepted : NotionCoreMachineDocument.materializeBlock state block = some source) :
    source.project.slots.map NotionCoreSpec.Slot.address = blockAddresses state block := by
  have nodes := (NotionCoreMachineDocument.materialized_slices state block source accepted).1
  have addresses := slices_addresses state (NotionCoreSliceForest.preorderTree block.title)
    source.slices nodes
  exact addresses

private def lookupAddresses (state : State) (bid : Nat) : List Address :=
  ((state.forest.find? (fun block => block.id == bid)).map (blockAddresses state)).getD []

private theorem named_addresses (state : State) (bid : Nat) (source : NotionCoreSource.Block)
    (accepted : NotionCoreMachineDocument.materializeEntry state bid = some source) :
    source.project.slots.map NotionCoreSpec.Slot.address = lookupAddresses state bid := by
  cases found : state.forest.find? (fun block => block.id == bid) with
  | none =>
    rw [NotionCoreMachineDocument.materializeEntry_tombstone state bid found] at accepted
    cases accepted
    simp [lookupAddresses,found,NotionCoreSource.Block.project,NotionCoreSource.Block.slots]
  | some block =>
    rw [NotionCoreMachineDocument.materializeEntry_stored state bid block found] at accepted
    simpa [lookupAddresses,found] using materialized_block_addresses state block source accepted

private theorem projected_addresses (state : State) (document : NotionCoreSourceDocument.Document)
    (accepted : NotionCoreMachineDocument.materializeDocument state = some document) :
    NotionCoreInvariant.addresses (NotionCoreSourceDocument.project document) =
      state.display.flatMap (lookupAddresses state) := by
  have sequence : ∀ (ids : List Nat) (doc : NotionCoreSourceDocument.Document),
      ids.mapM (NotionCoreMachineDocument.materializeEntry state) = some doc →
      NotionCoreInvariant.addresses (NotionCoreSourceDocument.project doc) = ids.flatMap (lookupAddresses state) := by
    intro ids
    induction ids with
    | nil => intro doc h; simp at h; subst doc; rfl
    | cons bid rest ih =>
      intro doc h
      simp only [List.mapM_cons] at h
      obtain ⟨source,first,later⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨tail,following,same⟩ := Option.bind_eq_some_iff.mp later
      have equal : source :: tail = doc := Option.some.inj same
      subst doc
      have headEq := named_addresses state bid source first
      have tailEq := ih tail following
      simpa [NotionCoreInvariant.addresses,NotionCoreSourceDocument.project] using congrArg₂ List.append headEq tailEq
  exact sequence state.display document accepted

private theorem flatMap_shown (state : State) (ids : List Nat) :
    ids.flatMap (lookupAddresses state) =
      (ids.filter fun bid => state.forest.any fun block => block.id == bid).flatMap (lookupAddresses state) := by
  induction ids with
  | nil => rfl
  | cons bid rest ih =>
    by_cases present : (state.forest.any fun block => block.id == bid) = true
    · simp [present, ih]
    · have absent : state.forest.find? (fun block => block.id == bid) = none := by
        apply List.find?_eq_none.mpr
        intro block member equal
        exact present (List.any_eq_true.mpr ⟨block,member,equal⟩)
      simp [present, ih, lookupAddresses, absent]

/-- The projected global address list permutes the actual forest's complete
physical partition; it is not inferred from visible text alone. -/
theorem projected_addresses_perm (state : State) (aligned : NotionCoreMachineDisplay.Aligned state)
    (document : NotionCoreSourceDocument.Document)
    (accepted : NotionCoreMachineDocument.materializeDocument state = some document) :
    (NotionCoreInvariant.addresses (NotionCoreSourceDocument.project document)).Perm
      ((ownedRefs state.forest).flatMap (fun owned => sliceAddresses state owned.2)) := by
  rw [projected_addresses state document accepted, flatMap_shown]
  have permutation := aligned.2.2.flatMap_right (lookupAddresses state)
  have exactForest : (state.forest.map NotionCoreSliceForest.Block.id).flatMap (lookupAddresses state) =
      state.forest.flatMap (blockAddresses state) := by
    rw [List.flatMap_map]
    apply List.flatMap_congr
    intro block member
    have found := NotionCoreMachineClient.find_block_member state.forest aligned.1 block member
    simp [lookupAddresses,found]
  change ((NotionCoreDisplayOrder.shown ⟨state.forest,state.display⟩).flatMap (lookupAddresses state)).Perm
    ((state.forest.map NotionCoreSliceForest.Block.id).flatMap (lookupAddresses state)) at permutation
  rw [exactForest] at permutation
  simpa [ownedRefs,List.flatMap_assoc,blockAddresses,List.flatMap_map,Function.comp_def,
    NotionCoreDisplayOrder.shown] using permutation

theorem projected_addresses_unique (state : State) (part : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (anchors : NotionCoreSliceForest.AnchorsUnique state.forest)
    (aligned : NotionCoreMachineDisplay.Aligned state)
    (document : NotionCoreSourceDocument.Document)
    (accepted : NotionCoreMachineDocument.materializeDocument state = some document) :
    (NotionCoreInvariant.addresses (NotionCoreSourceDocument.project document)).Nodup :=
  (projected_addresses_perm state aligned document accepted).nodup_iff.mpr
    (all_slice_addresses_unique state part unique anchors)

/-- Every accepted source step from an actual projected state has the guards
needed by the existing same-sequence history simulation. -/
theorem accepted_source_guard (state : State) (part : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (anchors : NotionCoreSliceForest.AnchorsUnique state.forest)
    (aligned : NotionCoreMachineDisplay.Aligned state)
    (document after : NotionCoreSourceDocument.Document)
    (materialized : NotionCoreMachineDocument.materializeDocument state = some document)
    (command : NotionCoreSourceDocument.Command)
    (accepted : NotionCoreSourceDocument.step document command = some after) :
    NotionCoreSourceDocument.Guard document command := by
  have names : (document.map NotionCoreSource.Block.id).Nodup := by
    rw [NotionCoreMachineDocument.materialized_ids state document materialized]
    exact aligned.2.1
  exact NotionCoreSourceGuards.accepted_guard_of_unique command names
    (projected_addresses_unique state part unique anchors aligned document materialized) accepted

/-- At any honest canonical prefix, accepted source transitions satisfy the
independent specification. All projection guards are derived from replay. -/
theorem honest_prefix_source_step (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ suffix)
    (state : State) (replayed : replay {} pre = some state)
    (document after : NotionCoreSourceDocument.Document)
    (materialized : NotionCoreMachineDocument.materializeDocument state = some document)
    (command : NotionCoreSourceDocument.Command)
    (accepted : NotionCoreSourceDocument.step document command = some after) :
    NotionCoreSpec.step (NotionCoreSourceDocument.project document) command.semantic =
      some (NotionCoreSourceDocument.project after) := by
  obtain ⟨checked,checkedReplay,part,shape,_⟩ :=
    NotionCoreMachineHonestReplay.honest_prefix_reconstruct network reachable peer pre suffix position
  have equal : checked = state := Option.some.inj (checkedReplay.symm.trans replayed)
  subst checked
  have unique := NotionCoreMachineMarkerProgress.canonical_physical_unique_all network
    (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))
    peer pre suffix position state replayed
  have aligned := NotionCoreMachineDisplay.replay_aligned {} state pre
    (by simp [NotionCoreMachineDisplay.Aligned,NotionCoreDisplayOrder.Aligned,NotionCoreDisplayOrder.names,
      NotionCoreDisplayOrder.shown]) replayed
  have guard := accepted_source_guard state part unique shape.2.2.2.2 aligned document after materialized
    command accepted
  exact NotionCoreSourceDocument.step_sound command guard.1 guard.2 accepted

#print axioms honest_prefix_source_step

#print axioms accepted_source_guard

#print axioms projected_addresses_unique

#print axioms all_addresses_unique

#print axioms all_slice_addresses_unique
end Sal.MRDTs.Instances.NotionCoreMachineDocumentInvariant
