import Sal.MRDTs.Instances.NotionCoreMachineDocument
import Sal.MRDTs.Instances.NotionCoreSourceGuards
import Sal.MRDTs.Instances.NotionCoreMachineDocumentClient

/-! Projected semantic address uniqueness comes from the all-reference physical
partition. Empty title anchors participate; display order only permutes blocks. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineDocumentInvariant
open NotionCoreMachine
open NotionCoreMachinePartition
open NotionCoreForestRefs (ownedRefs)
open NotionCorePartition (Cell flatten)
open NotionCoreSource (Atom)
open NotionCoreSpec (Address)
open NotionCoreSliceForest (Ref)

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

/-- Within each instance, every owned reference reconstructs exactly one
physical cell; its concatenated addresses permute the actual physical IDs. -/
theorem instance_addresses (state : State) (part : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (inst : Nat) (stored : ∃ entry ∈ state.instances, entry.1 = inst) :
    (((ownedRefs state.forest).filter (fun owned => owned.2.start.1 == inst)).flatMap
      (fun owned => intervalAddresses state owned.2)).Perm ((physical state inst).map Atom.address) := by
  obtain ⟨cells,physicalEq,_,permutation⟩ := part.partitions inst stored
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

private theorem slices_addresses (state : State) (refs : List Ref) (slices : List NotionCoreSource.Slice)
    (accepted : refs.mapM (fun ref => do pure ⟨ref.start,← sliceAtoms state ref⟩) = some slices) :
    (slices.flatMap NotionCoreSource.Slice.slots).map NotionCoreSpec.Slot.address =
      refs.flatMap (intervalAddresses state) := by
  induction refs generalizing slices with
  | nil => simp at accepted; subst slices; rfl
  | cons ref rest ih =>
    cases extracted : sliceAtoms state ref with
    | none => simp [List.mapM_cons,extracted] at accepted
    | some atoms =>
      simp only [List.mapM_cons] at accepted
      obtain ⟨head,headRead,laterRead⟩ := Option.bind_eq_some_iff.mp accepted
      have headEq : head = (⟨ref.start,atoms⟩ : NotionCoreSource.Slice) := by
        simpa [extracted] using headRead.symm
      subst head
      obtain ⟨tail,following,same⟩ := Option.bind_eq_some_iff.mp laterRead
      have equal : (⟨ref.start,atoms⟩ : NotionCoreSource.Slice) :: tail = slices := Option.some.inj same
      subst slices
      have later := ih tail following
      rw [List.flatMap_cons,List.map_append,later,List.flatMap_cons,interval_extracted state ref atoms extracted]
      simp [NotionCoreSource.Slice.slots,NotionCoreSource.Slice.anchor,List.map_map,
        Function.comp_def,NotionCoreSourceDocument.slot_address]

def blockAddresses (state : State) (block : NotionCoreSliceForest.Block) : List Address :=
  (NotionCoreSliceForest.preorderTree block.title).flatMap (intervalAddresses state)

/-- Semantic anchors and retained atoms are exactly all the actual tree's
interval addresses, including the unused title anchor of an attached block. -/
theorem materialized_block_addresses (state : State) (part : Partitioned state)
    (shape : NotionCoreMachineShape.ShapeInvariant state)
    (block : NotionCoreSliceForest.Block) (member : block ∈ state.forest)
    (source : NotionCoreSource.Block)
    (accepted : NotionCoreMachineDocument.materializeBlock state block = some source) :
    source.project.slots.map NotionCoreSpec.Slot.address = blockAddresses state block := by
  have normal := shape.1 block member
  have owned : (block.id,block.title.slice) ∈ ownedRefs state.forest := by
    apply List.mem_flatMap.mpr
    refine ⟨block,member,List.mem_map.mpr ⟨block.title.slice,?_,rfl⟩⟩
    cases block.title
    simp [NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.Tree.slice]
  have rootName : ∀ bid tree, NotionCoreSliceForest.Normal bid tree → tree.slice.start.1 = bid := by
    intro bid tree h
    cases h <;> rfl
  have name : block.title.slice.start.1 = block.id := rootName _ _ normal
  have stored : state.instances.any (fun entry => entry.1 == block.id) = true := by
    simpa [name] using part.refsExist _ owned
  have empty : NotionCoreSliceForest.attached block.title = true →
      physical state block.id = NotionCoreSliceForest.emptyPhysical block.id :=
    fun inactive => shape.2.2 _ (List.mem_map.mpr ⟨block,member,rfl⟩) inactive
  have nodes := NotionCoreMachineDocumentClient.materialized_nodes state block source normal empty (fun _ => stored) accepted
  have addresses := slices_addresses state (NotionCoreSliceForest.preorderTree block.title)
    (NotionCorePreparation.nodes source) nodes
  simpa [NotionCoreMachineDocumentClient.nodes_project_slots,blockAddresses] using addresses

private def lookupAddresses (state : State) (bid : Nat) : List Address :=
  ((state.forest.find? (fun block => block.id == bid)).map (blockAddresses state)).getD []

private theorem named_addresses (state : State) (part : Partitioned state)
    (shape : NotionCoreMachineShape.ShapeInvariant state) (bid : Nat) (source : NotionCoreSource.Block)
    (accepted : (do let block ← state.forest.find? (fun block => block.id == bid)
                    NotionCoreMachineDocument.materializeBlock state block) = some source) :
    source.project.slots.map NotionCoreSpec.Slot.address = lookupAddresses state bid := by
  cases found : state.forest.find? (fun block => block.id == bid) with
  | none => simp [found] at accepted
  | some block =>
    have projected : NotionCoreMachineDocument.materializeBlock state block = some source := by simpa [found] using accepted
    simpa [lookupAddresses,found] using materialized_block_addresses state part shape block
      (List.mem_of_find?_eq_some found) source projected

private theorem projected_addresses (state : State) (part : Partitioned state)
    (shape : NotionCoreMachineShape.ShapeInvariant state) (document : NotionCoreSourceDocument.Document)
    (accepted : NotionCoreMachineDocument.materializeDocument state = some document) :
    NotionCoreInvariant.addresses (NotionCoreSourceDocument.project document) =
      state.display.flatMap (lookupAddresses state) := by
  have sequence : ∀ (ids : List Nat) (doc : NotionCoreSourceDocument.Document),
      ids.mapM (fun bid => do
        let block ← state.forest.find? (fun block => block.id == bid)
        NotionCoreMachineDocument.materializeBlock state block) = some doc →
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
      have headEq := named_addresses state part shape bid source first
      have tailEq := ih tail following
      simpa [NotionCoreInvariant.addresses,NotionCoreSourceDocument.project] using congrArg₂ List.append headEq tailEq
  exact sequence state.display document accepted

/-- The projected global address list permutes the actual forest's complete
physical partition; it is not inferred from visible text alone. -/
theorem projected_addresses_perm (state : State) (part : Partitioned state)
    (shape : NotionCoreMachineShape.ShapeInvariant state) (aligned : NotionCoreMachineDisplay.Aligned state)
    (document : NotionCoreSourceDocument.Document)
    (accepted : NotionCoreMachineDocument.materializeDocument state = some document) :
    (NotionCoreInvariant.addresses (NotionCoreSourceDocument.project document)).Perm
      ((ownedRefs state.forest).flatMap (fun owned => intervalAddresses state owned.2)) := by
  rw [projected_addresses state part shape document accepted]
  have permutation := aligned.2.flatMap_right (lookupAddresses state)
  have exactForest : (state.forest.map NotionCoreSliceForest.Block.id).flatMap (lookupAddresses state) =
      state.forest.flatMap (blockAddresses state) := by
    rw [List.flatMap_map]
    apply List.flatMap_congr
    intro block member
    have found := NotionCoreMachineClient.find_block_member state.forest aligned.1 block member
    simp [lookupAddresses,found]
  change (state.display.flatMap (lookupAddresses state)).Perm
    ((state.forest.map NotionCoreSliceForest.Block.id).flatMap (lookupAddresses state)) at permutation
  rw [exactForest] at permutation
  simpa [ownedRefs,List.flatMap_assoc,blockAddresses,List.flatMap_map,Function.comp_def] using permutation

theorem projected_addresses_unique (state : State) (part : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (shape : NotionCoreMachineShape.ShapeInvariant state) (aligned : NotionCoreMachineDisplay.Aligned state)
    (document : NotionCoreSourceDocument.Document)
    (accepted : NotionCoreMachineDocument.materializeDocument state = some document) :
    (NotionCoreInvariant.addresses (NotionCoreSourceDocument.project document)).Nodup :=
  (projected_addresses_perm state part shape aligned document accepted).nodup_iff.mpr
    (all_addresses_unique state part unique)

/-- Every accepted source step from an actual projected state has the guards
needed by the existing same-sequence history simulation. -/
theorem accepted_source_guard (state : State) (part : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (shape : NotionCoreMachineShape.ShapeInvariant state) (aligned : NotionCoreMachineDisplay.Aligned state)
    (document after : NotionCoreSourceDocument.Document)
    (materialized : NotionCoreMachineDocument.materializeDocument state = some document)
    (command : NotionCoreSourceDocument.Command)
    (accepted : NotionCoreSourceDocument.step document command = some after) :
    NotionCoreSourceDocument.Guard document command := by
  have names : (document.map NotionCoreSource.Block.id).Nodup := by
    rw [NotionCoreMachineDocument.materialized_ids state document materialized]
    exact aligned.2.nodup_iff.mpr aligned.1
  exact NotionCoreSourceGuards.accepted_guard_of_unique command names
    (projected_addresses_unique state part unique shape aligned document materialized) accepted

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
    (by simp [NotionCoreMachineDisplay.Aligned,NotionCoreDisplayOrder.Aligned,NotionCoreDisplayOrder.names]) replayed
  have guard := accepted_source_guard state part unique shape aligned document after materialized command accepted
  exact NotionCoreSourceDocument.step_sound command guard.1 guard.2 accepted

#print axioms honest_prefix_source_step

#print axioms accepted_source_guard

#print axioms projected_addresses_unique

#print axioms all_addresses_unique
end Sal.MRDTs.Instances.NotionCoreMachineDocumentInvariant
