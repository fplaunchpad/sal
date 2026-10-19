import Sal.MRDTs.Instances.NotionCoreMachineDocument
import Sal.MRDTs.Instances.NotionCoreMachineDocumentInvariant
import Sal.MRDTs.Instances.NotionCoreMachineFreshText
import Sal.MRDTs.Instances.NotionCoreMachinePartitionUpdates
import Sal.MRDTs.Instances.NotionCoreMachineHonestReplay

/-! Checked materialization under the actual physical insertion splice. The
interval factorization is the old partition witness; no next extraction or
materialized output is a premise. Fresh atoms may include a split marker.
Every slice of every chain is extracted after the splice; exactly the slice
holding the origin changes. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineDocumentInsert
open NotionCoreSpec (Address)
open NotionCoreSource (Atom)
open NotionCorePartition (Cell flatten insertCell)
open NotionCoreMachine

/-- Source insertion into a represented interval is obtained by checked
extraction after the global physical splice, including hidden origins. -/
theorem sliceAtoms_splice (state next : State) (before after : List Cell)
    (cell : Cell) (origin : Address) (fresh : List Atom)
    (oldPhysical : physical state cell.slice.start.1 = flatten (before ++ cell :: after))
    (oldUnique : ((physical state cell.slice.start.1).map Atom.address).Nodup)
    (present : origin ∈ cell.physical.map Atom.address)
    (changed : physical next cell.slice.start.1 =
      NotionCorePartition.spliceAfterBy Atom.address origin fresh
        (physical state cell.slice.start.1))
    (nextExists : next.instances.any (fun entry => entry.1 == cell.slice.start.1) = true)
    (nextUnique : ((physical next cell.slice.start.1).map Atom.address).Nodup) :
    sliceAtoms next ⟨cell.slice.start, after.head?.map (fun following => following.slice.start)⟩ =
      some (NotionCoreSource.insertSlice cell.slice
        (cell.slice.traversal.idxOf origin) fresh).atoms := by
  have updated : physical next cell.slice.start.1 =
      flatten (before ++ insertCell cell origin fresh :: after) := by
    rw [changed, oldPhysical]
    exact NotionCorePartition.insert_physical before after cell origin fresh
      (by simpa [oldPhysical] using oldUnique) present
  exact NotionCoreMachineSlices.sliceAtoms_cell next before after
    (insertCell cell origin fresh) nextExists updated nextUnique

def updateCell (origin : Address) (fresh : List Atom) (cell : Cell) : Cell :=
  if origin ∈ cell.physical.map Atom.address then insertCell cell origin fresh else cell

@[simp] theorem updateCell_start (origin : Address) (fresh : List Atom) (cell : Cell) :
    (updateCell origin fresh cell).slice.start = cell.slice.start := by
  unfold updateCell
  split <;> rfl

/-- The splice updates exactly the cell owning its origin, so endpoint
factorizations for all other cells remain available without a frame premise.
Physical address uniqueness alone excludes a second owning cell. -/
theorem updateCells_focus (before after : List Cell) (cell : Cell)
    (origin : Address) (fresh : List Atom)
    (unique : ((flatten (before ++ cell :: after)).map Atom.address).Nodup)
    (present : origin ∈ cell.physical.map Atom.address) :
    (before ++ cell :: after).map (updateCell origin fresh) =
      before ++ insertCell cell origin fresh :: after := by
  have whole : ((flatten before).map Atom.address ++
      (cell.physical.map Atom.address ++ (flatten after).map Atom.address)).Nodup := by
    simpa [flatten, List.flatMap_append] using unique
  obtain ⟨_, rest, apart⟩ := List.nodup_append.mp whole
  obtain ⟨_, _, apartAfter⟩ := List.nodup_append.mp rest
  have heldIn : ∀ other ∈ before ++ after, origin ∈ other.physical.map Atom.address →
      origin ∈ (flatten (before ++ after)).map Atom.address := by
    intro other member held
    obtain ⟨atom, inside, rfl⟩ := List.mem_map.mp held
    exact List.mem_map.mpr ⟨atom, List.mem_flatMap.mpr ⟨other, member, inside⟩, rfl⟩
  have excluded : ∀ other ∈ before ++ after, origin ∉ other.physical.map Atom.address := by
    intro other member held
    have elsewhere := heldIn other member held
    simp only [flatten, List.flatMap_append, List.map_append, List.mem_append] at elsewhere
    rcases elsewhere with inBefore | inAfter
    · exact apart origin inBefore origin (List.mem_append_left _ present) rfl
    · exact apartAfter origin present origin inAfter rfl
  have left : before.map (updateCell origin fresh) = before := by
    conv_rhs => rw [← List.map_id before]
    apply List.map_congr_left
    intro other member
    simp [updateCell, excluded other (List.mem_append_left _ member)]
  have right : after.map (updateCell origin fresh) = after := by
    conv_rhs => rw [← List.map_id after]
    apply List.map_congr_left
    intro other member
    simp [updateCell, excluded other (List.mem_append_right _ member)]
  simp [List.map_append, left, right, updateCell, present]

/-- Every old interval extracts its cellwise update after the splice. This
includes same-instance intervals on either side of the insertion. -/
theorem sliceAtoms_updated_cells (next : State) (before after : List Cell)
    (cell : Cell) (origin : Address) (fresh : List Atom)
    (physicalEq : physical next cell.slice.start.1 =
      flatten ((before ++ cell :: after).map (updateCell origin fresh)))
    (existsInstance : next.instances.any (fun entry => entry.1 == cell.slice.start.1) = true)
    (unique : ((physical next cell.slice.start.1).map Atom.address).Nodup) :
    sliceAtoms next ⟨cell.slice.start, after.head?.map (fun following => following.slice.start)⟩ =
      some (updateCell origin fresh cell).slice.atoms := by
  have extracted := NotionCoreMachineSlices.sliceAtoms_cell next
    (before.map (updateCell origin fresh)) (after.map (updateCell origin fresh))
    (updateCell origin fresh cell) (by simpa using existsInstance)
    (by simpa only [List.map_append,List.map_cons,updateCell_start] using physicalEq)
    (by simpa using unique)
  have ending : (after.map (updateCell origin fresh)).head?.map
      (fun following => following.slice.start) =
      after.head?.map (fun following => following.slice.start) := by
    cases after <;> simp
  simpa only [updateCell_start, ending] using extracted

/-- Whole-instance cell ownership determines each stored reference's result;
no selected source block or next materialization is supplied. -/
theorem ownedRef_splice (state next : State)
    (partitioned : NotionCoreMachinePartition.Partitioned state)
    (owned : Nat × NotionCoreSliceForest.Ref)
    (member : owned ∈ NotionCoreForestRefs.ownedRefs state.forest)
    (origin : Address) (fresh : List Atom)
    (oldUnique : ((physical state owned.2.start.1).map Atom.address).Nodup)
    (present : origin ∈ (physical state owned.2.start.1).map Atom.address)
    (changed : physical next owned.2.start.1 =
      NotionCorePartition.spliceAfterBy Atom.address origin fresh (physical state owned.2.start.1))
    (nextExists : next.instances.any (fun entry => entry.1 == owned.2.start.1) = true)
    (nextUnique : ((physical next owned.2.start.1).map Atom.address).Nodup) :
    ∃ slice : NotionCoreSource.Slice,
      slice.start = owned.2.start ∧ slice.stop = owned.2.stop ∧
      sliceAtoms state owned.2 = some slice.atoms ∧
      sliceAtoms next owned.2 = some
        (if origin ∈ slice.traversal then
          (NotionCoreSource.insertSlice slice (slice.traversal.idxOf origin) fresh).atoms
         else slice.atoms) := by
  obtain ⟨cells, phys, permutation⟩ := partitioned.partitions owned.2.start.1
    (partitioned.refsExist owned member)
  have representation : NotionCorePartition.Represents
      ⟨physical state owned.2.start.1,cells.map Cell.entry⟩ cells := ⟨phys,rfl,oldUnique⟩
  obtain ⟨selected,⟨selectedMember,selectedOwns⟩,_⟩ :=
    NotionCorePartition.physical_unique_owner origin representation present
  obtain ⟨left,right,focus⟩ := List.append_of_mem selectedMember
  have mapped : physical next owned.2.start.1 = flatten (cells.map (updateCell origin fresh)) := by
    rw [changed,phys,focus,updateCells_focus left right selected origin fresh
      (by simpa [← focus,← phys] using oldUnique) selectedOwns]
    exact NotionCorePartition.insert_physical left right selected origin fresh
      (by simpa [← focus,← phys] using oldUnique) selectedOwns
  have refMember := permutation.mem_iff.mp (List.mem_filter.mpr ⟨member,by simp⟩)
  obtain ⟨before,cell,after,shape,equal⟩ :=
    (NotionCoreMachinePartition.cellRefs_member cells owned).mp refMember
  have oldExists : state.instances.any (fun entry => entry.1 == owned.2.start.1) = true := by
    simpa using partitioned.refsExist owned member
  have position := NotionCoreMachineDocumentInvariant.physical_positions state _ origin present
  subst owned
  let slice : NotionCoreSource.Slice :=
    ⟨cell.slice.start, cell.slice.atoms, after.head?.map (fun following => following.slice.start)⟩
  refine ⟨slice,rfl,rfl,?_,?_⟩
  · exact NotionCoreMachineSlices.sliceAtoms_cell state before after cell oldExists
      (shape ▸ phys) oldUnique
  · have result := sliceAtoms_updated_cells next before after cell origin fresh
      (shape ▸ mapped) nextExists nextUnique
    by_cases owns : origin ∈ cell.physical.map Atom.address
    · have held : origin ∈ slice.traversal := (NotionCorePartition.slice_traversal_iff position).mpr owns
      rw [if_pos held]
      simp only [updateCell, owns, if_true, insertCell] at result
      have index : slice.traversal.idxOf origin = (cell.physical.map Atom.address).idxOf origin :=
        NotionCorePartition.slice_traversal_idxOf (slice := slice) owns
      rw [result, index]
      simp only [NotionCoreSource.insertSlice, slice, NotionCorePartition.traversal_idxOf owns]
    · have absent : origin ∉ slice.traversal := fun held =>
        owns ((NotionCorePartition.slice_traversal_iff (slice := slice) position).mp held)
      rw [if_neg absent]
      simpa [updateCell, owns] using result

/-- Each extracted slice of a stored chain changes by the source insertion
exactly when it holds the origin, including slices of other instances. -/
theorem sliceAtoms_insert (state next : State)
    (partitioned : NotionCoreMachinePartition.Partitioned state)
    (owned : Nat × NotionCoreSliceForest.Ref)
    (member : owned ∈ NotionCoreForestRefs.ownedRefs state.forest)
    (atoms : List Atom) (extracted : sliceAtoms state owned.2 = some atoms)
    (inst : Nat) (origin : Address) (fresh : List Atom) (originInst : origin.1 = inst)
    (unique : ∀ key, ((physical state key).map Atom.address).Nodup)
    (nextUnique : ∀ key, ((physical next key).map Atom.address).Nodup)
    (nextExists : ∀ key, state.instances.any (fun entry => entry.1 == key) = true →
      next.instances.any (fun entry => entry.1 == key) = true)
    (present : origin ∈ (physical state inst).map Atom.address)
    (changed : physical next inst = NotionCorePartition.spliceAfterBy Atom.address origin fresh (physical state inst))
    (frames : ∀ key, key ≠ inst → physical next key = physical state key) :
    let slice : NotionCoreSource.Slice := ⟨owned.2.start,atoms,owned.2.stop⟩
    sliceAtoms next owned.2 = some
      (if origin ∈ slice.traversal then
        NotionCoreSource.insertSlice slice (slice.traversal.idxOf origin) fresh else slice).atoms := by
  intro slice
  have oldExists : state.instances.any (fun entry => entry.1 == owned.2.start.1) = true := by
    simpa using partitioned.refsExist _ member
  by_cases same : owned.2.start.1 = inst
  · obtain ⟨found,startEq,stopEq,prior,updated⟩ := ownedRef_splice state next partitioned
      owned member origin fresh (unique _) (same ▸ present)
      (same ▸ changed) (nextExists _ oldExists) (nextUnique _)
    have atomsEq : found.atoms = atoms := Option.some.inj (prior.symm.trans extracted)
    have sliceEq : found = slice := by
      cases found; simp_all [slice]
    subst found
    rw [updated]
    split <;> rfl
  · have physicalFrame := frames owned.2.start.1 same
    have nextSelected : sliceAtoms next owned.2 = some atoms := by
      simpa only [sliceAtoms,physicalFrame,nextExists _ oldExists,oldExists] using extracted
    have originAbsent : origin ∉ slice.traversal := by
      intro held
      have sameInst := NotionCoreSource.traversal_instance slice origin
        (NotionCoreMachineClient.slice_storage state owned.2 atoms extracted).2 held
      exact same (sameInst.symm.trans originInst)
    rw [nextSelected, if_neg originAbsent]

private theorem mapM_transform {α β : Type} (xs : List α) (f g : α → Option β) (h : β → β)
    (transform : ∀ x ∈ xs, ∀ value, f x = some value → g x = some (h value))
    (ys : List β) (before : xs.mapM f = some ys) : xs.mapM g = some (ys.map h) := by
  induction xs generalizing ys with
  | nil => simp at before; subst ys; rfl
  | cons head rest ih =>
    cases first : f head with
    | none => simp [List.mapM_cons,first] at before
    | some value =>
      cases later : rest.mapM f with
      | none => simp [List.mapM_cons,first,later] at before
      | some tail =>
        have equal : value :: tail = ys := by simpa [List.mapM_cons,first,later] using before
        subst ys
        have next := transform head (by simp) value first
        have following := ih (fun x member => transform x (List.mem_cons_of_mem _ member)) tail later
        simp [List.mapM_cons,next,following]

/-- Per-block materialization commuting, including slices of other physical
instances. The supplied source is only the old materialization. -/
theorem materializeBlock_insert (state next : State)
    (partitioned : NotionCoreMachinePartition.Partitioned state)
    (block : NotionCoreSliceForest.Block) (source : NotionCoreSource.Block)
    (member : block ∈ state.forest)
    (old : NotionCoreMachineDocument.materializeBlock state block = some source)
    (inst : Nat) (origin : Address) (fresh : List Atom) (originInst : origin.1 = inst)
    (unique : ∀ key, ((physical state key).map Atom.address).Nodup)
    (nextUnique : ∀ key, ((physical next key).map Atom.address).Nodup)
    (nextExists : ∀ key, state.instances.any (fun entry => entry.1 == key) = true →
      next.instances.any (fun entry => entry.1 == key) = true)
    (present : origin ∈ (physical state inst).map Atom.address)
    (changed : physical next inst = NotionCorePartition.spliceAfterBy Atom.address origin fresh (physical state inst))
    (frames : ∀ key, key ≠ inst → physical next key = physical state key) :
    NotionCoreMachineDocument.materializeBlock next block = some
      (if NotionCoreSourceDocument.owns source origin then
        NotionCoreSourceDocument.insertBlock source origin fresh else source) := by
  obtain ⟨extracted,name,instEq⟩ := NotionCoreMachineDocument.materialized_slices state block source old
  have after : NotionCoreMachineClient.materialize next block.title = some
      (NotionCoreSource.insertSlices origin fresh source.slices) := by
    unfold NotionCoreMachineClient.materialize at extracted ⊢
    apply mapM_transform _ _ _ _ ?_ _ extracted
    intro ref inTree slice selected
    cases atoms : sliceAtoms state ref with
    | none => simp [atoms] at selected
    | some found =>
      have sliceEq : slice = ⟨ref.start,found,ref.stop⟩ := by simpa [atoms] using selected.symm
      subst slice
      have owned : (block.id,ref) ∈ NotionCoreForestRefs.ownedRefs state.forest :=
        List.mem_flatMap.mpr ⟨block,member,List.mem_map.mpr ⟨ref,inTree,rfl⟩⟩
      have updated := sliceAtoms_insert state next partitioned (block.id,ref) owned found atoms
        inst origin fresh originInst unique nextUnique nextExists present changed frames
      simp only at updated
      simp only [updated, pure]
      split <;> rfl
  have result : NotionCoreMachineDocument.materializeBlock next block =
      some (NotionCoreSourceDocument.insertBlock source origin fresh) := by
    cases source
    simp only at name instEq
    subst name instEq
    simp [NotionCoreMachineDocument.materializeBlock,after,NotionCoreSourceDocument.insertBlock]
  rw [result]
  split
  · rfl
  · rename_i absent
    congr 1
    cases source with
    | mk id inst slices =>
      simp only [NotionCoreSourceDocument.insertBlock, NotionCoreSource.Block.mk.injEq, true_and]
      conv_rhs => rw [← List.map_id slices]
      apply List.map_congr_left
      intro slice inside
      have outside : origin ∉ slice.traversal := by
        intro held
        apply absent
        simpa [NotionCoreSourceDocument.owns, NotionCoreSource.Block.traversal] using
          ⟨slice, inside, held⟩
      simp [outside]

/-- Actual display-ordered materialization follows the existing source
insertion map. The unchanged display and forest are operational frames. -/
theorem materializeDocument_insert (state next : State)
    (partitioned : NotionCoreMachinePartition.Partitioned state)
    (document : NotionCoreSourceDocument.Document)
    (old : NotionCoreMachineDocument.materializeDocument state = some document)
    (inst : Nat) (origin : Address) (fresh : List Atom) (originInst : origin.1 = inst)
    (unique : ∀ key, ((physical state key).map Atom.address).Nodup)
    (nextUnique : ∀ key, ((physical next key).map Atom.address).Nodup)
    (nextExists : ∀ key, state.instances.any (fun entry => entry.1 == key) = true →
      next.instances.any (fun entry => entry.1 == key) = true)
    (present : origin ∈ (physical state inst).map Atom.address)
    (changed : physical next inst = NotionCorePartition.spliceAfterBy Atom.address origin fresh (physical state inst))
    (frames : ∀ key, key ≠ inst → physical next key = physical state key)
    (forestFrame : next.forest = state.forest) (displayFrame : next.display = state.display) :
    NotionCoreMachineDocument.materializeDocument next = some
      (document.map (fun source => if NotionCoreSourceDocument.owns source origin then
        NotionCoreSourceDocument.insertBlock source origin fresh else source)) := by
  unfold NotionCoreMachineDocument.materializeDocument at old ⊢
  rw [displayFrame]
  apply mapM_transform state.display _ _ _ ?_ document old
  intro bid _ source extracted
  cases found : state.forest.find? (fun old => old.id == bid) with
  | none =>
    rw [NotionCoreMachineDocument.materializeEntry_tombstone state bid found] at extracted
    cases extracted
    rw [NotionCoreMachineDocument.materializeEntry_tombstone next bid (by rw [forestFrame]; exact found)]
    simp [NotionCoreSourceDocument.owns, NotionCoreSource.Block.traversal]
  | some block =>
    rw [NotionCoreMachineDocument.materializeEntry_stored state bid block found] at extracted
    rw [NotionCoreMachineDocument.materializeEntry_stored next bid block (by rw [forestFrame]; exact found)]
    exact materializeBlock_insert state next partitioned block source (List.mem_of_find?_eq_some found)
      extracted inst origin fresh originInst unique nextUnique nextExists present changed frames

/-- An available source origin makes the derived materialization map the
literal independent document transition. Origin availability is explicit;
this low-level interface does not assume a next document equation. -/
theorem insert_source_step (state next : State)
    (partitioned : NotionCoreMachinePartition.Partitioned state)
    (document : NotionCoreSourceDocument.Document)
    (old : NotionCoreMachineDocument.materializeDocument state = some document)
    (inst : Nat) (origin : Address) (fresh : List Atom) (originInst : origin.1 = inst)
    (unique : ∀ key, ((physical state key).map Atom.address).Nodup)
    (nextUnique : ∀ key, ((physical next key).map Atom.address).Nodup)
    (nextExists : ∀ key, state.instances.any (fun entry => entry.1 == key) = true →
      next.instances.any (fun entry => entry.1 == key) = true)
    (present : origin ∈ (physical state inst).map Atom.address)
    (changed : physical next inst = NotionCorePartition.spliceAfterBy Atom.address origin fresh (physical state inst))
    (frames : ∀ key, key ≠ inst → physical next key = physical state key)
    (forestFrame : next.forest = state.forest) (displayFrame : next.display = state.display)
    (available : ∃ source ∈ document, NotionCoreSourceDocument.owns source origin = true) :
    ∃ after, NotionCoreMachineDocument.materializeDocument next = some after ∧
      NotionCoreSourceDocument.step document (.insert origin fresh) = some after := by
  refine ⟨_,materializeDocument_insert state next partitioned document old inst origin fresh
    originInst unique nextUnique nextExists present changed frames forestFrame displayFrame,?_⟩
  have position := NotionCoreMachineDocumentInvariant.physical_positions state inst origin present
  cases ownerEq : NotionCoreSourceDocument.owner document origin with
  | none =>
    obtain ⟨source,member,owns⟩ := available
    have rejected := List.find?_eq_none.mp ownerEq source member
    exact False.elim (rejected owns)
  | some source => simp [NotionCoreSourceDocument.step,ownerEq,position]

/-- A located reference in an active instance is a live node of its chain:
dead title roots have instances that no live node shares. -/
theorem located_ref_live (state : State)
    (shape : NotionCoreMachineShape.ShapeInvariant state) (inst : Nat)
    (activeInst : NotionCoreMachineShape.ActiveInstance state inst)
    (ref : NotionCoreSliceForest.Ref) (tag : Bool)
    (member : (ref,tag) ∈ NotionCoreSliceForest.forestNodes state.forest)
    (same : ref.start.1 = inst) : tag = true := by
  cases tag with
  | true => rfl
  | false =>
    obtain ⟨live,liveMember,liveInst⟩ := activeInst
    obtain ⟨_,_,apart⟩ := shape.2.2.1 ref member
    exact absurd (liveInst.trans same.symm) (apart live liveMember)

#print axioms located_ref_live
private theorem stored_find (forest : NotionCoreSliceForest.Forest)
    (unique : (forest.map NotionCoreSliceForest.Block.id).Nodup)
    (block : NotionCoreSliceForest.Block) (member : block ∈ forest) :
    forest.find? (fun old => old.id == block.id) = some block := by
  induction forest with
  | nil => simp at member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simp
    · have distinct : head.id ≠ block.id := by
        intro same
        exact (List.nodup_cons.mp unique).1 (List.mem_map.mpr ⟨block,member,same.symm⟩)
      simpa [distinct] using ih (List.nodup_cons.mp unique).2 member

private theorem mapM_member_input {α β : Type} (f : α → Option β)
    (xs : List α) (ys : List β) (accepted : xs.mapM f = some ys)
    (x : α) (member : x ∈ xs) : ∃ y ∈ ys, f x = some y := by
  induction xs generalizing ys with
  | nil => simp at member
  | cons head rest ih =>
    cases first : f head with
    | none => simp [List.mapM_cons,first] at accepted
    | some value =>
      cases later : rest.mapM f with
      | none => simp [List.mapM_cons,first,later] at accepted
      | some tail =>
        have equal : value :: tail = ys := by simpa [List.mapM_cons,first,later] using accepted
        subst ys
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨value,by simp,first⟩
        · obtain ⟨y,member,eq⟩ := ih tail later member
          exact ⟨y,List.mem_cons_of_mem _ member,eq⟩

/-- Every physical origin of a stored instance is owned by a materialized
source block: the partition places it in an interval of some stored chain. -/
theorem materialized_origin_available (state : State)
    (partitioned : NotionCoreMachinePartition.Partitioned state)
    (aligned : NotionCoreMachineDisplay.Aligned state)
    (unique : ∀ key, ((physical state key).map Atom.address).Nodup)
    (document : NotionCoreSourceDocument.Document)
    (old : NotionCoreMachineDocument.materializeDocument state = some document)
    (inst : Nat) (existsInstance : ∃ entry ∈ state.instances, entry.1 = inst)
    (origin : Address) (present : origin ∈ (physical state inst).map Atom.address) :
    ∃ source ∈ document, NotionCoreSourceDocument.owns source origin = true := by
  obtain ⟨cells,phys,permutation⟩ := partitioned.partitions inst existsInstance
  have representation : NotionCorePartition.Represents
      ⟨physical state inst,cells.map Cell.entry⟩ cells := ⟨phys,rfl,unique _⟩
  obtain ⟨cell,⟨cellMember,owns⟩,_⟩ :=
    NotionCorePartition.physical_unique_owner origin representation present
  obtain ⟨before,after,focus⟩ := List.append_of_mem cellMember
  let owned : Nat × NotionCoreSliceForest.Ref :=
    (cell.owner,⟨cell.slice.start,after.head?.map (fun following => following.slice.start)⟩)
  have ownedCells : owned ∈ NotionCoreMachinePartition.cellRefs cells :=
    (NotionCoreMachinePartition.cellRefs_member cells owned).mpr ⟨before,cell,after,focus,rfl⟩
  have ownedFilter := List.mem_filter.mp (permutation.mem_iff.mpr ownedCells)
  have same : owned.2.start.1 = inst := by simpa using ownedFilter.2
  obtain ⟨block,member,refMapped⟩ := List.mem_flatMap.mp ownedFilter.1
  obtain ⟨ref,inTree,refEq⟩ := List.mem_map.mp refMapped
  have displayed : block.id ∈ state.display :=
    ((NotionCoreDisplayOrder.shown_member _ _).mp
      (aligned.2.2.mem_iff.mpr (List.mem_map.mpr ⟨block,member,rfl⟩))).1
  obtain ⟨source,sourceMember,lookup⟩ := mapM_member_input _ state.display document old block.id displayed
  have found := stored_find state.forest aligned.1 block member
  rw [NotionCoreMachineDocument.materializeEntry_stored state block.id block found] at lookup
  obtain ⟨extracted,_,_⟩ := NotionCoreMachineDocument.materialized_slices state block source lookup
  have cellInst : cell.slice.start.1 = inst := same
  have refAtoms := NotionCoreMachineSlices.sliceAtoms_cell state before after cell
    (by simpa [cellInst] using existsInstance) (by simpa only [cellInst,focus] using phys)
    (by simpa only [cellInst] using unique inst)
  have refIs : ref = owned.2 := congrArg Prod.snd refEq
  obtain ⟨slice,sliceMember,sliceRead⟩ := mapM_member_input _ _ _ extracted ref inTree
  rw [refIs, refAtoms] at sliceRead
  have sliceEq : slice = ⟨cell.slice.start,cell.slice.atoms,owned.2.stop⟩ := by
    simp at sliceRead
    rw [← sliceRead]
  subst slice
  have position := NotionCoreMachineDocumentInvariant.physical_positions state inst origin present
  have held : origin ∈ (⟨cell.slice.start,cell.slice.atoms,owned.2.stop⟩ : NotionCoreSource.Slice).traversal :=
    (NotionCorePartition.slice_traversal_iff position).mpr owns
  refine ⟨source,sourceMember,?_⟩
  simpa [NotionCoreSourceDocument.owns, NotionCoreSource.Block.traversal] using ⟨_,sliceMember,held⟩

#print axioms materialized_origin_available
private theorem replay_append (state : State) (a b : List NotionCorePayload.Transaction) :
    replay state (a ++ b) = (replay state a >>= fun next => replay next b) := by
  induction a generalizing state with
  | nil => rfl
  | cons tx rest ih =>
    simp only [List.cons_append,replay]
    cases step : applyTransaction state tx <;> simp [ih]

/-- Honest canonical insertion executes and simulates the independent source
insert with statically live fresh text. All freshness, physical/spatial frames,
active-origin availability and next uniqueness are derived. -/
theorem canonical_insert_source_step_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closedVersion : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (document : NotionCoreSourceDocument.Document)
    (old : NotionCoreMachineDocument.materializeDocument state = some document)
    (block inst : NotionCorePayload.BlockKey) (origin : NotionCoreOriginTree.Origin) (atoms : List Nat)
    (payload : tx.payload = .insert block inst origin atoms) :
    ∃ next after, applyTransaction state tx = some next ∧
      NotionCoreMachineDocument.materializeDocument next = some after ∧
      NotionCoreSourceDocument.step document (.insert
        (NotionCorePhysicalReplay.originAddress (blockName inst) origin)
        ((NotionCorePayload.textItems tx.id atoms (fun _ => false)).map
          (NotionCorePhysicalReplay.atom (blockName inst)))) = some after := by
  have creators := NotionCoreMachineNetwork.creator_reachable reachable
  have networkReach := NotionCoreCreatorNetwork.payload_reachable creators
  obtain ⟨checked,checkedReplay,part,_,_⟩ :=
    NotionCoreMachineHonestReplay.honest_prefix_reconstruct_version network reachable version closedVersion pre (tx :: suffix) position
  have stateEq : checked = state := Option.some.inj (checkedReplay.symm.trans accepted)
  subst checked
  have nonempty := NotionCoreMachineRootReplay.canonical_insert_nonempty_version network creators version tx
    (position ▸ List.mem_append_right pre (by simp)) block inst origin atoms payload
  obtain ⟨next,operation,changed⟩ := NotionCoreMachineCanonicalForest.canonical_insert_physical_version
    network networkReach version closedVersion pre suffix tx position state accepted block inst origin atoms payload nonempty
  have transaction : applyTransaction state tx = some next := by
    simp [applyTransaction,NotionCorePayload.operations,payload,applyOperations,operation]
  have nextEq : ∃ rows, next = putInstance state (blockName inst)
      {getInstance state (blockName inst) with rows := rows} := by
    cases integrated : integrateRows (getInstance state (blockName inst)).rows
        (NotionCoreParentMap.runRows origin (NotionCorePayload.textItems tx.id atoms
          (fun id => decide (id ∈ (getInstance state (blockName inst)).pending)))) with
    | none => simp [applyOperation,integrated] at operation
    | some rows => exact ⟨rows,by simpa [applyOperation,integrated] using operation.symm⟩
  obtain ⟨rows,nextEq⟩ := nextEq
  have stored := NotionCoreMachineCreatorPresence.canonical_required_instance_version network creators
    version closedVersion pre suffix tx position state accepted inst (by simp [payload,NotionCoreCreatorNetwork.requiredBlocks])
  have nextReplay : replay {} (pre ++ [tx]) = some next := by
    rw [replay_append,accepted]
    simp [replay,transaction]
  have nextPosition : NotionCoreReconstruction.transactionsFor network version = (pre ++ [tx]) ++ suffix := by
    simpa [List.append_assoc] using position
  have unique := NotionCoreMachineVersionTables.version_physical_unique_all network networkReach
    version closedVersion pre (tx :: suffix) position state accepted
  have nextUnique := NotionCoreMachineVersionTables.version_physical_unique_all network networkReach
    version closedVersion (pre ++ [tx]) suffix nextPosition next nextReplay
  have present := NotionCoreMachineCanonicalForest.canonical_insert_origin_present_version network networkReach
    version closedVersion pre suffix tx position state accepted block inst origin atoms payload
  have static := NotionCoreMachineFreshText.version_textItems_pending_false network networkReach
    version pre suffix tx position state accepted inst atoms
  rw [static] at changed
  have aligned := NotionCoreMachineDisplay.replay_aligned {} state pre
    (by simp [NotionCoreMachineDisplay.Aligned,NotionCoreDisplayOrder.Aligned,NotionCoreDisplayOrder.names,
      NotionCoreDisplayOrder.shown]) accepted
  have available := materialized_origin_available state part aligned unique document old
    (blockName inst) stored _ present
  obtain ⟨after,materialized,sourceStep⟩ := insert_source_step state next part document old
    (blockName inst) (NotionCorePhysicalReplay.originAddress (blockName inst) origin)
    ((NotionCorePayload.textItems tx.id atoms (fun _ => false)).map
      (NotionCorePhysicalReplay.atom (blockName inst)))
    (by cases origin <;> rfl) unique nextUnique (by
      intro key oldExists
      rw [nextEq]
      have storedKey : ∃ entry ∈ state.instances, entry.1 = key := by simpa using oldExists
      have result := (NotionCoreMachinePartitionUpdates.putInstance_exists_iff state (blockName inst)
        key {getInstance state (blockName inst) with rows := rows} stored).mpr storedKey
      simpa using result) present changed (by
        intro key distinct
        rw [nextEq]
        simp [physical,NotionCoreMachineTables.getInstance_put,distinct])
    (by rw [nextEq]; unfold putInstance; split <;> rfl)
    (by rw [nextEq]; unfold putInstance; split <;> rfl) available
  exact ⟨next,after,transaction,materialized,sourceStep⟩

/-- Canonical insertion supplies a guarded atomic source-history update;
origin safety and block uniqueness follow from the actual old projection. -/
theorem canonical_insert_execution_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closedVersion : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : State) (replayed : replay {} pre = some state)
    (document : NotionCoreSourceDocument.Document)
    (materialized : NotionCoreMachineDocument.materializeDocument state = some document)
    (block inst : NotionCorePayload.BlockKey) (origin : NotionCoreOriginTree.Origin) (atoms : List Nat)
    (payload : tx.payload = .insert block inst origin atoms) :
    ∃ result after, applyTransaction state tx = some result ∧
      NotionCoreMachineDocument.materializeDocument result = some after ∧
      NotionCoreSourceDocument.Execution document
        [.insert (NotionCorePhysicalReplay.originAddress (blockName inst) origin)
          ((NotionCorePayload.textItems tx.id atoms (fun _ => false)).map
            (NotionCorePhysicalReplay.atom (blockName inst)))] after := by
  obtain ⟨result,after,transaction,projected,stepped⟩ := canonical_insert_source_step_version
    network reachable version closedVersion pre suffix tx position state replayed document materialized block inst origin atoms payload
  obtain ⟨checked,checkedReplay,part,shape,_⟩ :=
    NotionCoreMachineHonestReplay.honest_prefix_reconstruct_version network reachable version closedVersion pre (tx :: suffix) position
  have equal : checked = state := Option.some.inj (checkedReplay.symm.trans replayed)
  subst checked
  have unique := NotionCoreMachineVersionTables.version_physical_unique_all network
    (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))
    version closedVersion pre (tx :: suffix) position state replayed
  have aligned := NotionCoreMachineDisplay.replay_aligned {} state pre
    (by simp [NotionCoreMachineDisplay.Aligned,NotionCoreDisplayOrder.Aligned,NotionCoreDisplayOrder.names,
      NotionCoreDisplayOrder.shown]) replayed
  have guard := NotionCoreMachineDocumentInvariant.accepted_source_guard state part unique
    shape.2.2.2.2 aligned document after materialized _ stepped
  exact ⟨result,after,transaction,projected,.cons guard stepped (.nil after)⟩

theorem canonical_insert_execution (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (replayed : replay {} pre = some state)
    (document : NotionCoreSourceDocument.Document)
    (materialized : NotionCoreMachineDocument.materializeDocument state = some document)
    (block inst : NotionCorePayload.BlockKey) (origin : NotionCoreOriginTree.Origin) (atoms : List Nat)
    (payload : tx.payload = .insert block inst origin atoms) :
    ∃ result after, applyTransaction state tx = some result ∧
      NotionCoreMachineDocument.materializeDocument result = some after ∧
      NotionCoreSourceDocument.Execution document
        [.insert (NotionCorePhysicalReplay.originAddress (blockName inst) origin)
          ((NotionCorePayload.textItems tx.id atoms (fun _ => false)).map
            (NotionCorePhysicalReplay.atom (blockName inst)))] after :=
  canonical_insert_execution_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed
      (NotionCorePayloadNetwork.forget_reachable
        (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))) peer)
    pre suffix tx position state replayed document materialized block inst origin atoms payload

#print axioms canonical_insert_execution_version
#print axioms canonical_insert_source_step_version
#print axioms canonical_insert_execution

theorem canonical_insert_source_step (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (document : NotionCoreSourceDocument.Document)
    (old : NotionCoreMachineDocument.materializeDocument state = some document)
    (block inst : NotionCorePayload.BlockKey) (origin : NotionCoreOriginTree.Origin) (atoms : List Nat)
    (payload : tx.payload = .insert block inst origin atoms) :
    ∃ next after, applyTransaction state tx = some next ∧
      NotionCoreMachineDocument.materializeDocument next = some after ∧
      NotionCoreSourceDocument.step document (.insert
        (NotionCorePhysicalReplay.originAddress (blockName inst) origin)
        ((NotionCorePayload.textItems tx.id atoms (fun _ => false)).map
          (NotionCorePhysicalReplay.atom (blockName inst)))) = some after :=
  canonical_insert_source_step_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed
      (NotionCorePayloadNetwork.forget_reachable
        (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))) peer)
    pre suffix tx position state accepted document old block inst origin atoms payload

#print axioms canonical_insert_source_step
namespace SPOT
private def first : NotionRunAllocation.Id := ⟨1,[65]⟩
private def second : NotionRunAllocation.Id := ⟨2,[65]⟩
private def third : NotionRunAllocation.Id := ⟨3,[65]⟩
private def storedBlock : NotionCoreSliceForest.Block := ⟨0,.node ⟨(0,.start),none⟩ .nil⟩
private def after : State := {instances := [(0,⟨[
  ⟨⟨first,.text 97 false⟩,.start⟩,
  ⟨⟨second,.text 98 false⟩,.item first⟩,
  ⟨⟨third,.text 88 false⟩,.item first⟩],[]⟩)],forest := [storedBlock],display := [0]}
private def aa : Address := NotionCorePhysicalReplay.address 0 first
private def bb : Address := NotionCorePhysicalReplay.address 0 second
private def xx : Address := NotionCorePhysicalReplay.address 0 third
/-- A fresh sibling is rendered immediately after its origin; the older
sibling stays after the whole fresh run, rather than before it. -/
theorem insertion_control :
    NotionCoreMachineDocument.materializeDocument after = some
      [⟨0,0,[⟨(0,.start),[⟨aa,.text 97 false⟩,⟨xx,.text 88 false⟩,⟨bb,.text 98 false⟩],none⟩]⟩] ∧
    (NotionCoreMachineDocument.materializeDocument after).map
      (fun doc => doc.flatMap (fun block => block.slices.flatMap fun slice =>
        slice.atoms.flatMap atomText)) ≠ some [97,98,88] := by
  decide +kernel
end SPOT

#print axioms insert_source_step
#print axioms SPOT.insertion_control
#print axioms materializeDocument_insert
#print axioms materializeBlock_insert
#print axioms ownedRef_splice
#print axioms sliceAtoms_updated_cells
#print axioms updateCells_focus
#print axioms sliceAtoms_splice
#print axioms sliceAtoms_insert
end Sal.MRDTs.Instances.NotionCoreMachineDocumentInsert
