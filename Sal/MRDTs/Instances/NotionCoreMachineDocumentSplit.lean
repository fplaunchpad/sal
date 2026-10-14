import Sal.MRDTs.Instances.NotionCoreMachineDocumentInsert
import Sal.MRDTs.Instances.NotionCoreMachineDocumentCreate
import Sal.MRDTs.Instances.NotionCoreMachineCanonicalSplit
import Sal.MRDTs.Instances.NotionCoreSourceGuards
import Sal.MRDTs.Instances.NotionCoreMachineDocumentInvariant
import Sal.MRDTs.Instances.NotionCoreMachineCommands

/-! Checked materialization at the actual split marker. Physical insertion
and endpoint cutting remain separate source phases. Structural cell witnesses
are inputs, not supplied extraction or rendered-output equations. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineDocumentSplit
open NotionCoreSpec (Address)
open NotionCoreSource (Atom Slice Block)
open NotionCorePartition (Cell flatten boundary)
open NotionCoreSliceForest (Ref Normal active attached)
open NotionCoreMachine
open NotionCoreMachineDocument

/-- The fresh marker is an interior atom after RGA insertion. Changing the
left stop to marker and right start to marker excludes it from both extracts. -/
theorem split_slice_extraction (state raw : State) (before after : List Cell) (cell : Cell)
    (origin marker : Address)
    (oldPhysical : physical state cell.slice.start.1 = flatten (before ++ cell :: after))
    (oldUnique : ((physical state cell.slice.start.1).map Atom.address).Nodup)
    (present : origin ∈ cell.slice.traversal)
    (sameInstance : marker.1 = cell.slice.start.1)
    (changed : physical raw cell.slice.start.1 = NotionCorePartition.spliceAfterBy Atom.address
      origin [boundary marker] (physical state cell.slice.start.1))
    (existsInstance : raw.instances.any (fun entry => entry.1 == cell.slice.start.1) = true)
    (unique : ((physical raw cell.slice.start.1).map Atom.address).Nodup) :
    let position := cell.slice.traversal.idxOf origin
    sliceAtoms raw ⟨cell.slice.start,some marker⟩ = some (cell.slice.atoms.take position) ∧
      sliceAtoms raw ⟨marker,after.head?.map (fun next => next.slice.start)⟩ =
        some (cell.slice.atoms.drop position) := by
  let position := cell.slice.traversal.idxOf origin
  have factor : physical raw cell.slice.start.1 =
      (flatten before ++ boundary cell.slice.start :: cell.slice.atoms.take position) ++
        boundary marker :: (cell.slice.atoms.drop position ++ flatten after) := by
    rw [changed,oldPhysical,NotionCorePartition.insert_physical before after cell origin [boundary marker]
      (by simpa [oldPhysical] using oldUnique) present]
    simp [flatten,NotionCorePartition.Cell.physical,NotionCorePartition.insertCell,
      NotionCoreSource.insertSlice,position,List.append_assoc]
  constructor
  · exact NotionCoreMachineSlices.sliceAtoms_factor raw (flatten before)
      (cell.slice.atoms.take position) (boundary marker :: (cell.slice.atoms.drop position ++ flatten after))
      cell.slice.start (some marker) existsInstance factor
      (Or.inr ⟨marker,cell.slice.atoms.drop position ++ flatten after,rfl,rfl⟩) unique
  · have factorRight : physical raw marker.1 =
        ((flatten before ++ boundary cell.slice.start :: cell.slice.atoms.take position) ++
          boundary marker :: cell.slice.atoms.drop position) ++ flatten after := by
      rw [sameInstance,factor]
      simp [List.append_assoc]
    have ending : (flatten after = [] ∧ after.head?.map (fun next => next.slice.start) = none) ∨
        ∃ finish rest, flatten after = boundary finish :: rest ∧
          after.head?.map (fun next => next.slice.start) = some finish := by
      cases after with
      | nil => exact Or.inl ⟨rfl,rfl⟩
      | cons next rest => exact Or.inr ⟨next.slice.start,next.slice.atoms ++ flatten rest,rfl,rfl⟩
    exact NotionCoreMachineSlices.sliceAtoms_factor raw
      (flatten before ++ boundary cell.slice.start :: cell.slice.atoms.take position)
      (cell.slice.atoms.drop position) (flatten after) marker
      (after.head?.map (fun next => next.slice.start))
      (by simpa only [sameInstance] using existsInstance) factorRight ending
      (by simpa only [sameInstance] using unique)

theorem cut_active_ref (bid : Nat) (tree : NotionCoreSliceForest.Tree)
    (normal : Normal bid tree) (marker : Address) :
    active (NotionCoreSliceForest.cutActive tree marker) = ⟨(active tree).start,some marker⟩ ∧
      attached (NotionCoreSliceForest.cutActive tree marker) = attached tree := by
  cases normal <;> exact ⟨rfl,rfl⟩

/-- The selected source's actual tree cut materializes the left half of the
existing source-document split, including preservation of attached root shape. -/
theorem materialize_source_cut (state raw : State) (block : NotionCoreSliceForest.Block)
    (normal : Normal block.id block.title) (before after : List Cell) (cell : Cell)
    (selected : active block.title = ⟨cell.slice.start,after.head?.map (fun next => next.slice.start)⟩)
    (origin marker : Address) (target freshInstance : Nat)
    (oldPhysical : physical state cell.slice.start.1 = flatten (before ++ cell :: after))
    (oldUnique : ((physical state cell.slice.start.1).map Atom.address).Nodup)
    (present : origin ∈ cell.slice.traversal)
    (sameInstance : marker.1 = cell.slice.start.1)
    (changed : physical raw cell.slice.start.1 = NotionCorePartition.spliceAfterBy Atom.address
      origin [boundary marker] (physical state cell.slice.start.1))
    (existsInstance : raw.instances.any (fun entry => entry.1 == cell.slice.start.1) = true)
    (unique : ((physical raw cell.slice.start.1).map Atom.address).Nodup) :
    let source : Block := ⟨block.id,if attached block.title then .attached block.id else .own,cell.slice⟩
    materializeBlock raw {block with title := NotionCoreSliceForest.cutActive block.title marker} =
      some (NotionCoreSource.splitBlock source (cell.slice.traversal.idxOf origin) marker target freshInstance).1 := by
  have left := (split_slice_extraction state raw before after cell origin marker oldPhysical oldUnique
    present sameInstance changed existsInstance unique).1
  have cut := cut_active_ref block.id block.title normal marker
  simp [materializeBlock,cut.1,cut.2,selected,left,NotionCoreSource.splitBlock,NotionCoreSource.splitSlice]

/-- The moved leaf under the target's retained empty title materializes the
right half; the unused own-root identity is kept by the attached shape tag. -/
theorem materialize_destination_cut (state raw : State) (before after : List Cell) (cell : Cell)
    (origin marker : Address) (source : Block) (target : Nat)
    (oldPhysical : physical state cell.slice.start.1 = flatten (before ++ cell :: after))
    (oldUnique : ((physical state cell.slice.start.1).map Atom.address).Nodup)
    (present : origin ∈ cell.slice.traversal)
    (sameInstance : marker.1 = cell.slice.start.1)
    (changed : physical raw cell.slice.start.1 = NotionCorePartition.spliceAfterBy Atom.address
      origin [boundary marker] (physical state cell.slice.start.1))
    (existsInstance : raw.instances.any (fun entry => entry.1 == cell.slice.start.1) = true)
    (unique : ((physical raw cell.slice.start.1).map Atom.address).Nodup)
    (activeSlice : source.active = cell.slice) :
    materializeBlock raw ⟨target,.node (NotionCoreSliceForest.titleRef target)
      (.cons (.node ⟨marker,after.head?.map (fun next => next.slice.start)⟩ .nil) .nil)⟩ =
        some (NotionCoreSource.splitBlock source (cell.slice.traversal.idxOf origin) marker target target).2 := by
  have right := (split_slice_extraction state raw before after cell origin marker oldPhysical oldUnique
    present sameInstance changed existsInstance unique).2
  simp [materializeBlock,active,attached,NotionCoreSliceForest.Tree.children,
    NotionCoreSliceForest.Tree.slice,right,NotionCoreSource.splitBlock,NotionCoreSource.splitSlice,activeSlice]

/-- The actual post-move forest changes titles but retains every block ID.
Lookup therefore derives its new surrounding context from the old forest. -/
theorem find_title_map (forest : NotionCoreSliceForest.Forest)
    (change : NotionCoreSliceForest.Block → NotionCoreSliceForest.Block)
    (ids : ∀ block, (change block).id = block.id) (bid : Nat) :
    (forest.map change).find? (fun block => block.id == bid) =
      (forest.find? (fun block => block.id == bid)).map change := by
  induction forest with
  | nil => rfl
  | cons block rest ih =>
    by_cases selected : block.id == bid
    · simp [List.find?,ids,selected]
    · simp [List.find?,ids,selected,ih]

/-- Forest context for a single selected source and the appended destination.
This identity is derived from fresh target and unique old IDs, before any
extraction or document-output equation is used. -/
theorem split_forest_map (before after : NotionCoreSliceForest.Forest)
    (source : NotionCoreSliceForest.Block) (target : Nat) (marker : Address)
    (unique : ((before ++ source :: after).map NotionCoreSliceForest.Block.id).Nodup)
    (fresh : target ∉ (before ++ source :: after).map NotionCoreSliceForest.Block.id) :
    let destination : NotionCoreSliceForest.Block := ⟨target,
      .node (NotionCoreSliceForest.titleRef target)
        (.cons (.node ⟨marker,(active source.title).stop⟩ .nil) .nil)⟩
    let change := fun block : NotionCoreSliceForest.Block =>
      if block.id = source.id then {block with title := NotionCoreSliceForest.cutActive block.title marker}
      else if block.id = target then destination else block
    ((before ++ source :: after) ++ [({id := target,title := NotionCoreSliceForest.freshTitle target} : NotionCoreSliceForest.Block)]).map change =
      (before ++ {source with title := NotionCoreSliceForest.cutActive source.title marker} :: after) ++
        [destination] := by
  have uniqueMapped : (before.map NotionCoreSliceForest.Block.id ++ source.id :: after.map NotionCoreSliceForest.Block.id).Nodup := by
    simpa using unique
  have sourceNotBefore : source.id ∉ before.map NotionCoreSliceForest.Block.id := by
    have separated := (List.nodup_append.mp uniqueMapped).2.2
    exact fun member => separated source.id member source.id (by simp) rfl
  have sourceNotAfter : source.id ∉ after.map NotionCoreSliceForest.Block.id := by
    exact (List.nodup_cons.mp (List.nodup_append.mp uniqueMapped).2.1).1
  have targetNe : target ≠ source.id := by
    intro equal
    apply fresh
    simp [equal]
  have untouched (xs : NotionCoreSliceForest.Forest)
      (noSource : source.id ∉ xs.map NotionCoreSliceForest.Block.id)
      (noTarget : target ∉ xs.map NotionCoreSliceForest.Block.id) :
      xs.map (fun block : NotionCoreSliceForest.Block =>
        if block.id = source.id then {block with title := NotionCoreSliceForest.cutActive block.title marker}
        else if block.id = target then
          ⟨target,.node (NotionCoreSliceForest.titleRef target)
            (.cons (.node ⟨marker,(active source.title).stop⟩ .nil) .nil)⟩ else block) = xs := by
    conv_rhs => rw [← List.map_id xs]
    apply List.map_congr_left
    intro block member
    have first : block.id ≠ source.id := fun equal => noSource (List.mem_map.mpr ⟨block,member,equal⟩)
    have second : block.id ≠ target := fun equal => noTarget (List.mem_map.mpr ⟨block,member,equal⟩)
    simp [first,second]
  have beforeTarget : target ∉ before.map NotionCoreSliceForest.Block.id := by
    intro member
    exact fresh (by simp [member])
  have afterTarget : target ∉ after.map NotionCoreSliceForest.Block.id := by
    intro member
    exact fresh (by simp [member])
  simp only [List.map_append,List.map_cons,List.map_nil]
  rw [untouched before sourceNotBefore beforeTarget,untouched after sourceNotAfter afterTarget]
  simp [targetNe]

private theorem mapM_transport {α β : Type} (xs : List α) (f g : α → Option β)
    (change : β → β) (pointwise : ∀ x y, f x = some y → g x = some (change y))
    (ys : List β) (accepted : xs.mapM f = some ys) :
    xs.mapM g = some (ys.map change) := by
  induction xs generalizing ys with
  | nil => simpa using accepted
  | cons head tail ih =>
    cases first : f head with
    | none => simp [List.mapM_cons,first] at accepted
    | some value =>
      cases rest : tail.mapM f with
      | none => simp [List.mapM_cons,first,rest] at accepted
      | some values =>
        have equal : value :: values = ys := by
          simpa [List.mapM_cons,first,rest] using accepted
        subst ys
        simp [List.mapM_cons,pointwise head value first,ih values rest]

/-- Display materialization composes checked local extraction proofs through
an actual ID-preserving forest change. No document-output equation is input;
the local extraction premise is discharged by the physical slice lemmas. -/
theorem materializeDocument_title_map (state next : State)
    (changeTree : NotionCoreSliceForest.Block → NotionCoreSliceForest.Block)
    (ids : ∀ block, (changeTree block).id = block.id)
    (forest : next.forest = state.forest.map changeTree)
    (display : next.display = state.display)
    (changeSource : Block → Block)
    (localExtract : ∀ block ∈ state.forest, ∀ source,
      materializeBlock state block = some source →
      materializeBlock next (changeTree block) = some (changeSource source))
    (document : NotionCoreSourceDocument.Document)
    (accepted : materializeDocument state = some document) :
    materializeDocument next = some (document.map changeSource) := by
  unfold materializeDocument at accepted ⊢
  rw [display]
  apply mapM_transport state.display _ _ changeSource ?_ document accepted
  intro bid source selected
  rw [forest,find_title_map state.forest changeTree ids bid]
  cases found : state.forest.find? (fun block => block.id == bid) with
  | none => simp [found] at selected
  | some block =>
    have extracted : materializeBlock state block = some source := by
      simpa [found] using selected
    have nextExtract := localExtract block (List.mem_of_find?_eq_some found) source extracted
    simpa using nextExtract

/-- Actual recursive marker selection identifies an old origin-owning slice.
A fresh marker cannot have appeared in an unaffected interval: this follows
from checked old extraction and the physical splice, not an owner premise. -/
theorem selected_marker_origin (state raw : State)
    (oldPart : NotionCoreMachinePartition.Partitioned state)
    (rawPart : NotionCoreMachinePartition.Partitioned raw)
    (owned : Nat × Ref)
    (oldMember : owned ∈ NotionCoreForestRefs.ownedRefs state.forest)
    (rawMember : owned ∈ NotionCoreForestRefs.ownedRefs raw.forest)
    (origin marker : Address)
    (oldUnique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (rawUnique : ∀ inst, ((physical raw inst).map Atom.address).Nodup)
    (present : origin ∈ (physical state marker.1).map Atom.address)
    (fresh : marker ∉ (physical state marker.1).map Atom.address)
    (changed : physical raw marker.1 = NotionCorePartition.spliceAfterBy Atom.address
      origin [boundary marker] (physical state marker.1))
    (literal : boundary marker ∈ physical raw marker.1)
    (contained : NotionCoreSliceForest.contains (physical raw) owned.2 marker = true) :
    ∃ slice : Slice, slice.start = owned.2.start ∧
      sliceAtoms state owned.2 = some slice.atoms ∧ origin ∈ slice.traversal := by
  have same : owned.2.start.1 = marker.1 := by
    have conditions : owned.2.start.1 = marker.1 ∧
        (NotionCorePartition.extractIds (physical raw owned.2.start.1) owned.2.start owned.2.stop).contains (some marker) = true := by
      simpa only [NotionCoreSliceForest.contains,Bool.and_eq_true,decide_eq_true_eq] using contained
    exact conditions.1
  obtain ⟨before,cell,after,left,right,factor,refEq,atomsEq,_,_⟩ :=
    NotionCoreMachinePartitionSplit.containing_cell_cut raw rawPart rawUnique
      owned.1 owned.2 marker rawMember contained literal
  have ref : owned.2 = ⟨cell.slice.start,after.head?.map (fun next => next.slice.start)⟩ :=
    congrArg Prod.snd refEq
  have rawExists : raw.instances.any (fun entry => entry.1 == owned.2.start.1) = true := by
    simpa using rawPart.refsExist owned rawMember
  have rawExtract : sliceAtoms raw owned.2 = some cell.slice.atoms := by
    rw [ref]
    apply NotionCoreMachineSlices.sliceAtoms_cell raw before after cell
    · simpa only [ref] using rawExists
    · simpa [← same,ref] using factor
    · simpa only [ref] using rawUnique owned.2.start.1
  obtain ⟨slice,startEq,oldExtract,updated⟩ :=
    NotionCoreMachineDocumentInsert.ownedRef_splice state raw oldPart owned oldMember origin
      [boundary marker] (oldUnique _) (same ▸ present) (same ▸ changed) rawExists (rawUnique _)
  refine ⟨slice,startEq,oldExtract,?_⟩
  by_contra absent
  simp only [if_neg absent] at updated
  have equal : slice.atoms = cell.slice.atoms := Option.some.inj (updated.symm.trans rawExtract)
  have markerIn : boundary marker ∈ slice.atoms := by rw [equal,atomsEq]; simp
  have physicalMember := (NotionCoreMachineClient.slice_physical state owned.2 slice.atoms oldExtract).2
    (boundary marker) markerIn
  exact fresh (by rw [← same]; exact List.mem_map.mpr ⟨boundary marker,physicalMember,rfl⟩)

private theorem mapM_output_member {α β : Type} (f : α → Option β)
    (xs : List α) (ys : List β) (accepted : xs.mapM f = some ys)
    (x : α) (member : x ∈ xs) (y : β) (selected : f x = some y) : y ∈ ys := by
  induction xs generalizing ys with
  | nil => simp at member
  | cons head tail ih =>
    cases first : f head with
    | none => simp [List.mapM_cons,first] at accepted
    | some value =>
      cases rest : tail.mapM f with
      | none => simp [List.mapM_cons,first,rest] at accepted
      | some values =>
        have equal : value :: values = ys := by
          simpa [List.mapM_cons,first,rest] using accepted
        subst ys
        rcases List.mem_cons.mp member with equal | member
        · subst x
          have valueEq := Option.some.inj (first.symm.trans selected)
          simp [valueEq]
        · exact List.mem_cons_of_mem _ (ih values rest member)

/-- Stored normal blocks occur in the actual display-ordered projection;
this uses display alignment and successful materialization, not a caller's
receipt or owner mapping. -/
theorem materialized_member (state : State)
    (aligned : NotionCoreMachineDisplay.Aligned state)
    (document : NotionCoreSourceDocument.Document)
    (accepted : materializeDocument state = some document)
    (block : NotionCoreSliceForest.Block) (member : block ∈ state.forest)
    (source : Block) (extracted : materializeBlock state block = some source) :
    source ∈ document := by
  have found := NotionCoreMachineClient.find_block_member state.forest aligned.1 block member
  have displayed : block.id ∈ state.display := aligned.2.mem_iff.mpr
    (List.mem_map.mpr ⟨block,member,rfl⟩)
  apply mapM_output_member _ state.display document accepted block.id displayed source
  simpa [found] using extracted

/-- Once the source-selected old slice has been materialized, global slot
uniqueness identifies the document's searched owner with that same block. -/
theorem owner_of_materialized_slice (document : NotionCoreSourceDocument.Document)
    (unique : (NotionCoreInvariant.addresses (NotionCoreSourceDocument.project document)).Nodup)
    (source : Block) (member : source ∈ document) (origin : Address)
    (present : origin ∈ source.active.traversal) :
    NotionCoreSourceDocument.owner document origin = some source := by
  cases found : NotionCoreSourceDocument.owner document origin with
  | none =>
    have absent := List.find?_eq_none.mp found source member
    simp [NotionCoreSourceDocument.owns,present] at absent
  | some other =>
    have otherMember := List.mem_of_find?_eq_some found
    have otherOwns := List.find?_some found
    have otherPresent : origin ∈ other.active.traversal := by
      simpa [NotionCoreSourceDocument.owns] using otherOwns
    have same := NotionCoreSourceGuards.active_owner_unique unique member otherMember present otherPresent
    simpa [same] using found

private theorem block_eq_of_id (forest : NotionCoreSliceForest.Forest)
    (unique : (forest.map NotionCoreSliceForest.Block.id).Nodup)
    (left right : NotionCoreSliceForest.Block) (leftMember : left ∈ forest)
    (rightMember : right ∈ forest) (ids : left.id = right.id) : left = right := by
  have first := NotionCoreMachineClient.find_block_member forest unique left leftMember
  have second := NotionCoreMachineClient.find_block_member forest unique right rightMember
  rw [ids] at first
  exact Option.some.inj (first.symm.trans second)

private theorem normal_active_owned (state : State)
    (normal : NotionCoreSliceForest.NormalForest state.forest)
    (block : NotionCoreSliceForest.Block) (member : block ∈ state.forest) :
    (block.id,active block.title) ∈ NotionCoreForestRefs.ownedRefs state.forest := by
  have activeMember : active block.title ∈ NotionCoreSliceForest.preorderTree block.title := by
    have helper (bid : Nat) (tree : NotionCoreSliceForest.Tree) (h : Normal bid tree) :
        active tree ∈ NotionCoreSliceForest.preorderTree tree := by
      cases h <;> simp [active,NotionCoreSliceForest.preorderTree,
      NotionCoreSliceForest.preorderChildren,NotionCoreSliceForest.Tree.children,NotionCoreSliceForest.Tree.slice]
    exact helper block.id block.title (normal block member)
  exact List.mem_flatMap.mpr ⟨block,member,List.mem_map.mpr ⟨_,activeMember,rfl⟩⟩

private theorem source_find_member (document : NotionCoreSourceDocument.Document)
    (unique : (document.map Block.id).Nodup) (source : Block) (member : source ∈ document) :
    document.find? (fun block => block.id == source.id) = some source := by
  induction document with
  | nil => simp at member
  | cons first rest ih =>
    have nd := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with rfl | member
    · simp
    · have different : first.id ≠ source.id := by
        intro equal
        exact nd.1 (List.mem_map.mpr ⟨source,member,equal.symm⟩)
      simp [different,ih nd.2 member]

/-- Complete display-ordered split materialization from the actual physical
splice and the source algorithm's derived forest context. No next document,
owner, extraction, or rendered-output equation is assumed. -/
theorem split_document_from_context (state raw next : State)
    (part : NotionCoreMachinePartition.Partitioned state)
    (normal : NotionCoreSliceForest.NormalForest state.forest)
    (aligned : NotionCoreMachineDisplay.Aligned state)
    (document : NotionCoreSourceDocument.Document)
    (old : materializeDocument state = some document)
    (docUnique : (NotionCoreInvariant.addresses (NotionCoreSourceDocument.project document)).Nodup)
    (before after : NotionCoreSliceForest.Forest) (selected : NotionCoreSliceForest.Block)
    (target : Nat) (origin marker : Address)
    (forest : state.forest = (before ++ selected :: after) ++ [⟨target,NotionCoreSliceForest.freshTitle target⟩])
    (targetFresh : target ∉ (before ++ selected :: after).map NotionCoreSliceForest.Block.id)
    (lead tail : List Cell) (cell : Cell)
    (selectedRef : active selected.title = ⟨cell.slice.start,tail.head?.map (fun next => next.slice.start)⟩)
    (oldPhysical : physical state cell.slice.start.1 = flatten (lead ++ cell :: tail))
    (originPresent : origin ∈ cell.slice.traversal)
    (sameMarker : marker.1 = cell.slice.start.1)
    (originInst : origin.1 = cell.slice.start.1)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (rawUnique : ∀ inst, ((physical raw inst).map Atom.address).Nodup)
    (rawExists : ∀ inst, state.instances.any (fun entry => entry.1 == inst) = true →
      raw.instances.any (fun entry => entry.1 == inst) = true)
    (changed : physical raw cell.slice.start.1 = NotionCorePartition.spliceAfterBy Atom.address
      origin [boundary marker] (physical state cell.slice.start.1))
    (frames : ∀ inst, inst ≠ cell.slice.start.1 → physical raw inst = physical state inst)
    (nextInstances : next.instances = raw.instances)
    (nextDisplay : next.display = state.display)
    (nextForest : next.forest =
      (before ++ {selected with title := NotionCoreSliceForest.cutActive selected.title marker} :: after) ++
      [⟨target,.node (NotionCoreSliceForest.titleRef target)
        (.cons (.node ⟨marker,(active selected.title).stop⟩ .nil) .nil)⟩])
    (targetEmpty : physical state target = NotionCoreSliceForest.emptyPhysical target) :
    ∃ result, materializeDocument next = some result ∧
      NotionCoreSourceDocument.step document (.split origin marker target) = some result := by
  let source : Block := ⟨selected.id,if attached selected.title then .attached selected.id else .own,cell.slice⟩
  let destination : NotionCoreSliceForest.Block := ⟨target,NotionCoreSliceForest.freshTitle target⟩
  let rightTree : NotionCoreSliceForest.Block := ⟨target,.node (NotionCoreSliceForest.titleRef target)
    (.cons (.node ⟨marker,(active selected.title).stop⟩ .nil) .nil)⟩
  let halves := NotionCoreSource.splitBlock source (cell.slice.traversal.idxOf origin) marker target target
  let changeTree := fun block : NotionCoreSliceForest.Block =>
    if block.id = selected.id then {block with title := NotionCoreSliceForest.cutActive block.title marker}
    else if block.id = target then rightTree else block
  let changeSource := fun block : Block =>
    if block.id = selected.id then halves.1 else if block.id = target then halves.2 else block
  have selectedMember : selected ∈ state.forest := by rw [forest]; simp
  have destMember : destination ∈ state.forest := by rw [forest]; simp [destination]
  have selectedNormal := normal selected selectedMember
  have activeOwned := normal_active_owned state normal selected selectedMember
  have oldExists : state.instances.any (fun entry => entry.1 == cell.slice.start.1) = true := by
    have stored := part.refsExist (selected.id,active selected.title) activeOwned
    simpa [selectedRef] using stored
  have newExists := rawExists cell.slice.start.1 oldExists
  have sourceMat : materializeBlock state selected = some source := by
    have extracted := NotionCoreMachineSlices.sliceAtoms_cell state lead tail cell oldExists oldPhysical (unique _)
    simp [materializeBlock,selectedRef,extracted,source]
  have sourceMember := materialized_member state aligned document old selected selectedMember source sourceMat
  have sourceOwner := owner_of_materialized_slice document docUnique source sourceMember origin originPresent
  have targetExists : state.instances.any (fun entry => entry.1 == target) = true := by
    have owned := normal_active_owned state normal destination destMember
    simpa [destination,NotionCoreSliceForest.active,NotionCoreSliceForest.freshTitle,
      NotionCoreSliceForest.titleRef,NotionCoreSliceForest.Tree.children,NotionCoreSliceForest.Tree.slice]
      using part.refsExist (destination.id,active destination.title) owned
  have destMat : materializeBlock state destination = some (NotionCoreSourceDocument.freshBlock target target) := by
    have extracted := NotionCoreMachineSlices.empty_title_atoms state target targetExists targetEmpty
    change sliceAtoms state ⟨(target,.start),none⟩ = some [] at extracted
    simp [materializeBlock,destination,NotionCoreSliceForest.active,NotionCoreSliceForest.attached,
      NotionCoreSliceForest.freshTitle,NotionCoreSliceForest.Tree.children,NotionCoreSliceForest.Tree.slice,
      extracted,NotionCoreSourceDocument.freshBlock,NotionCoreSliceForest.titleRef]
  have destDocMember := materialized_member state aligned document old destination destMember _ destMat
  have docIds : (document.map Block.id).Nodup := by
    rw [materialized_ids state document old]
    exact aligned.2.nodup_iff.mpr aligned.1
  have destFound := source_find_member document docIds (NotionCoreSourceDocument.freshBlock target target) destDocMember
  change document.find? (fun block => block.id == target) = some (NotionCoreSourceDocument.freshBlock target target) at destFound
  have sourceTarget : selected.id ≠ target := by
    intro equal
    exact targetFresh (by simp [← equal])
  have oldBaseUnique : ((before ++ selected :: after).map NotionCoreSliceForest.Block.id).Nodup := by
    have oldUnique : (state.forest.map NotionCoreSliceForest.Block.id).Nodup := aligned.1
    rw [forest,List.map_append] at oldUnique
    exact (List.nodup_append.mp oldUnique).1
  have treeMap : next.forest = state.forest.map changeTree := by
    rw [forest,nextForest]
    exact (split_forest_map before after selected target marker oldBaseUnique targetFresh).symm
  have treeIds : ∀ block, (changeTree block).id = block.id := by
    intro block
    simp only [changeTree]
    split
    · rfl
    · split
      · rename_i equal
        exact equal.symm
      · rfl
  have localExtract : ∀ block ∈ state.forest, ∀ value,
      materializeBlock state block = some value → materializeBlock next (changeTree block) = some (changeSource value) := by
    intro block member value mat
    have valueId := (materialized_atoms state block value mat).2
    have nextMatFrame (b : NotionCoreSliceForest.Block) : materializeBlock next b = materializeBlock raw b := by
      simp only [materializeBlock,sliceAtoms,physical,getInstance,nextInstances]
    by_cases isSource : block.id = selected.id
    · have equal := block_eq_of_id state.forest aligned.1 block selected member selectedMember isSource
      subst block
      have valueEq : value = source := Option.some.inj (mat.symm.trans sourceMat)
      subst value
      rw [nextMatFrame]
      simpa [changeTree,changeSource,source,sourceTarget,halves] using
        materialize_source_cut state raw selected selectedNormal lead tail cell selectedRef origin marker
          target target oldPhysical (unique _) originPresent sameMarker changed newExists (rawUnique _)
    · by_cases isTarget : block.id = target
      · have equal := block_eq_of_id state.forest aligned.1 block destination member destMember isTarget
        subst block
        have valueEq : value = NotionCoreSourceDocument.freshBlock target target := Option.some.inj (mat.symm.trans destMat)
        subst value
        rw [nextMatFrame]
        have right := materialize_destination_cut state raw lead tail cell origin marker source target
          oldPhysical (unique _) originPresent sameMarker changed newExists (rawUnique _) rfl
        simpa [changeTree,changeSource,destination,rightTree,selectedRef,sourceTarget,halves,
          NotionCoreSourceDocument.freshBlock,Ne.symm sourceTarget] using right
      · have valueMember := materialized_member state aligned document old block member value mat
        have absent : ¬ origin ∈ value.active.traversal := by
          intro owned
          have equal := NotionCoreSourceGuards.active_owner_unique docUnique sourceMember valueMember originPresent owned
          have ids := congrArg Block.id equal
          exact isSource (valueId.symm.trans ids.symm)
        have owned := normal_active_owned state normal block member
        have updated := NotionCoreMachineDocumentInsert.materializeBlock_insert state raw part block value owned mat
          cell.slice.start.1 origin [boundary marker] originInst unique rawUnique rawExists
          (by
            rw [oldPhysical]
            apply List.mem_map.mpr
            rcases List.mem_cons.mp originPresent with equal | inside
            · exact ⟨boundary cell.slice.start,List.mem_flatMap.mpr ⟨cell,by simp,by simp [Cell.physical]⟩,equal.symm⟩
            · obtain ⟨atom,member,equal⟩ := List.mem_map.mp inside
              exact ⟨atom,List.mem_flatMap.mpr ⟨cell,by simp,by simp [Cell.physical,member]⟩,equal⟩) changed frames
        rw [nextMatFrame]
        simpa [changeTree,changeSource,isSource,isTarget,valueId,NotionCoreSourceDocument.owns,absent] using updated
  refine ⟨document.map changeSource,
    materializeDocument_title_map state next changeTree treeIds treeMap nextDisplay changeSource localExtract document old,?_⟩
  simp only [NotionCoreSourceDocument.step,sourceOwner,destFound]
  simp [sourceTarget,source,NotionCoreSourceDocument.EmptyRoot,NotionCoreSourceDocument.freshBlock,
    changeSource,halves]

/-- Honest canonical split refines the existing two-command source-document
transaction. The displayed predecessor is the requested block, whereas the
source to cut is recovered by the actual origin/marker searches. -/
theorem canonical_split_source_step_with_execution (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (document : NotionCoreSourceDocument.Document)
    (old : materializeDocument state = some document)
    (block inst : NotionCorePayload.BlockKey) (origin : NotionCoreOriginTree.Origin)
    (payload : tx.payload = .split block inst origin) :
    ∃ next intermediate result, applyTransaction state tx = some next ∧
      materializeDocument next = some result ∧
      NotionCoreSourceDocument.step document (.create (blockName (.issued tx.id))
        (blockName (.issued tx.id)) (some (blockName block))) = some intermediate ∧
      NotionCoreSourceDocument.step intermediate (.split
        (NotionCorePhysicalReplay.originAddress (blockName inst) origin)
        (NotionCorePhysicalReplay.address (blockName inst) tx.id)
        (blockName (.issued tx.id))) = some result ∧
      NotionCoreSourceDocument.Execution document (NotionCoreMachineCommands.commands tx) result := by
  have creators := NotionCoreMachineNetwork.creator_reachable reachable
  have payloadReach := NotionCoreCreatorNetwork.payload_reachable creators
  obtain ⟨checked,checkedReplay,part,shape,rootActive⟩ :=
    NotionCoreMachineHonestReplay.honest_prefix_reconstruct network reachable peer pre (tx :: suffix) position
  have equal : checked = state := Option.some.inj (checkedReplay.symm.trans accepted)
  subst checked
  obtain ⟨provider,providerMember,root,_⟩ := NotionCoreRootCreators.canonical_selected_root_provider
    network creators (NotionCoreMachineHonestReplay.honest_root_provenance network reachable)
    peer pre suffix tx position inst (by simp [payload,NotionCoreRootCreators.selectedInstances])
  have activeInst : NotionCoreMachineShape.ActiveInstance state (blockName inst) :=
    (rootActive _).mpr ⟨provider,providerMember,inst,root,rfl⟩
  obtain ⟨freshInstance,freshBlock⟩ := NotionCoreMachineCanonicalCreate.canonical_destination_fresh
    network creators peer pre suffix tx position state accepted
  obtain ⟨created,rows,createStep,integrated,stage,rawForest,emptyTarget,_⟩ :=
    NotionCoreMachineMarkerProgress.canonical_split_marker_phase network creators peer pre suffix tx position
      state accepted part block inst origin payload
  let raw := putInstance created (blockName inst) {getInstance created (blockName inst) with rows := rows}
  let marker := NotionCorePhysicalReplay.address (blockName inst) tx.id
  let address := NotionCorePhysicalReplay.originAddress (blockName inst) origin
  let target := blockName (.issued tx.id)
  have createShape := NotionCoreMachineCanonicalCreate.fresh_create_shape state created (.issued tx.id)
    (some block) freshInstance freshBlock createStep
  have createPart := NotionCoreMachinePartitionCreate.create_preserves_partitioned state created
    (.issued tx.id) (some block) part freshInstance freshBlock createStep
  have createStrong := NotionCoreMachineShape.fresh_create_shape_preserves state created (.issued tx.id)
    (some block) shape freshInstance freshBlock createStep
  have createActive := NotionCoreMachineShape.fresh_create_active state created (.issued tx.id)
    (some block) freshInstance freshBlock createStep (blockName inst) activeInst
  have rawStrong := NotionCoreMachineShape.raw_marker_shape_preserves created inst rows createStrong createActive
  have aligned := NotionCoreMachineDisplay.replay_aligned {} state pre
    (by simp [NotionCoreMachineDisplay.Aligned,NotionCoreDisplayOrder.Aligned,NotionCoreDisplayOrder.names]) accepted
  have createAligned := NotionCoreMachineDisplay.operation_aligned state created _ aligned createStep
  have previousMember := NotionCoreMachineBlockPresence.canonical_required_block
    network creators peer pre suffix tx position state accepted block
      (by simp [payload,NotionCoreCreatorNetwork.requiredBlocks])
  obtain ⟨intermediate,createdDoc,createDocStep⟩ := NotionCoreMachineDocumentCreate.fresh_create_document
    state created (.issued tx.id) (some block) freshInstance freshBlock createStep aligned document old (by
      intro key equality
      have keyEq : key = block := Option.some.inj equality.symm
      subst key
      exact aligned.2.mem_iff.mpr previousMember)
  have existsOld := NotionCoreMachineCreatorPresence.canonical_required_instance network creators peer pre suffix tx
    position state accepted inst (by simp [payload,NotionCoreCreatorNetwork.requiredBlocks])
  have instDistinct : blockName inst ≠ target := by
    obtain ⟨entry,member,equal⟩ := existsOld
    exact fun same => freshInstance entry member (equal.trans same)
  have storage := NotionCoreMachineCanonicalCreate.fresh_create_storage state created (.issued tx.id)
    (some block) freshInstance freshBlock createStep
  have sameStorage : getInstance created (blockName inst) = getInstance state (blockName inst) := by
    simpa [target,instDistinct] using storage (blockName inst)
  obtain ⟨originalRows,originalIntegrated,originalPhysical,fresh,originPhysical⟩ :=
    NotionCoreMachineMarkerProgress.canonical_marker_physical network payloadReach peer pre suffix tx position
      state accepted block inst origin payload
  have rowEqual : originalRows = rows := by
    rw [← sameStorage] at originalIntegrated
    exact Option.some.inj (originalIntegrated.symm.trans integrated)
  subst originalRows
  have changed : physical raw (blockName inst) = NotionCorePartition.spliceAfterBy Atom.address
      address [boundary marker] (physical created (blockName inst)) := by
    simpa only [raw,physical,NotionCoreMachineTables.getInstance_put,if_pos rfl,sameStorage] using originalPhysical
  have originPresent : address ∈ (physical created (blockName inst)).map Atom.address := by
    simpa only [physical,sameStorage] using originPhysical
  have markerFresh : marker ∉ (physical created (blockName inst)).map Atom.address := by
    simpa only [physical,sameStorage] using fresh
  have createdUnique : ∀ key, ((physical created key).map Atom.address).Nodup := by
    have uniqueOld := NotionCoreMachineMarkerProgress.canonical_physical_unique_all network payloadReach peer pre
      (tx :: suffix) position state accepted
    have physicalFrame := NotionCoreMachineCanonicalCreate.fresh_create_physical state created (.issued tx.id)
      (some block) freshInstance freshBlock createStep
    intro key
    by_cases same : key = target
    · subst key
      rw [physicalFrame.1]
      simp [NotionCoreSliceForest.emptyPhysical]
    · rw [physicalFrame.2 key same]
      exact uniqueOld key
  have freshTarget : target ∉ state.forest.map NotionCoreSliceForest.Block.id := by
    intro member
    obtain ⟨b,member,equal⟩ := List.mem_map.mp member
    exact freshBlock b member equal
  have freshMarker : NotionCoreSliceForest.FreshMarker state.forest marker := by
    intro b member boundaryMember
    obtain ⟨ref,refMember,equal⟩ := List.mem_map.mp boundaryMember
    apply stage.fresh (b.id,ref)
    · apply List.mem_flatMap.mpr
      exact ⟨b,by rw [rawForest]; exact List.mem_append_left _ member,List.mem_map.mpr ⟨ref,refMember,rfl⟩⟩
    · exact equal
  have inactive : ∀ b ∈ state.forest, attached b.title = true →
      NotionCoreSliceForest.contains (physical raw) (NotionCoreSliceForest.titleRef b.id) marker = false := by
    intro b member attached
    apply NotionCoreMachineShape.inactive_title_rejects raw rawStrong b _ attached marker
    rw [rawForest]
    exact List.mem_append_left _ member
  have rawExists : ∃ entry ∈ raw.instances, entry.1 = marker.1 := by
    have createdExists : ∃ entry ∈ created.instances, entry.1 = blockName inst := by
      obtain ⟨entry,member,equal⟩ := existsOld
      exact ⟨entry,createShape.1 ▸ List.mem_append_left _ member,equal⟩
    exact (NotionCoreMachinePartitionUpdates.putInstance_exists_iff created (blockName inst)
      (blockName inst) {getInstance created (blockName inst) with rows := rows} createdExists).mpr createdExists
  have markerDistinct : marker.1 ≠ target := NotionCoreMachineMarkerProgress.marker_instance_ne_empty raw
    (blockName inst) target tx.id stage.present emptyTarget
  obtain ⟨chosen,chosenMember,ref,refMember,contained⟩ := NotionCoreMachinePartition.containing_tree_ref raw
    stage.partitioned stage.unique marker rawExists (List.mem_map.mpr ⟨boundary marker,stage.present,rfl⟩) stage.fresh
  have chosenOld : chosen ∈ state.forest := by
    rw [rawForest] at chosenMember
    rcases List.mem_append.mp chosenMember with member | member
    · exact member
    · simp only [List.mem_singleton] at member
      subst chosen
      simp [NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.preorderChildren,
        NotionCoreSliceForest.freshTitle,NotionCoreSliceForest.Tree.children,NotionCoreSliceForest.Tree.slice] at refMember
      subst ref
      have equal : target = marker.1 := (by
        simpa only [NotionCoreSliceForest.contains,NotionCoreSliceForest.titleRef,Bool.and_eq_true,decide_eq_true_eq] using contained : target = marker.1 ∧ _).1
      exact False.elim (markerDistinct equal.symm)
  obtain ⟨before,chosen,after,context,chosenContains,atomic⟩ := NotionCoreMachinePartitionSplit.atomicSplit_context
    (physical raw) marker target state.forest shape.1 freshMarker freshTarget inactive emptyTarget
      ⟨chosen,chosenOld,ref,refMember,contained⟩
  have chosenCreated : chosen ∈ created.forest := by rw [createShape.2.1]; exact List.mem_append_left _ (by rw [context]; simp)
  have chosenRaw : chosen ∈ raw.forest := by rw [rawForest]; exact List.mem_append_left _ (by rw [context]; simp)
  have oldOwned := normal_active_owned created createStrong.1 chosen chosenCreated
  have rawOwned := normal_active_owned raw rawStrong.1 chosen chosenRaw
  obtain ⟨slice,startEq,oldSlice,ownsOrigin⟩ := selected_marker_origin created raw createPart stage.partitioned
    (chosen.id,active chosen.title) oldOwned rawOwned address marker createdUnique stage.unique
    originPresent markerFresh changed stage.present chosenContains
  obtain ⟨lead,cell,tail,factor,refEq⟩ := NotionCoreMachinePartition.ref_factor created createPart
    (chosen.id,active chosen.title) oldOwned
  have selectedRef : active chosen.title = ⟨cell.slice.start,tail.head?.map (fun next => next.slice.start)⟩ := congrArg Prod.snd refEq
  change physical created (active chosen.title).start.1 = _ at factor
  rw [selectedRef] at factor
  have existsCell : created.instances.any (fun entry => entry.1 == cell.slice.start.1) = true := by
    simpa [selectedRef] using createPart.refsExist (chosen.id,active chosen.title) oldOwned
  have extractCell := NotionCoreMachineSlices.sliceAtoms_cell created lead tail cell existsCell factor (createdUnique _)
  have sliceEq : slice = cell.slice := by
    have atomsEq := Option.some.inj (oldSlice.symm.trans (by simpa only [selectedRef] using extractCell))
    have start := startEq.trans (congrArg NotionCoreSliceForest.Ref.start selectedRef)
    change Slice.mk slice.start slice.atoms = Slice.mk cell.slice.start cell.slice.atoms
    exact congrArg₂ Slice.mk start atomsEq
  subst slice
  have sameInst : cell.slice.start.1 = blockName inst := by
    have condition : (active chosen.title).start.1 = marker.1 := by
      have conditions : (active chosen.title).start.1 = marker.1 ∧
          (NotionCorePartition.extractIds (physical raw (active chosen.title).start.1)
            (active chosen.title).start (active chosen.title).stop).contains (some marker) = true := by
        simpa only [NotionCoreSliceForest.contains,Bool.and_eq_true,decide_eq_true_eq] using chosenContains
      exact conditions.1
    simpa [selectedRef,marker,NotionCorePhysicalReplay.address] using condition
  let next : State := {raw with forest :=
    (before ++ {chosen with title := NotionCoreSliceForest.cutActive chosen.title marker} :: after) ++
    [⟨target,.node (NotionCoreSliceForest.titleRef target)
      (.cons (.node ⟨marker,(active chosen.title).stop⟩ .nil) .nil)⟩]}
  have transaction := NotionCoreMachineMarkerProgress.split_transaction_of_atomic state created tx block inst origin
    rows next.forest payload createStep integrated stage rawForest atomic
  have docUnique := NotionCoreMachineDocumentInvariant.projected_addresses_unique created createPart createdUnique
    createStrong createAligned intermediate createdDoc
  obtain ⟨result,materialized,splitStep⟩ := split_document_from_context created raw next createPart createStrong.1
    createAligned intermediate createdDoc docUnique before after chosen target address marker
    (by rw [createShape.2.1,context]) (by simpa [context] using freshTarget)
    lead tail cell selectedRef factor ownsOrigin (by simpa [marker,NotionCorePhysicalReplay.address] using sameInst.symm)
    (by cases origin <;> simpa [address,NotionCorePhysicalReplay.originAddress] using sameInst.symm)
    createdUnique stage.unique (by
      intro key oldExists
      have stored : ∃ entry ∈ created.instances, entry.1 = key := by simpa using oldExists
      have sourceStored : ∃ entry ∈ created.instances, entry.1 = blockName inst := by
        simpa [selectedRef,sameInst] using createPart.refsExist (chosen.id,active chosen.title) oldOwned
      simpa using (NotionCoreMachinePartitionUpdates.putInstance_exists_iff created (blockName inst) key
        {getInstance created (blockName inst) with rows := rows} sourceStored).mpr stored)
    (by simpa [sameInst] using changed)
    (by intro key different; simp [raw,physical,NotionCoreMachineTables.getInstance_put,← sameInst,different])
    rfl (by unfold next raw putInstance; split <;> rfl) rfl
    (NotionCoreMachineCanonicalCreate.fresh_create_physical state created (.issued tx.id)
      (some block) freshInstance freshBlock createStep).1
  have oldUnique := NotionCoreMachineMarkerProgress.canonical_physical_unique_all network payloadReach peer pre
    (tx :: suffix) position state accepted
  have createGuard := NotionCoreMachineDocumentInvariant.accepted_source_guard state part oldUnique shape aligned
    document intermediate old _ createDocStep
  have splitGuard := NotionCoreMachineDocumentInvariant.accepted_source_guard created createPart createdUnique
    createStrong createAligned intermediate result createdDoc _ splitStep
  have execution := NotionCoreSourceDocument.Execution.cons createGuard createDocStep
    (NotionCoreSourceDocument.Execution.cons splitGuard splitStep (NotionCoreSourceDocument.Execution.nil result))
  exact ⟨next,intermediate,result,transaction,materialized,createDocStep,splitStep,
    by simpa [NotionCoreMachineCommands.commands,payload] using execution⟩

/-- Public atomic execution endpoint for history composition. -/
theorem canonical_split_execution (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (document : NotionCoreSourceDocument.Document)
    (old : materializeDocument state = some document)
    (block inst : NotionCorePayload.BlockKey) (origin : NotionCoreOriginTree.Origin)
    (payload : tx.payload = .split block inst origin) :
    ∃ next result, applyTransaction state tx = some next ∧ materializeDocument next = some result ∧
      NotionCoreSourceDocument.Execution document (NotionCoreMachineCommands.commands tx) result := by
  obtain ⟨next,_,result,transaction,materialized,_,_,execution⟩ := canonical_split_source_step_with_execution
    network reachable peer pre suffix tx position state accepted document old block inst origin payload
  exact ⟨next,result,transaction,materialized,execution⟩

#print axioms canonical_split_execution
#print axioms canonical_split_source_step_with_execution
#print axioms split_document_from_context
#print axioms materialized_member
#print axioms owner_of_materialized_slice
#print axioms selected_marker_origin
#print axioms materializeDocument_title_map
#print axioms find_title_map
#print axioms split_forest_map
#print axioms split_slice_extraction
#print axioms materialize_source_cut
#print axioms materialize_destination_cut
end Sal.MRDTs.Instances.NotionCoreMachineDocumentSplit
