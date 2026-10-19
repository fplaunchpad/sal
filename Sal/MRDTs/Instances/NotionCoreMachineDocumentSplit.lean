import Sal.MRDTs.Instances.NotionCoreMachineDocumentInsert
import Sal.MRDTs.Instances.NotionCoreMachineDocumentCreate
import Sal.MRDTs.Instances.NotionCoreMachineCanonicalSplit
import Sal.MRDTs.Instances.NotionCoreSourceGuards
import Sal.MRDTs.Instances.NotionCoreMachineDocumentInvariant
import Sal.MRDTs.Instances.NotionCoreMachineCommands

/-! Checked materialization at the actual split marker. Physical insertion
and endpoint cutting remain separate source phases. The forest search cuts a
chain at the node holding the marker: the kept prefix ends with the left part
of that node, and the right part with every later node moves below the fresh
destination's empty title. Structural cell witnesses are inputs, not supplied
extraction or rendered-output equations. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineDocumentSplit
open NotionCoreSpec (Address)
open NotionCoreSource (Atom Slice Block)
open NotionCorePartition (Cell flatten boundary)
open NotionCoreSliceForest (Ref leftRef rightRef)
open NotionCoreMachine
open NotionCoreMachineDocument

/-- The fresh marker is an interior atom after RGA insertion. Changing the
left stop to marker and right start to marker excludes it from both extracts. -/
theorem split_slice_extraction (state raw : State) (before after : List Cell) (cell : Cell)
    (origin marker : Address)
    (oldPhysical : physical state cell.slice.start.1 = flatten (before ++ cell :: after))
    (oldUnique : ((physical state cell.slice.start.1).map Atom.address).Nodup)
    (present : origin ∈ cell.physical.map Atom.address)
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
    ∃ slice : Slice, slice.start = owned.2.start ∧ slice.stop = owned.2.stop ∧
      sliceAtoms state owned.2 = some slice.atoms ∧ origin ∈ slice.traversal := by
  have same : owned.2.start.1 = marker.1 := by
    have conditions : owned.2.start.1 = marker.1 ∧
        (NotionCorePartition.extractIds (physical raw owned.2.start.1) owned.2.start owned.2.stop).contains (some marker) = true := by
      simpa only [NotionCoreSliceForest.contains,Bool.and_eq_true,decide_eq_true_eq] using contained
    exact conditions.1
  have refMember : owned.2 ∈ NotionCoreSliceForest.forestRefs raw.forest := by
    rw [← NotionCoreForestRefs.ownedRefs_refs]
    exact List.mem_map.mpr ⟨owned,rawMember,rfl⟩
  obtain ⟨before,cell,after,left,right,factor,ref,atomsEq,_⟩ :=
    NotionCoreMachinePartitionSplit.containing_cell_cut raw _
      (NotionCoreMachinePartition.covers_of_partitioned rawPart) rawUnique owned.2 marker refMember
      contained literal
  have rawExists : raw.instances.any (fun entry => entry.1 == owned.2.start.1) = true := by
    simpa using rawPart.refsExist owned rawMember
  have rawExtract : sliceAtoms raw owned.2 = some cell.slice.atoms := by
    rw [ref]
    apply NotionCoreMachineSlices.sliceAtoms_cell raw before after cell
    · simpa only [ref] using rawExists
    · simpa [← same,ref] using factor
    · simpa only [ref] using rawUnique owned.2.start.1
  obtain ⟨slice,startEq,stopEq,oldExtract,updated⟩ :=
    NotionCoreMachineDocumentInsert.ownedRef_splice state raw oldPart owned oldMember origin
      [boundary marker] (oldUnique _) (same ▸ present) (same ▸ changed) rawExists (rawUnique _)
  refine ⟨slice,startEq,stopEq,oldExtract,?_⟩
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

private theorem block_eq_of_id (forest : NotionCoreSliceForest.Forest)
    (unique : (forest.map NotionCoreSliceForest.Block.id).Nodup)
    (left right : NotionCoreSliceForest.Block) (leftMember : left ∈ forest)
    (rightMember : right ∈ forest) (ids : left.id = right.id) : left = right := by
  have first := NotionCoreMachineClient.find_block_member forest unique left leftMember
  have second := NotionCoreMachineClient.find_block_member forest unique right rightMember
  rw [ids] at first
  exact Option.some.inj (first.symm.trans second)

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

private theorem mapM_split {α β : Type} (f : α → Option β) (pre post : List α) (x : α) (ys : List β)
    (accepted : (pre ++ x :: post).mapM f = some ys) :
    ∃ preY y postY, pre.mapM f = some preY ∧ f x = some y ∧ post.mapM f = some postY ∧
      ys = preY ++ y :: postY := by
  induction pre generalizing ys with
  | nil =>
    simp only [List.nil_append, List.mapM_cons] at accepted
    obtain ⟨y, first, later⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨postY, following, same⟩ := Option.bind_eq_some_iff.mp later
    exact ⟨[], y, postY, rfl, first, following, (Option.some.inj same).symm⟩
  | cons head rest ih =>
    simp only [List.cons_append, List.mapM_cons] at accepted
    obtain ⟨headY, first, later⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨tailY, following, same⟩ := Option.bind_eq_some_iff.mp later
    obtain ⟨preY, y, postY, preRead, xRead, postRead, tailEq⟩ := ih tailY following
    refine ⟨headY :: preY, y, postY, ?_, xRead, postRead, ?_⟩
    · simp [List.mapM_cons, first, preRead]
    · rw [← Option.some.inj same, tailEq]
      rfl

private theorem mapM_keep {α β : Type} (xs : List α) (f g : α → Option β) (ys : List β)
    (accepted : xs.mapM f = some ys)
    (frame : ∀ x ∈ xs, ∀ y, f x = some y → g x = some y) : xs.mapM g = some ys := by
  induction xs generalizing ys with
  | nil => simpa using accepted
  | cons head rest ih =>
    simp only [List.mapM_cons] at accepted
    obtain ⟨y, first, later⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨tail, following, same⟩ := Option.bind_eq_some_iff.mp later
    have equal : y :: tail = ys := Option.some.inj same
    subst ys
    rw [List.mapM_cons, frame head (by simp) y first,
      ih tail following (fun x member => frame x (List.mem_cons_of_mem _ member))]
    rfl

private theorem mapM_append_some {α β : Type} (f : α → Option β) (xs ys : List α) (as bs : List β)
    (left : xs.mapM f = some as) (right : ys.mapM f = some bs) : (xs ++ ys).mapM f = some (as ++ bs) := by
  induction xs generalizing as with
  | nil => simp at left; subst as; simpa using right
  | cons head rest ih =>
    simp only [List.mapM_cons] at left
    obtain ⟨a, first, later⟩ := Option.bind_eq_some_iff.mp left
    obtain ⟨tail, following, same⟩ := Option.bind_eq_some_iff.mp later
    have equal : a :: tail = as := Option.some.inj same
    subst as
    simp [List.mapM_cons, first, ih tail following]

/-- A stored reference whose slice does not hold the split origin keeps its
extracted atoms across the marker splice. -/
private theorem untouched_ref (state raw : State)
    (part : NotionCoreMachinePartition.Partitioned state)
    (block : NotionCoreSliceForest.Block) (member : block ∈ state.forest)
    (ref : Ref) (inTree : ref ∈ NotionCoreSliceForest.preorderTree block.title)
    (atoms : List Atom) (extracted : sliceAtoms state ref = some atoms)
    (inst : Nat) (origin marker : Address) (originInst : origin.1 = inst)
    (unique : ∀ key, ((physical state key).map Atom.address).Nodup)
    (rawUnique : ∀ key, ((physical raw key).map Atom.address).Nodup)
    (rawExists : ∀ key, state.instances.any (fun entry => entry.1 == key) = true →
      raw.instances.any (fun entry => entry.1 == key) = true)
    (present : origin ∈ (physical state inst).map Atom.address)
    (changed : physical raw inst = NotionCorePartition.spliceAfterBy Atom.address
      origin [boundary marker] (physical state inst))
    (frames : ∀ key, key ≠ inst → physical raw key = physical state key)
    (absent : origin ∉ (⟨ref.start,atoms,ref.stop⟩ : Slice).traversal) :
    sliceAtoms raw ref = some atoms := by
  have owned : (block.id,ref) ∈ NotionCoreForestRefs.ownedRefs state.forest :=
    List.mem_flatMap.mpr ⟨block,member,List.mem_map.mpr ⟨ref,inTree,rfl⟩⟩
  have updated := NotionCoreMachineDocumentInsert.sliceAtoms_insert state raw part (block.id,ref) owned
    atoms extracted inst origin [boundary marker] originInst unique rawUnique rawExists present changed frames
  simp only at updated
  rw [updated, if_neg absent]

/-- Every stored block occurs in the actual display-ordered projection; this
uses display alignment and successful materialization, not a caller's receipt
or owner mapping. -/
theorem materialized_member (state : State)
    (aligned : NotionCoreMachineDisplay.Aligned state)
    (document : NotionCoreSourceDocument.Document)
    (accepted : materializeDocument state = some document)
    (block : NotionCoreSliceForest.Block) (member : block ∈ state.forest)
    (source : Block) (extracted : materializeBlock state block = some source) :
    source ∈ document := by
  have found := NotionCoreMachineClient.find_block_member state.forest aligned.1 block member
  have displayed : block.id ∈ state.display :=
    ((NotionCoreDisplayOrder.shown_member _ _).mp
      (aligned.2.2.mem_iff.mpr (List.mem_map.mpr ⟨block,member,rfl⟩))).1
  obtain ⟨value,valueMember,lookup⟩ :=
    mapM_member_input _ state.display document accepted block.id displayed
  rw [materializeEntry_stored state block.id block found, extracted] at lookup
  cases lookup
  exact valueMember

/-- Once the source-selected old slice has been materialized, global slot
uniqueness identifies the document's searched owner with that same block. -/
theorem owner_of_materialized_slice (document : NotionCoreSourceDocument.Document)
    (unique : (NotionCoreInvariant.addresses (NotionCoreSourceDocument.project document)).Nodup)
    (source : Block) (member : source ∈ document) (origin : Address)
    (present : origin ∈ source.traversal) :
    NotionCoreSourceDocument.owner document origin = some source := by
  cases found : NotionCoreSourceDocument.owner document origin with
  | none =>
    have absent := List.find?_eq_none.mp found source member
    simp [NotionCoreSourceDocument.owns,present] at absent
  | some other =>
    obtain ⟨otherMember,otherPresent⟩ := NotionCoreSourceDocument.owner_some found
    have same := NotionCoreSourceGuards.owner_unique unique member otherMember present otherPresent
    exact congrArg some same.symm

/-- The selected chain's cut materializes the kept part of the source
document split: the slices before the cut and the left part of the cut slice. -/
theorem materialize_source_cut (state raw : State)
    (part : NotionCoreMachinePartition.Partitioned state)
    (block : NotionCoreSliceForest.Block) (member : block ∈ state.forest)
    (pre post : List Ref) (ref : Ref) (title : NotionCoreSliceForest.Tree) (origin marker : Address)
    (tree : NotionCoreSliceForest.preorderTree block.title = pre ++ ref :: post)
    (titleTree : NotionCoreSliceForest.preorderTree title = pre ++ [leftRef ref marker])
    (lead tail : List Cell) (cell : Cell)
    (refCell : ref = ⟨cell.slice.start,tail.head?.map (fun next => next.slice.start)⟩)
    (cellStop : cell.slice.stop = tail.head?.map (fun next => next.slice.start))
    (oldPhysical : physical state cell.slice.start.1 = flatten (lead ++ cell :: tail))
    (physicalHeld : origin ∈ cell.physical.map Atom.address)
    (sameInstance : marker.1 = cell.slice.start.1) (originInst : origin.1 = cell.slice.start.1)
    (unique : ∀ key, ((physical state key).map Atom.address).Nodup)
    (rawUnique : ∀ key, ((physical raw key).map Atom.address).Nodup)
    (rawExists : ∀ key, state.instances.any (fun entry => entry.1 == key) = true →
      raw.instances.any (fun entry => entry.1 == key) = true)
    (changed : physical raw cell.slice.start.1 = NotionCorePartition.spliceAfterBy Atom.address
      origin [boundary marker] (physical state cell.slice.start.1))
    (frames : ∀ key, key ≠ cell.slice.start.1 → physical raw key = physical state key)
    (source : Block) (old : materializeBlock state block = some source)
    (blockUnique : source.traversal.Nodup) :
    materializeBlock raw {block with title := title} =
        some {source with slices := (NotionCoreSource.splitSlices origin marker source.slices).1} ∧
      ∃ preS postS, source.slices = preS ++ cell.slice :: postS ∧
        (∀ slice ∈ preS ++ postS, origin ∉ slice.traversal) ∧
        sliceAtoms raw (rightRef ref marker) =
          some (cell.slice.atoms.drop (cell.slice.traversal.idxOf origin)) ∧
        post.mapM (fun ref => do pure (⟨ref.start,← sliceAtoms raw ref,ref.stop⟩ : Slice)) = some postS := by
  have present : origin ∈ cell.slice.traversal := NotionCorePartition.traversal_of_physical physicalHeld
  obtain ⟨extracted,name,instEq⟩ := materialized_slices state block source old
  unfold NotionCoreMachineClient.materialize at extracted
  rw [tree] at extracted
  obtain ⟨preS,refS,postS,preRead,refRead,postRead,slicesEq⟩ := mapM_split _ pre post ref _ extracted
  have existsCell : state.instances.any (fun entry => entry.1 == cell.slice.start.1) = true := by
    obtain ⟨atoms,atomsRead⟩ : ∃ atoms, sliceAtoms state ref = some atoms := by
      cases h : sliceAtoms state ref with
      | none => simp [h] at refRead
      | some atoms => exact ⟨atoms,rfl⟩
    have stored := (NotionCoreMachineClient.slice_storage state ref atoms atomsRead).1
    simpa [refCell] using stored
  have cellRead := NotionCoreMachineSlices.sliceAtoms_cell state lead tail cell existsCell oldPhysical (unique _)
  have refEq : refS = cell.slice := by
    rw [refCell, cellRead] at refRead
    simp at refRead
    rw [← refRead, ← cellStop]
  subst refS
  have whole : (preS.flatMap Slice.traversal ++ (cell.slice.traversal ++ postS.flatMap Slice.traversal)).Nodup := by
    simpa [NotionCoreSource.Block.traversal, slicesEq, List.flatMap_append] using blockUnique
  obtain ⟨_,rest,apart⟩ := List.nodup_append.mp whole
  obtain ⟨_,_,apartAfter⟩ := List.nodup_append.mp rest
  have absentPre : ∀ slice ∈ preS, origin ∉ slice.traversal := fun slice member held =>
    apart origin (List.mem_flatMap.mpr ⟨slice,member,held⟩) origin (List.mem_append_left _ present) rfl
  have absentPost : ∀ slice ∈ postS, origin ∉ slice.traversal := fun slice member held =>
    apartAfter origin present origin (List.mem_flatMap.mpr ⟨slice,member,held⟩) rfl
  have physicalPresent : origin ∈ (physical state cell.slice.start.1).map Atom.address := by
    rw [oldPhysical]
    obtain ⟨atom,atomMember,equal⟩ := List.mem_map.mp physicalHeld
    exact List.mem_map.mpr ⟨atom,List.mem_flatMap.mpr ⟨cell,by simp,atomMember⟩,equal⟩
  have keep (refs : List Ref) (slices : List Slice) (inside : ∀ r ∈ refs, r ∈ NotionCoreSliceForest.preorderTree block.title)
      (read : refs.mapM (fun ref => do pure (⟨ref.start,← sliceAtoms state ref,ref.stop⟩ : Slice)) = some slices)
      (outside : ∀ slice ∈ slices, origin ∉ slice.traversal) :
      refs.mapM (fun ref => do pure (⟨ref.start,← sliceAtoms raw ref,ref.stop⟩ : Slice)) = some slices := by
    apply mapM_keep refs _ _ slices read
    intro r rMember slice sliceRead
    cases atoms : sliceAtoms state r with
    | none => simp [atoms] at sliceRead
    | some found =>
      have sliceEq : slice = ⟨r.start,found,r.stop⟩ := by simpa [atoms] using sliceRead.symm
      subst slice
      have sliceMember : (⟨r.start,found,r.stop⟩ : Slice) ∈ slices :=
        mapM_output_member _ refs slices read r rMember _ sliceRead
      have rawRead := untouched_ref state raw part block member r (inside r rMember) found atoms
        cell.slice.start.1 origin marker originInst unique rawUnique rawExists physicalPresent changed frames
        (outside _ sliceMember)
      simp [rawRead]
  have preRaw := keep pre preS (fun r member => by rw [tree]; simp [member]) preRead absentPre
  have postRaw := keep post postS (fun r member => by rw [tree]; simp [member]) postRead absentPost
  have newExists := rawExists cell.slice.start.1 existsCell
  have halves := split_slice_extraction state raw lead tail cell origin marker oldPhysical (unique _)
    physicalHeld sameInstance changed newExists (rawUnique _)
  simp only at halves
  have leftRead : sliceAtoms raw (leftRef ref marker) =
      some (cell.slice.atoms.take (cell.slice.traversal.idxOf origin)) := by
    rw [refCell]; exact halves.1
  have rightRead : sliceAtoms raw (rightRef ref marker) =
      some (cell.slice.atoms.drop (cell.slice.traversal.idxOf origin)) := by
    rw [refCell]; exact halves.2
  have cut := NotionCoreSource.splitSlices_focus origin marker preS cell.slice postS absentPre present
  constructor
  · have titleRead : NotionCoreMachineClient.materialize raw title = some
        (preS ++ [(NotionCoreSource.splitSlice cell.slice (cell.slice.traversal.idxOf origin) marker).1]) := by
      unfold NotionCoreMachineClient.materialize
      rw [titleTree]
      apply mapM_append_some _ _ _ _ _ preRaw
      simp only [List.mapM_cons, List.mapM_nil, leftRead]
      simp [NotionCoreSource.splitSlice, leftRef, refCell]
    cases source
    simp only at name instEq slicesEq
    subst name instEq slicesEq
    simp [materializeBlock, titleRead, cut]
  · refine ⟨preS,postS,slicesEq,?_,?_,postRaw⟩
    · intro slice member
      rcases List.mem_append.mp member with inPre | inPost
      · exact absentPre slice inPre
      · exact absentPost slice inPost
    · exact rightRead

/-- Display materialization composes checked local extraction proofs through
an actual ID-preserving forest change. Tombstones keep their names and stay
tombstones. No document-output equation is input. -/
theorem materializeDocument_title_map (state next : State)
    (changeTree : NotionCoreSliceForest.Block → NotionCoreSliceForest.Block)
    (ids : ∀ block, (changeTree block).id = block.id)
    (forest : next.forest = state.forest.map changeTree)
    (display : next.display = state.display)
    (changeSource : Block → Block)
    (tombstones : ∀ bid, state.forest.find? (fun block => block.id == bid) = none →
      changeSource ⟨bid,bid,[]⟩ = ⟨bid,bid,[]⟩)
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
  have nextFind : next.forest.find? (fun block => block.id == bid) =
      (state.forest.find? (fun block => block.id == bid)).map changeTree := by
    rw [forest, find_title_map state.forest changeTree ids bid]
  cases found : state.forest.find? (fun block => block.id == bid) with
  | none =>
    rw [materializeEntry_tombstone state bid found] at selected
    cases selected
    rw [materializeEntry_tombstone next bid (by rw [nextFind, found]; rfl), tombstones bid found]
  | some block =>
    rw [materializeEntry_stored state bid block found] at selected
    rw [materializeEntry_stored next bid (changeTree block) (by rw [nextFind, found]; rfl)]
    exact localExtract block (List.mem_of_find?_eq_some found) source selected

/-- Complete display-ordered split materialization from the actual physical
splice and the chain cut derived from the forest search. No next document,
owner, extraction, or rendered-output equation is assumed. -/
theorem split_document_from_context (state raw next : State)
    (part : NotionCoreMachinePartition.Partitioned state)
    (aligned : NotionCoreMachineDisplay.Aligned state)
    (document : NotionCoreSourceDocument.Document)
    (old : materializeDocument state = some document)
    (docUnique : (NotionCoreInvariant.addresses (NotionCoreSourceDocument.project document)).Nodup)
    (before after : NotionCoreSliceForest.Forest) (selected : NotionCoreSliceForest.Block)
    (target : Nat) (origin marker : Address) (key : Nat × Nat)
    (markerEq : marker = (origin.1, .event key))
    (forest : state.forest = (before ++ selected :: after) ++ [⟨target,NotionCoreSliceForest.freshTitle target⟩])
    (targetFresh : target ∉ (before ++ selected :: after).map NotionCoreSliceForest.Block.id)
    (pre post : List Ref) (ref : Ref) (title moved : NotionCoreSliceForest.Tree)
    (tree : NotionCoreSliceForest.preorderTree selected.title = pre ++ ref :: post)
    (titleTree : NotionCoreSliceForest.preorderTree title = pre ++ [leftRef ref marker])
    (movedTree : NotionCoreSliceForest.preorderTree moved = rightRef ref marker :: post)
    (lead tail : List Cell) (cell : Cell)
    (refCell : ref = ⟨cell.slice.start,tail.head?.map (fun next => next.slice.start)⟩)
    (cellStop : cell.slice.stop = tail.head?.map (fun next => next.slice.start))
    (oldPhysical : physical state cell.slice.start.1 = flatten (lead ++ cell :: tail))
    (originHeld : origin ∈ cell.physical.map Atom.address)
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
      (before ++ {selected with title := title} :: after) ++
      [⟨target,.node (NotionCoreSliceForest.titleRef target) (.cons moved .nil)⟩])
    (targetEmpty : physical state target = NotionCoreSliceForest.emptyPhysical target)
    (targetDistinct : target ≠ cell.slice.start.1) :
    ∃ result, materializeDocument next = some result ∧
      NotionCoreSourceDocument.step document (.split origin key target) = some result := by
  have originPresent : origin ∈ cell.slice.traversal := NotionCorePartition.traversal_of_physical originHeld
  have physicalOrigin : origin ∈ (physical state cell.slice.start.1).map Atom.address := by
    rw [oldPhysical]
    obtain ⟨atom,atomMember,equal⟩ := List.mem_map.mp originHeld
    exact List.mem_map.mpr ⟨atom,List.mem_flatMap.mpr ⟨cell,by simp,atomMember⟩,equal⟩
  have position := NotionCoreMachineDocumentInvariant.physical_positions state _ origin physicalOrigin
  let destination : NotionCoreSliceForest.Block := ⟨target,NotionCoreSliceForest.freshTitle target⟩
  let rightTree : NotionCoreSliceForest.Block :=
    ⟨target,.node (NotionCoreSliceForest.titleRef target) (.cons moved .nil)⟩
  have selectedMember : selected ∈ state.forest := by rw [forest]; simp
  have destMember : destination ∈ state.forest := by rw [forest]; simp [destination]
  obtain ⟨source,sourceMat⟩ := NotionCoreMachineDocument.materializeBlock_total state part unique selected
    selectedMember
  have sourceMember := materialized_member state aligned document old selected selectedMember source sourceMat
  have sourceUnique := NotionCoreSourceGuards.block_unique docUnique sourceMember
  obtain ⟨sourceCut,preS,postS,slicesEq,absent,rightRead,postRaw⟩ := materialize_source_cut state raw part
    selected selectedMember pre post ref title origin marker tree titleTree lead tail cell refCell cellStop
    oldPhysical originHeld sameMarker originInst unique rawUnique rawExists changed frames source sourceMat
    sourceUnique
  have sourceHeld : origin ∈ source.traversal := by
    simp [NotionCoreSource.Block.traversal, slicesEq, originPresent]
  have sourceOwner := owner_of_materialized_slice document docUnique source sourceMember origin sourceHeld
  have sourceId : source.id = selected.id := (materialized_slices state selected source sourceMat).2.1
  have targetExists : state.instances.any (fun entry => entry.1 == target) = true := by
    have owned : (target,NotionCoreSliceForest.titleRef target) ∈ NotionCoreForestRefs.ownedRefs state.forest :=
      List.mem_flatMap.mpr ⟨destination,destMember,by simp [destination,NotionCoreSliceForest.freshTitle,
        NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.preorderChildren]⟩
    simpa [NotionCoreSliceForest.titleRef] using part.refsExist _ owned
  have titleRead := NotionCoreMachineSlices.empty_title_atoms state target targetExists targetEmpty
  have destMat : materializeBlock state destination = some (NotionCoreSourceDocument.freshBlock target target) := by
    simp only [materializeBlock, NotionCoreMachineClient.materialize, destination,
      NotionCoreSliceForest.freshTitle, NotionCoreSliceForest.preorderTree,
      NotionCoreSliceForest.preorderChildren, List.mapM_cons, List.mapM_nil, titleRead]
    rfl
  have destDocMember := materialized_member state aligned document old destination destMember _ destMat
  have docIds : (document.map Block.id).Nodup := by
    rw [materialized_ids state document old]
    exact aligned.2.1
  have destFound := source_find_member document docIds (NotionCoreSourceDocument.freshBlock target target) destDocMember
  change document.find? (fun block => block.id == target) = some (NotionCoreSourceDocument.freshBlock target target) at destFound
  have sourceTarget : selected.id ≠ target := by
    intro equal
    exact targetFresh (by simp [← equal])
  have oldBaseUnique : ((before ++ selected :: after).map NotionCoreSliceForest.Block.id).Nodup := by
    have oldUnique : (state.forest.map NotionCoreSliceForest.Block.id).Nodup := aligned.1
    rw [forest,List.map_append] at oldUnique
    exact (List.nodup_append.mp oldUnique).1
  have agrees : NotionCoreSource.InstanceAgrees origin source.slices := by
    intro slice member held
    rw [slicesEq] at member
    rcases List.mem_append.mp member with inPre | inRest
    · exact absurd held (absent slice (List.mem_append_left _ inPre))
    · rcases List.mem_cons.mp inRest with rfl | inPost
      · exact originInst.symm
      · exact absurd held (absent slice (List.mem_append_right _ inPost))
  let cut := NotionCoreSource.splitSlices origin marker source.slices
  let changeTree := fun block : NotionCoreSliceForest.Block =>
    if block.id = selected.id then {block with title := title}
    else if block.id = target then rightTree else block
  let changeSource := fun block : Block =>
    if block.id = source.id then {block with slices := cut.1}
    else if block.id = target then {block with slices := block.slices ++ cut.2} else block
  have treeMap : next.forest = state.forest.map changeTree := by
    rw [forest,nextForest]
    simp only [List.map_append,List.map_cons,List.map_nil]
    have uniqueMapped : (before.map NotionCoreSliceForest.Block.id ++ selected.id ::
        after.map NotionCoreSliceForest.Block.id).Nodup := by simpa using oldBaseUnique
    have untouched (xs : NotionCoreSliceForest.Forest)
        (noSource : selected.id ∉ xs.map NotionCoreSliceForest.Block.id)
        (noTarget : target ∉ xs.map NotionCoreSliceForest.Block.id) : xs.map changeTree = xs := by
      conv_rhs => rw [← List.map_id xs]
      apply List.map_congr_left
      intro block member
      have first : block.id ≠ selected.id := fun equal => noSource (List.mem_map.mpr ⟨block,member,equal⟩)
      have second : block.id ≠ target := fun equal => noTarget (List.mem_map.mpr ⟨block,member,equal⟩)
      simp [changeTree,first,second]
    have sourceNotBefore : selected.id ∉ before.map NotionCoreSliceForest.Block.id := by
      have separated := (List.nodup_append.mp uniqueMapped).2.2
      exact fun member => separated selected.id member selected.id (by simp) rfl
    have sourceNotAfter : selected.id ∉ after.map NotionCoreSliceForest.Block.id :=
      (List.nodup_cons.mp (List.nodup_append.mp uniqueMapped).2.1).1
    rw [untouched before sourceNotBefore (fun member => targetFresh (by simp [member])),
      untouched after sourceNotAfter (fun member => targetFresh (by simp [member]))]
    simp [changeTree,rightTree,Ne.symm sourceTarget]
  have treeIds : ∀ block, (changeTree block).id = block.id := by
    intro block
    simp only [changeTree]
    split
    · rfl
    · split
      · rename_i equal
        exact equal.symm
      · rfl
  have nextMatFrame (b : NotionCoreSliceForest.Block) : materializeBlock next b = materializeBlock raw b := by
    simp only [materializeBlock,NotionCoreMachineClient.materialize,sliceAtoms,physical,getInstance,
      nextInstances]
  have localExtract : ∀ block ∈ state.forest, ∀ value,
      materializeBlock state block = some value →
      materializeBlock next (changeTree block) = some (changeSource value) := by
    intro block member value mat
    have valueId := (materialized_slices state block value mat).2.1
    rw [nextMatFrame]
    by_cases isSource : block.id = selected.id
    · have equal := block_eq_of_id state.forest aligned.1 block selected member selectedMember isSource
      subst block
      have valueEq : value = source := Option.some.inj (mat.symm.trans sourceMat)
      subst value
      simpa [changeTree,changeSource] using sourceCut
    · by_cases isTarget : block.id = target
      · have equal := block_eq_of_id state.forest aligned.1 block destination member destMember isTarget
        subst block
        have valueEq : value = NotionCoreSourceDocument.freshBlock target target :=
          Option.some.inj (mat.symm.trans destMat)
        subst value
        have rawTitle : sliceAtoms raw (NotionCoreSliceForest.titleRef target) = some [] :=
          NotionCoreMachineSlices.empty_title_atoms raw target (rawExists target targetExists)
            (by rw [frames target targetDistinct]; exact targetEmpty)
        have movedRead : NotionCoreMachineClient.materialize raw rightTree.title = some
            (⟨(target,.start),[],none⟩ :: (NotionCoreSource.splitSlice cell.slice
              (cell.slice.traversal.idxOf origin) marker).2 :: postS) := by
          unfold NotionCoreMachineClient.materialize
          simp only [rightTree, NotionCoreSliceForest.preorderTree, NotionCoreSliceForest.preorderChildren,
            List.append_nil]
          rw [movedTree]
          simp only [List.mapM_cons, rawTitle, rightRead, postRaw]
          simp [NotionCoreSliceForest.titleRef, NotionCoreSource.splitSlice, rightRef, refCell, cellStop]
        have cutEq := NotionCoreSource.splitSlices_focus origin marker preS cell.slice postS
          (fun slice member => absent slice (List.mem_append_left _ member)) originPresent
        have notSource : target ≠ source.id := by rw [sourceId]; exact Ne.symm sourceTarget
        simp [changeTree, changeSource, isSource, notSource, materializeBlock, movedRead, cut,
          slicesEq, cutEq, NotionCoreSourceDocument.freshBlock, destination, rightTree]
      · have valueMember := materialized_member state aligned document old block member value mat
        have notOwned : NotionCoreSourceDocument.owns value origin = false := by
          cases owned : NotionCoreSourceDocument.owns value origin
          · rfl
          · have held : origin ∈ value.traversal := by simpa [NotionCoreSourceDocument.owns] using owned
            have same := NotionCoreSourceGuards.owner_unique docUnique sourceMember valueMember sourceHeld held
            exact absurd (valueId.symm.trans ((congrArg Block.id same).symm.trans sourceId)) isSource
        have updated := NotionCoreMachineDocumentInsert.materializeBlock_insert state raw part block value member mat
          cell.slice.start.1 origin [boundary marker] originInst unique rawUnique rawExists
          physicalOrigin changed frames
        rw [notOwned] at updated
        have notSource : value.id ≠ source.id := by rw [valueId,sourceId]; exact isSource
        have notTarget : value.id ≠ target := by rw [valueId]; exact isTarget
        simpa [changeTree,changeSource,isSource,isTarget,notSource,notTarget] using updated
  have tombstones : ∀ bid, state.forest.find? (fun block => block.id == bid) = none →
      changeSource ⟨bid,bid,[]⟩ = ⟨bid,bid,[]⟩ := by
    intro bid absent
    have notSource : bid ≠ source.id := by
      intro equal
      apply List.find?_eq_none.mp absent selected selectedMember
      rw [equal, sourceId]
      simp
    have notTarget : bid ≠ target := by
      intro equal
      apply List.find?_eq_none.mp absent destination destMember
      simp [destination, equal]
    simp [changeSource,notSource,notTarget]
  refine ⟨document.map changeSource,
    materializeDocument_title_map state next changeTree treeIds treeMap nextDisplay changeSource tombstones
      localExtract document old,?_⟩
  have sourceIdTarget : source.id ≠ target := by rw [sourceId]; exact sourceTarget
  subst markerEq
  simp [NotionCoreSourceDocument.step,position,sourceOwner,destFound,sourceIdTarget,agrees,
    NotionCoreSourceDocument.EmptyRoot,NotionCoreSourceDocument.freshBlock,changeSource,cut]

/-- Honest canonical split refines the existing two-command source-document
transaction. The displayed predecessor is the requested block, whereas the
chain to cut is recovered by the actual origin/marker searches. -/
theorem canonical_split_source_step_with_execution_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
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
        (NotionCorePhysicalReplay.markerKey tx.id)
        (blockName (.issued tx.id))) = some result ∧
      NotionCoreSourceDocument.Execution document (NotionCoreMachineCommands.commands tx) result := by
  have creators := NotionCoreMachineNetwork.creator_reachable reachable
  have payloadReach := NotionCoreCreatorNetwork.payload_reachable creators
  obtain ⟨checked,checkedReplay,part,shape,_⟩ :=
    NotionCoreMachineHonestReplay.honest_prefix_reconstruct_version network reachable version closed pre (tx :: suffix) position
  have equal : checked = state := Option.some.inj (checkedReplay.symm.trans accepted)
  subst checked
  obtain ⟨freshInstance,freshBlock⟩ := NotionCoreMachineCanonicalCreate.canonical_destination_fresh_version
    network creators version closed pre suffix tx position state accepted
  obtain ⟨created,rows,createStep,integrated,stage,rawForest,emptyTarget,_⟩ :=
    NotionCoreMachineMarkerProgress.canonical_split_marker_phase_version network creators version closed pre suffix tx position
      state accepted part block inst origin payload
  let raw := putInstance created (blockName inst) {getInstance created (blockName inst) with rows := rows}
  let marker := NotionCorePhysicalReplay.address (blockName inst) tx.id
  let address := NotionCorePhysicalReplay.originAddress (blockName inst) origin
  let target := blockName (.issued tx.id)
  have createShape := NotionCoreMachineCanonicalCreate.fresh_create_shape state created (.issued tx.id)
    (some block) freshInstance freshBlock createStep
  have createPart := NotionCoreMachinePartitionCreate.create_preserves_partitioned state created
    (.issued tx.id) (some block) part freshInstance freshBlock.1 createStep
  have aligned := NotionCoreMachineDisplay.replay_aligned {} state pre
    (by simp [NotionCoreMachineDisplay.Aligned,NotionCoreDisplayOrder.Aligned,NotionCoreDisplayOrder.names,
      NotionCoreDisplayOrder.shown]) accepted
  have createAligned := NotionCoreMachineDisplay.operation_aligned state created _ aligned createStep
  have previousMember := NotionCoreMachineBlockPresence.canonical_required_block_version
    network creators version closed pre suffix tx position state accepted block
      (by simp [payload,NotionCoreCreatorNetwork.requiredBlocks])
  obtain ⟨intermediate,createdDoc,createDocStep⟩ := NotionCoreMachineDocumentCreate.fresh_create_document
    state created (.issued tx.id) (some block) freshInstance freshBlock createStep aligned document old (by
      intro key equality
      have keyEq : key = block := Option.some.inj equality.symm
      subst key
      exact previousMember)
  have existsOld := NotionCoreMachineCreatorPresence.canonical_required_instance_version network creators version closed pre suffix tx
    position state accepted inst (by simp [payload,NotionCoreCreatorNetwork.requiredBlocks])
  have instDistinct : blockName inst ≠ target := by
    obtain ⟨entry,member,equal⟩ := existsOld
    exact fun same => freshInstance entry member (equal.trans same)
  have storage := NotionCoreMachineCanonicalCreate.fresh_create_storage state created (.issued tx.id)
    (some block) freshInstance freshBlock createStep
  have sameStorage : getInstance created (blockName inst) = getInstance state (blockName inst) := by
    simpa [target,instDistinct] using storage (blockName inst)
  obtain ⟨originalRows,originalIntegrated,originalPhysical,fresh,originPhysical⟩ :=
    NotionCoreMachineMarkerProgress.canonical_marker_physical_version network payloadReach version closed pre suffix tx position
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
  have physicalFrame := NotionCoreMachineCanonicalCreate.fresh_create_physical state created (.issued tx.id)
    (some block) freshInstance freshBlock createStep
  have createdUnique : ∀ key, ((physical created key).map Atom.address).Nodup := by
    have uniqueOld := NotionCoreMachineMarkerProgress.canonical_physical_unique_all_version network payloadReach version closed pre
      (tx :: suffix) position state accepted
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
    exact freshBlock.1 b member equal
  have freshMarker : NotionCoreSliceForest.FreshMarker state.forest marker := by
    intro b member boundaryMember
    obtain ⟨ref,refMember,equal⟩ := List.mem_map.mp boundaryMember
    apply stage.fresh (b.id,ref)
    · apply List.mem_flatMap.mpr
      exact ⟨b,by rw [rawForest]; exact List.mem_append_left _ member,List.mem_map.mpr ⟨ref,refMember,rfl⟩⟩
    · exact equal
  have createdExists : ∃ entry ∈ created.instances, entry.1 = blockName inst := by
    obtain ⟨entry,member,equal⟩ := existsOld
    exact ⟨entry,createShape.1 ▸ List.mem_append_left _ member,equal⟩
  have rawExists : ∃ entry ∈ raw.instances, entry.1 = marker.1 :=
    (NotionCoreMachinePartitionUpdates.putInstance_exists_iff created (blockName inst)
      (blockName inst) {getInstance created (blockName inst) with rows := rows} createdExists).mpr createdExists
  have markerDistinct : marker.1 ≠ target := NotionCoreMachineMarkerProgress.marker_instance_ne_empty raw
    (blockName inst) target tx.id stage.present emptyTarget
  have chains : ∀ found ∈ state.forest, NotionCoreSliceForest.Chain found.title :=
    fun found member => (shape.1 found member).1
  obtain ⟨forest,atomic,_⟩ := NotionCoreMachinePartitionSplit.atomicSplit_partitioned
    raw state.forest marker target rawForest stage.partitioned stage.unique chains
      freshMarker freshTarget emptyTarget rawExists stage.present stage.fresh
  obtain ⟨before,chosen,after,refsBefore,ref,refsAfter,title,moved,context,tree,chosenContains,_,titleTree,
    _,movedTree,resultEq⟩ := NotionCoreSliceForest.atomicSplit_result (physical raw) marker target
      state.forest forest chains freshMarker freshTarget emptyTarget atomic
  have chosenCreated : chosen ∈ created.forest := by rw [createShape.2.1, context]; simp
  have chosenRaw : chosen ∈ raw.forest := by rw [rawForest, context]; simp
  have refInTree : ref ∈ NotionCoreSliceForest.preorderTree chosen.title := by rw [tree]; simp
  have oldOwned : (chosen.id,ref) ∈ NotionCoreForestRefs.ownedRefs created.forest :=
    List.mem_flatMap.mpr ⟨chosen,chosenCreated,List.mem_map.mpr ⟨ref,refInTree,rfl⟩⟩
  have rawOwned : (chosen.id,ref) ∈ NotionCoreForestRefs.ownedRefs raw.forest :=
    List.mem_flatMap.mpr ⟨chosen,chosenRaw,List.mem_map.mpr ⟨ref,refInTree,rfl⟩⟩
  obtain ⟨slice,startEq,stopEq,oldSlice,ownsOrigin⟩ := selected_marker_origin created raw createPart stage.partitioned
    (chosen.id,ref) oldOwned rawOwned address marker createdUnique stage.unique
    originPresent markerFresh changed stage.present chosenContains
  obtain ⟨lead,cell,tail,factor,refEq,cellStop⟩ := NotionCoreMachinePartition.ref_factor_chained created
    createPart (chosen.id,ref) oldOwned
  have refCell : ref = ⟨cell.slice.start,tail.head?.map (fun next => next.slice.start)⟩ := congrArg Prod.snd refEq
  change physical created ref.start.1 = _ at factor
  rw [refCell] at factor
  have existsCell : created.instances.any (fun entry => entry.1 == cell.slice.start.1) = true := by
    simpa [refCell] using createPart.refsExist (chosen.id,ref) oldOwned
  have extractCell := NotionCoreMachineSlices.sliceAtoms_cell created lead tail cell existsCell factor (createdUnique _)
  have sliceEq : slice = cell.slice := by
    have atomsEq := Option.some.inj (oldSlice.symm.trans (by simpa only [refCell] using extractCell))
    have start := startEq.trans (congrArg NotionCoreSliceForest.Ref.start refCell)
    have stop := (stopEq.trans (congrArg NotionCoreSliceForest.Ref.stop refCell)).trans cellStop.symm
    change Slice.mk slice.start slice.atoms slice.stop =
      Slice.mk cell.slice.start cell.slice.atoms cell.slice.stop
    rw [start, atomsEq, stop]
  subst slice
  have sameInst : cell.slice.start.1 = blockName inst := by
    have condition : ref.start.1 = marker.1 := by
      have conditions : ref.start.1 = marker.1 ∧
          (NotionCorePartition.extractIds (physical raw ref.start.1)
            ref.start ref.stop).contains (some marker) = true := by
        simpa only [NotionCoreSliceForest.contains,Bool.and_eq_true,decide_eq_true_eq] using chosenContains
      exact conditions.1
    simpa [refCell,marker,NotionCorePhysicalReplay.address] using condition
  let next : State := {raw with forest := forest}
  have transaction := NotionCoreMachineMarkerProgress.split_transaction_of_atomic state created tx block inst origin
    rows forest payload createStep integrated stage rawForest atomic
  have createdShape := NotionCoreMachineShape.fresh_create_shape_preserves state created (.issued tx.id)
    (some block) shape part freshInstance freshBlock createStep
  have docUnique := NotionCoreMachineDocumentInvariant.projected_addresses_unique created createPart createdUnique
    createdShape.2.2.2.2 createAligned intermediate createdDoc
  have originHeld : address ∈ cell.physical.map Atom.address :=
    (NotionCorePartition.slice_traversal_iff
      (NotionCoreMachineDocumentInvariant.physical_positions created _ address originPresent)).mp ownsOrigin
  have addressInst : address.1 = blockName inst := by cases origin <;> rfl
  obtain ⟨result,materialized,splitStep⟩ := split_document_from_context created raw next createPart
    createAligned intermediate createdDoc docUnique before after chosen target address marker
    (NotionCorePhysicalReplay.markerKey tx.id) (by rw [addressInst]; rfl)
    (by rw [createShape.2.1,context]) (by simpa [context] using freshTarget)
    refsBefore refsAfter ref title moved tree titleTree movedTree
    lead tail cell refCell cellStop factor originHeld
    (by simpa [marker,NotionCorePhysicalReplay.address] using sameInst.symm)
    (by cases origin <;> simpa [address,NotionCorePhysicalReplay.originAddress] using sameInst.symm)
    createdUnique stage.unique (by
      intro key oldExists
      have stored : ∃ entry ∈ created.instances, entry.1 = key := by simpa using oldExists
      simpa using (NotionCoreMachinePartitionUpdates.putInstance_exists_iff created (blockName inst) key
        {getInstance created (blockName inst) with rows := rows} createdExists).mpr stored)
    (by simpa [sameInst] using changed)
    (by intro key different; simp [raw,physical,NotionCoreMachineTables.getInstance_put,← sameInst,different])
    rfl (by unfold next raw putInstance; split <;> rfl) resultEq physicalFrame.1
    (by rw [sameInst]; exact Ne.symm instDistinct)
  have oldUnique := NotionCoreMachineMarkerProgress.canonical_physical_unique_all_version network payloadReach version closed pre
    (tx :: suffix) position state accepted
  have createGuard := NotionCoreMachineDocumentInvariant.accepted_source_guard state part oldUnique
    shape.2.2.2.2 aligned document intermediate old _ createDocStep
  have splitGuard := NotionCoreMachineDocumentInvariant.accepted_source_guard created createPart createdUnique
    createdShape.2.2.2.2 createAligned intermediate result createdDoc _ splitStep
  have execution := NotionCoreSourceDocument.Execution.cons createGuard createDocStep
    (NotionCoreSourceDocument.Execution.cons splitGuard splitStep (NotionCoreSourceDocument.Execution.nil result))
  exact ⟨next,intermediate,result,transaction,materialized,createDocStep,splitStep,
    by simpa [NotionCoreMachineCommands.commands,payload] using execution⟩

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
        (NotionCorePhysicalReplay.markerKey tx.id)
        (blockName (.issued tx.id))) = some result ∧
      NotionCoreSourceDocument.Execution document (NotionCoreMachineCommands.commands tx) result := by
  have issued := NotionCorePayloadNetwork.forget_reachable
    (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))
  exact canonical_split_source_step_with_execution_version network reachable
    (network.allocation.peers peer).received (NotionCoreIssuance.peers_closed issued peer)
    pre suffix tx position state accepted document old block inst origin payload

/-- Public atomic execution endpoint for history composition. -/
theorem canonical_split_execution_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (document : NotionCoreSourceDocument.Document)
    (old : materializeDocument state = some document)
    (block inst : NotionCorePayload.BlockKey) (origin : NotionCoreOriginTree.Origin)
    (payload : tx.payload = .split block inst origin) :
    ∃ next result, applyTransaction state tx = some next ∧ materializeDocument next = some result ∧
      NotionCoreSourceDocument.Execution document (NotionCoreMachineCommands.commands tx) result := by
  obtain ⟨next,_,result,transaction,materialized,_,_,execution⟩ := canonical_split_source_step_with_execution_version
    network reachable version closed pre suffix tx position state accepted document old block inst origin payload
  exact ⟨next,result,transaction,materialized,execution⟩

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
  have issued := NotionCorePayloadNetwork.forget_reachable
    (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))
  exact canonical_split_execution_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed issued peer) pre suffix tx position state accepted document old block inst origin payload

#print axioms canonical_split_execution_version
#print axioms canonical_split_source_step_with_execution_version
#print axioms canonical_split_execution
#print axioms canonical_split_source_step_with_execution
#print axioms split_document_from_context
#print axioms materialized_member
#print axioms owner_of_materialized_slice
#print axioms selected_marker_origin
#print axioms materializeDocument_title_map
#print axioms find_title_map
#print axioms split_slice_extraction
#print axioms materialize_source_cut
end Sal.MRDTs.Instances.NotionCoreMachineDocumentSplit
