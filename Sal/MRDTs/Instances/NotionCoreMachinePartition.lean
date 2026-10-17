import Sal.MRDTs.Instances.NotionCoreForestRefs
import Sal.MRDTs.Instances.NotionCoreMachineSlices
import Sal.MRDTs.Instances.NotionCoreMachineRouting

/-! Correspondence between every stored forest reference and physical interval
cells, including empty title roots. Enumeration is per-instance physical order;
forest Map order and displayed block order are different enumerations. This
structural invariant is not yet derived for all reachable machine states. -/
namespace Sal.MRDTs.Instances.NotionCoreMachinePartition
open NotionCoreSpec (Address)
open NotionCoreSource (Atom)
open NotionCorePartition (Cell flatten)
open NotionCoreSliceForest (Ref)
open NotionCoreMachine
open NotionCoreForestRefs (ownedRefs)

def cellRefs : List Cell → List (Nat × Ref)
  | [] => []
  | cell :: rest => (cell.owner, ⟨cell.slice.start, rest.head?.map (fun next => next.slice.start)⟩) :: cellRefs rest

theorem cellRefs_member (cells : List Cell) (owned : Nat × Ref) :
    owned ∈ cellRefs cells ↔ ∃ before cell after,
      cells = before ++ cell :: after ∧
      owned = (cell.owner, ⟨cell.slice.start, after.head?.map (fun next => next.slice.start)⟩) := by
  constructor
  · intro member
    induction cells with
    | nil => simp [cellRefs] at member
    | cons cell rest ih =>
      rcases List.mem_cons.mp member with same | later
      · exact ⟨[], cell, rest, rfl, same⟩
      · obtain ⟨before, found, after, shape, equal⟩ := ih later
        exact ⟨cell :: before, found, after, by simp [shape], equal⟩
  · rintro ⟨before, cell, after, rfl, rfl⟩
    induction before with
    | nil => simp [cellRefs]
    | cons head rest ih => exact List.mem_cons_of_mem _ ih

/-- The reference permutation names actual owner/start/stop triples. Owners
need not be distinct: after a split and a merge back, one block owns two cells
of one instance. -/
structure Partitioned (state : State) : Prop where
  refsExist : ∀ owned ∈ ownedRefs state.forest,
    ∃ entry ∈ state.instances, entry.1 = owned.2.start.1
  partitions : ∀ inst, (∃ entry ∈ state.instances, entry.1 = inst) →
    ∃ cells, physical state inst = flatten cells ∧
      ((ownedRefs state.forest).filter (fun owned => owned.2.start.1 == inst)).Perm (cellRefs cells)

theorem initial_partitioned : Partitioned {} := by
  constructor
  · simp [ownedRefs]
  · simp

theorem ref_factor (state : State) (partitioned : Partitioned state)
    (owned : Nat × Ref) (member : owned ∈ ownedRefs state.forest) :
    ∃ before cell after,
      physical state owned.2.start.1 = flatten (before ++ cell :: after) ∧
      owned = (cell.owner, ⟨cell.slice.start, after.head?.map (fun next => next.slice.start)⟩) := by
  obtain ⟨cells, physicalEq, permutation⟩ := partitioned.partitions owned.2.start.1
    (partitioned.refsExist owned member)
  have matched := permutation.mem_iff.mp (List.mem_filter.mpr ⟨member, by simp⟩)
  obtain ⟨before, cell, after, shape, equal⟩ := (cellRefs_member cells owned).mp matched
  exact ⟨before, cell, after, shape ▸ physicalEq, equal⟩

/-- Every actual forest slice passes checked extraction when its endpoints
are the represented next physical boundaries. No extracted value is assumed. -/
theorem ref_extracts (state : State) (partitioned : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (owned : Nat × Ref) (member : owned ∈ ownedRefs state.forest) :
    ∃ atoms, sliceAtoms state owned.2 = some atoms := by
  obtain ⟨before, cell, after, physicalEq, equal⟩ := ref_factor state partitioned owned member
  have existsInstance : state.instances.any (fun entry => entry.1 == owned.2.start.1) = true := by
    simpa using partitioned.refsExist owned member
  subst owned
  exact ⟨cell.slice.atoms, NotionCoreMachineSlices.sliceAtoms_cell state before after cell
    existsInstance physicalEq (unique cell.slice.start.1)⟩

theorem extracted_validBounds (state : State) (ref : Ref) (atoms : List Atom)
    (extracted : sliceAtoms state ref = some atoms) : validBounds state ref = true := by
  cases stop : ref.stop <;> simp [sliceAtoms, validBounds, stop] at extracted ⊢
  all_goals simp_all

theorem partition_bounds (state : State) (partitioned : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup) :
    validForestBounds state = true := by
  apply List.all_eq_true.mpr
  intro block present
  apply List.all_eq_true.mpr
  intro ref member
  have owned : (block.id,ref) ∈ ownedRefs state.forest := by
    exact List.mem_flatMap.mpr ⟨block, present, List.mem_map.mpr ⟨ref, member, rfl⟩⟩
  obtain ⟨atoms, extracted⟩ := ref_extracts state partitioned unique (block.id,ref) owned
  exact extracted_validBounds state ref atoms extracted

private theorem extractIds_cell (before after : List Cell) (cell : Cell)
    (unique : ((flatten (before ++ cell :: after)).map Atom.address).Nodup) :
    NotionCorePartition.extractIds (flatten (before ++ cell :: after)) cell.slice.start
      (after.head?.map (fun next => next.slice.start)) = NotionCorePartition.ids cell.slice.atoms := by
  have factor : flatten (before ++ cell :: after) =
      (flatten before ++ NotionCorePartition.boundary cell.slice.start :: cell.slice.atoms) ++ flatten after := by
    simp [flatten, Cell.physical, List.append_assoc]
  rw [factor] at unique ⊢
  apply NotionCorePartition.extractIds_factor _ _ _ _ _ ?_ unique
  cases after with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons next rest =>
      exact Or.inr ⟨next.slice.start, next.slice.atoms ++ flatten rest, rfl, rfl⟩

/-- A physical item which is not already a stored boundary lies inside an
actual forest reference. The search witness is recovered from the partition;
the caller supplies neither its owner nor a successful search result. -/
theorem containing_ref (state : State) (partitioned : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (marker : Address)
    (existsInstance : ∃ entry ∈ state.instances, entry.1 = marker.1)
    (present : marker ∈ (physical state marker.1).map Atom.address)
    (newBoundary : ∀ owned ∈ ownedRefs state.forest, owned.2.start ≠ marker) :
    ∃ owned ∈ ownedRefs state.forest,
      NotionCoreSliceForest.contains (physical state) owned.2 marker = true := by
  obtain ⟨cells, physicalEq, permutation⟩ :=
    partitioned.partitions marker.1 existsInstance
  have representation : NotionCorePartition.Represents
      ⟨physical state marker.1, cells.map Cell.entry⟩ cells :=
    ⟨physicalEq, rfl, unique marker.1⟩
  obtain ⟨cell, ⟨member, active⟩, _⟩ :=
    NotionCorePartition.physical_unique_owner marker representation present
  obtain ⟨before, after, shape⟩ := List.append_of_mem member
  let owned : Nat × Ref :=
    (cell.owner, ⟨cell.slice.start, after.head?.map (fun next => next.slice.start)⟩)
  have inCells : owned ∈ cellRefs cells :=
    (cellRefs_member cells owned).mpr ⟨before, cell, after, shape, rfl⟩
  have inFilter := List.mem_filter.mp (permutation.mem_iff.mpr inCells)
  have sameInstance : cell.slice.start.1 = marker.1 := by simpa [owned] using inFilter.2
  have interior : marker ∈ cell.slice.atoms.map Atom.address := by
    rcases List.mem_cons.mp active with equal | inside
    · exact False.elim (newBoundary owned inFilter.1 equal.symm)
    · exact inside
  refine ⟨owned, inFilter.1, ?_⟩
  have extracted : NotionCorePartition.extractIds (physical state cell.slice.start.1)
      cell.slice.start (after.head?.map (fun next => next.slice.start)) =
      NotionCorePartition.ids cell.slice.atoms := by
    rw [sameInstance, physicalEq, shape]
    apply extractIds_cell
    simpa [physicalEq, shape] using unique marker.1
  simp only [NotionCoreSliceForest.contains, owned, sameInstance, decide_true, Bool.true_and]
  rw [← sameInstance, extracted]
  simpa [NotionCorePartition.ids] using interior

theorem containing_tree_ref (state : State) (partitioned : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (marker : Address)
    (existsInstance : ∃ entry ∈ state.instances, entry.1 = marker.1)
    (present : marker ∈ (physical state marker.1).map Atom.address)
    (newBoundary : ∀ owned ∈ ownedRefs state.forest, owned.2.start ≠ marker) :
    ∃ block ∈ state.forest, ∃ ref ∈ NotionCoreSliceForest.preorderTree block.title,
      NotionCoreSliceForest.contains (physical state) ref marker = true := by
  obtain ⟨owned, ownedMember, contained⟩ :=
    containing_ref state partitioned unique marker existsInstance present newBoundary
  obtain ⟨block, blockMember, refMember⟩ := List.mem_flatMap.mp ownedMember
  obtain ⟨ref, treeMember, equal⟩ := List.mem_map.mp refMember
  subst owned
  exact ⟨block, blockMember, ref, treeMember, contained⟩

/-- Partition coverage supplies the actual recursive search witness and the
old endpoint checks. Thus neither successful search nor valid output bounds
are premises. Preservation of `Partitioned` through complete replay remains
separate from this structural progress theorem. -/
theorem splitForest_partition_progress (state : State) (partitioned : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (marker : Address)
    (existsInstance : ∃ entry ∈ state.instances, entry.1 = marker.1)
    (present : marker ∈ (physical state marker.1).map Atom.address)
    (newBoundary : ∀ owned ∈ ownedRefs state.forest, owned.2.start ≠ marker) :
    ∃ forest, NotionCoreSliceForest.splitForest (physical state) marker state.forest = some forest ∧
      validForestBounds {state with forest := forest} = true := by
  exact NotionCoreMachineRouting.splitForest_checked_progress state marker
    (partition_bounds state partitioned unique) unique
    (containing_tree_ref state partitioned unique marker existsInstance present newBoundary)

/-! Owner-free coverage. `Partitioned` depends on the forest only through its
multiset of interval references: owners are recovered from the forest itself. -/

/-- The forest's interval references, owners forgotten, are a permutation of
each instance's represented cells. -/
structure Covers (state : State) (refs : List Ref) : Prop where
  refsExist : ∀ ref ∈ refs, ∃ entry ∈ state.instances, entry.1 = ref.start.1
  partitions : ∀ inst, (∃ entry ∈ state.instances, entry.1 = inst) →
    ∃ cells, physical state inst = flatten cells ∧
      (refs.filter (fun ref => ref.start.1 == inst)).Perm ((cellRefs cells).map Prod.snd)

theorem covers_perm {state : State} {refs other : List Ref} (covers : Covers state refs)
    (same : other.Perm refs) : Covers state other := by
  constructor
  · exact fun ref member => covers.refsExist ref (same.mem_iff.mp member)
  · intro inst existsInstance
    obtain ⟨cells, physicalEq, permutation⟩ := covers.partitions inst existsInstance
    exact ⟨cells, physicalEq, (same.filter _).trans permutation⟩

theorem covers_of_partitioned {state : State} (partitioned : Partitioned state) :
    Covers state (NotionCoreSliceForest.forestRefs state.forest) := by
  rw [← NotionCoreForestRefs.ownedRefs_refs]
  constructor
  · intro ref member
    obtain ⟨owned, ownedMember, rfl⟩ := List.mem_map.mp member
    exact partitioned.refsExist owned ownedMember
  · intro inst existsInstance
    obtain ⟨cells, physicalEq, permutation⟩ := partitioned.partitions inst existsInstance
    refine ⟨cells, physicalEq, ?_⟩
    rw [List.filter_map]
    exact permutation.map Prod.snd

private theorem cellRefs_snd_starts (cells : List Cell) :
    ((cellRefs cells).map Prod.snd).map Ref.start = cells.map (fun cell => cell.slice.start) := by
  induction cells with
  | nil => rfl
  | cons cell rest ih => simp [cellRefs, ih]

private theorem cell_starts_unique (cells : List Cell)
    (unique : ((flatten cells).map Atom.address).Nodup) :
    (cells.map (fun cell => cell.slice.start)).Nodup := by
  induction cells with
  | nil => simp
  | cons cell rest ih =>
    simp only [flatten, List.flatMap_cons, Cell.physical, List.cons_append, List.map_cons,
      List.map_append, List.nodup_cons, List.nodup_append] at unique
    refine List.nodup_cons.mpr ⟨?_, ih (by simpa [flatten] using unique.2.2.1)⟩
    intro member
    obtain ⟨other, otherMember, same⟩ := List.mem_map.mp member
    apply unique.1
    refine List.mem_append_right _ (List.mem_map.mpr ⟨NotionCorePartition.boundary other.slice.start,
      List.mem_flatMap.mpr ⟨other, otherMember, by simp [Cell.physical]⟩, ?_⟩)
    simpa [NotionCorePartition.boundary] using same

/-- Within one instance, covered references have distinct starts. -/
theorem covers_starts_unique {state : State} {refs : List Ref} (covers : Covers state refs)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup) (inst : Nat)
    (existsInstance : ∃ entry ∈ state.instances, entry.1 = inst) :
    ((refs.filter (fun ref => ref.start.1 == inst)).map Ref.start).Nodup := by
  obtain ⟨cells, physicalEq, permutation⟩ := covers.partitions inst existsInstance
  rw [(permutation.map Ref.start).nodup_iff, cellRefs_snd_starts]
  exact cell_starts_unique cells (physicalEq ▸ unique inst)

private def ownerOf (owned : List (Nat × Ref)) (start : Address) : Nat :=
  ((owned.find? fun entry => entry.2.start == start).map Prod.fst).getD 0

private theorem ownerOf_member {owned : List (Nat × Ref)} {entry : Nat × Ref} (member : entry ∈ owned)
    (consistent : ∀ other ∈ owned, other.2.start = entry.2.start → other = entry) :
    ownerOf owned entry.2.start = entry.1 := by
  obtain ⟨found, foundEq⟩ : ∃ found, owned.find? (fun other => other.2.start == entry.2.start) = some found :=
    Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨entry, member, by simp⟩)
  have same := consistent found (List.mem_of_find?_eq_some foundEq) (by simpa using List.find?_some foundEq)
  simp [ownerOf, foundEq, same]

private theorem cellRefs_reown (cells : List Cell) (owner : Address → Nat) :
    cellRefs (cells.map fun cell => ⟨owner cell.slice.start, cell.slice⟩) =
      (cellRefs cells).map fun entry => (owner entry.2.start, entry.2) := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    simp only [List.map_cons, cellRefs, ih]
    cases rest <;> rfl

private theorem flatten_reown (cells : List Cell) (owner : Address → Nat) :
    flatten (cells.map fun cell => ⟨owner cell.slice.start, cell.slice⟩) = flatten cells := by
  simp only [flatten, List.flatMap_map]
  rfl

/-- Coverage of a forest's references gives the full owned partition: each
cell takes the owner of the unique reference starting at its start. -/
theorem partitioned_of_covers (state : State) (forest : NotionCoreSliceForest.Forest)
    (covers : Covers state (NotionCoreSliceForest.forestRefs forest))
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup) :
    Partitioned {state with forest := forest} := by
  rw [← NotionCoreForestRefs.ownedRefs_refs] at covers
  constructor
  · intro owned member
    exact covers.refsExist owned.2 (List.mem_map.mpr ⟨owned, member, rfl⟩)
  · intro inst existsInstance
    obtain ⟨cells, physicalEq, permutation⟩ := covers.partitions inst existsInstance
    let owned := ownedRefs forest
    let own := ownerOf owned
    refine ⟨cells.map fun cell => ⟨own cell.slice.start, cell.slice⟩,
      by rw [flatten_reown]; exact physicalEq, ?_⟩
    rw [cellRefs_reown]
    have starts := covers_starts_unique covers unique inst existsInstance
    rw [List.filter_map, List.map_map] at starts
    have consistent : ∀ entry ∈ owned.filter (fun owned => owned.2.start.1 == inst),
        own entry.2.start = entry.1 := by
      intro entry member
      apply ownerOf_member (List.mem_filter.mp member).1
      intro other otherMember sameStart
      have otherFiltered : other ∈ owned.filter (fun owned => owned.2.start.1 == inst) :=
        List.mem_filter.mpr ⟨otherMember, by
          have := (List.mem_filter.mp member).2
          simpa [sameStart] using this⟩
      exact List.inj_on_of_nodup_map starts otherFiltered member sameStart
    have fixed : (owned.filter fun owned => owned.2.start.1 == inst) =
        ((owned.filter fun owned => owned.2.start.1 == inst).map Prod.snd).map
          fun ref => (own ref.start, ref) := by
      rw [List.map_map]
      conv_lhs => rw [← List.map_id (owned.filter _)]
      apply List.map_congr_left
      intro entry member
      simp [consistent entry member]
    change (owned.filter _).Perm _
    rw [fixed]
    have mapped := permutation.map (fun ref => (own ref.start, ref))
    rw [List.filter_map] at mapped
    simpa [List.map_map, Function.comp_def] using mapped

/-- Merge moves interval references between blocks without changing them, so
the partition survives with owners recomputed from the merged forest. -/
theorem merge_partitioned (state : State) (source target : Nat) (partitioned : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (blocks : (state.forest.map NotionCoreSliceForest.Block.id).Nodup) :
    Partitioned {state with forest := NotionCoreSliceForest.mergeForest state.forest source target} := by
  apply partitioned_of_covers _ _ _ unique
  exact covers_perm (covers_of_partitioned partitioned)
    (NotionCoreSliceForest.mergeForest_refs state.forest source target blocks)

/-- The stop is the next physical start, including an empty cell's start.
Dropping that stop silently changes the interval represented by the first ref. -/
theorem next_boundary_control :
    cellRefs [⟨4, ⟨(0, .start), []⟩⟩, ⟨7, ⟨(0, .event (9, 0)), []⟩⟩] =
      [(4, ⟨(0, .start), some (0, .event (9, 0))⟩), (7, ⟨(0, .event (9, 0)), none⟩)] ∧
    cellRefs [⟨4, ⟨(0, .start), []⟩⟩, ⟨7, ⟨(0, .event (9, 0)), []⟩⟩] ≠
      [(4, ⟨(0, .start), none⟩), (7, ⟨(0, .event (9, 0)), none⟩)] := by decide +kernel

#print axioms ref_extracts
#print axioms partition_bounds
#print axioms containing_tree_ref
#print axioms splitForest_partition_progress
#print axioms partitioned_of_covers
#print axioms merge_partitioned
end Sal.MRDTs.Instances.NotionCoreMachinePartition
