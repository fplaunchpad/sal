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

/-- The reference permutation names actual owner/start/stop triples. Owner
uniqueness is per instance: an attached block also has an empty title in its
own different instance. It must not be required globally across all cells. -/
structure Partitioned (state : State) : Prop where
  refsExist : ∀ owned ∈ ownedRefs state.forest,
    ∃ entry ∈ state.instances, entry.1 = owned.2.start.1
  partitions : ∀ inst, (∃ entry ∈ state.instances, entry.1 = inst) →
    ∃ cells, physical state inst = flatten cells ∧ (cells.map Cell.owner).Nodup ∧
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
  obtain ⟨cells, physicalEq, _, permutation⟩ := partitioned.partitions owned.2.start.1
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
  obtain ⟨cells, physicalEq, owners, permutation⟩ :=
    partitioned.partitions marker.1 existsInstance
  have representation : NotionCorePartition.Represents
      ⟨physical state marker.1, cells.map Cell.entry⟩ cells :=
    ⟨physicalEq, rfl, unique marker.1, owners⟩
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
end Sal.MRDTs.Instances.NotionCoreMachinePartition
