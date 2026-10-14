import Sal.MRDTs.Instances.NotionCoreMachine

/-! Actual checked slice extraction from a structurally partitioned physical
instance. The stop must be the next physical boundary, not the next block in
Map or display order. Establishing this relation for complete replay remains a
separate invariant obligation. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineSlices
open NotionCoreSpec (Address)
open NotionCoreSource (Atom)
open NotionCorePartition (Cell boundary flatten)
open NotionCoreMachine

private theorem boundary_index {α : Type} [BEq α] [LawfulBEq α]
    (before after : List α) (item : α) (unique : (before ++ item :: after).Nodup) :
    (before ++ item :: after).idxOf item = before.length := by
  have absent : item ∉ before := by
    have h := (List.nodup_cons.mp (List.nodup_middle.mp unique)).1
    exact fun member => h (List.mem_append_left _ member)
  simp [List.idxOf_append_of_notMem absent]

/-- Both endpoint checks succeed from physical factorization and uniqueness;
the checked interpreter then returns exactly the interior atoms. -/
theorem sliceAtoms_factor (state : State) (before inside after : List Atom)
    (start : Address) (stop : Option Address)
    (existsInstance : state.instances.any (fun entry => entry.1 == start.1) = true)
    (physicalEq : physical state start.1 = (before ++ boundary start :: inside) ++ after)
    (ending : (after = [] ∧ stop = none) ∨
      ∃ finish rest, after = boundary finish :: rest ∧ stop = some finish)
    (unique : ((physical state start.1).map Atom.address).Nodup) :
    sliceAtoms state ⟨start, stop⟩ = some inside := by
  have shapeUnique : (before.map Atom.address ++ start ::
      (inside.map Atom.address ++ after.map Atom.address)).Nodup := by
    simpa [physicalEq, boundary, List.append_assoc] using unique
  have startIndex : ((physical state start.1).map Atom.address).idxOf start = before.length := by
    simpa [physicalEq, boundary, List.append_assoc] using
      boundary_index (before.map Atom.address) (inside.map Atom.address ++ after.map Atom.address) start shapeUnique
  have startPresent : ((physical state start.1).map Atom.address).contains start = true := by
    simp [physicalEq, boundary]
  have extracted : NotionCorePartition.extract (physical state start.1) start stop = inside := by
    rw [physicalEq]
    apply NotionCorePartition.extract_factor before inside after start stop ending
    simpa [physicalEq] using unique
  rcases ending with ⟨rfl, rfl⟩ | ⟨finish, rest, rfl, rfl⟩
  · have bound : before.length < (physical state start.1).length := by
      simp [physicalEq]
    simp only [sliceAtoms, existsInstance, startPresent, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte, List.length_map, startIndex, extracted]
    simp [bind, Option.bind, Nat.not_le.mpr bound]
  · have stopIndex : ((physical state start.1).map Atom.address).idxOf finish =
        before.length + 1 + inside.length := by
      have factorUnique : (((before ++ boundary start :: inside).map Atom.address) ++
          finish :: rest.map Atom.address).Nodup := by
        simpa [physicalEq, boundary] using unique
      simpa [physicalEq, boundary, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        boundary_index ((before ++ boundary start :: inside).map Atom.address)
          (rest.map Atom.address) finish factorUnique
    have stopPresent : ((physical state start.1).map Atom.address).contains finish = true := by
      simp [physicalEq, boundary]
    have bound : ¬ before.length + 1 + inside.length ≤ before.length := by omega
    simp only [sliceAtoms, existsInstance, startPresent, stopPresent, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte, startIndex, stopIndex, extracted]
    simp [bind, Option.bind, bound]

/-- A stored Ref with the next physical endpoint extracts its represented cell.
The conclusion includes successful validation, not only unchecked extraction. -/
theorem sliceAtoms_cell (state : State) (before after : List Cell) (cell : Cell)
    (existsInstance : state.instances.any (fun entry => entry.1 == cell.slice.start.1) = true)
    (physicalEq : physical state cell.slice.start.1 = flatten (before ++ cell :: after))
    (unique : ((physical state cell.slice.start.1).map Atom.address).Nodup) :
    sliceAtoms state ⟨cell.slice.start, after.head?.map (fun next => next.slice.start)⟩ =
      some cell.slice.atoms := by
  apply sliceAtoms_factor state (flatten before) cell.slice.atoms (flatten after)
    cell.slice.start _ existsInstance
  · simpa [flatten, Cell.physical, List.append_assoc] using physicalEq
  · cases after with
    | nil => exact Or.inl ⟨rfl, rfl⟩
    | cons next rest =>
        exact Or.inr ⟨next.slice.start, next.slice.atoms ++ flatten rest, rfl, rfl⟩
  · exact unique

/-- An inactive title contributes no atoms, but its virtual START and instance
must still exist. This is distinct from having no slice for that instance. -/
theorem empty_title_atoms (state : State) (bid : Nat)
    (existsInstance : state.instances.any (fun entry => entry.1 == bid) = true)
    (empty : physical state bid = [boundary (bid, .start)]) :
    sliceAtoms state (NotionCoreSliceForest.titleRef bid) = some [] := by
  apply sliceAtoms_factor state [] [] [] (bid, .start) none existsInstance
  · exact empty
  · exact Or.inl ⟨rfl, rfl⟩
  · simp [empty]

/-- Actual preorder extraction of a detached core leaf below an empty title
agrees with its physical partition cell, including tombstoned atoms. -/
theorem attached_tree_atoms (state : State) (bid : Nat) (before after : List Cell) (cell : Cell)
    (titleExists : state.instances.any (fun entry => entry.1 == bid) = true)
    (titleEmpty : physical state bid = [boundary (bid, .start)])
    (activeExists : state.instances.any (fun entry => entry.1 == cell.slice.start.1) = true)
    (physicalEq : physical state cell.slice.start.1 = flatten (before ++ cell :: after))
    (unique : ((physical state cell.slice.start.1).map Atom.address).Nodup) :
    treeAtoms state (.node (NotionCoreSliceForest.titleRef bid)
      (.cons (.node ⟨cell.slice.start, after.head?.map (fun next => next.slice.start)⟩ .nil) .nil)) =
      some cell.slice.atoms := by
  have root := empty_title_atoms state bid titleExists titleEmpty
  have leaf := sliceAtoms_cell state before after cell activeExists physicalEq unique
  simp [treeAtoms, NotionCoreSliceForest.preorderTree, NotionCoreSliceForest.preorderChildren,
    root, leaf]

private def a : NotionRunAllocation.Id := ⟨1,[65]⟩
private def b : NotionRunAllocation.Id := ⟨2,[65]⟩
private def fixture : State := {instances := [(0, {rows :=
  [⟨⟨a,.text 97 true⟩,.start⟩,⟨⟨b,.text 98 false⟩,.item a⟩]})]}
private def aa : Address := NotionCorePhysicalReplay.address 0 a
private def bb : Address := NotionCorePhysicalReplay.address 0 b

/-- A legal empty interior succeeds, whereas reversed bounds are rejected.
The hidden text atom remains physically present and can be an endpoint. -/
theorem empty_and_reversed_control :
    sliceAtoms fixture ⟨aa, some bb⟩ = some [] ∧
    sliceAtoms fixture ⟨bb, some aa⟩ ≠ some [] := by decide +kernel

/-- The stop belongs to physical interval ownership. Dropping it admits the
next interval's visible text; tombstones alone do not repair that mistake. -/
theorem stop_ownership_control :
    (sliceAtoms fixture ⟨(0,.start), some bb⟩).map (List.flatMap atomText) = some [] ∧
    (sliceAtoms fixture ⟨(0,.start), none⟩).map (List.flatMap atomText) ≠ some [] := by decide +kernel

#print axioms sliceAtoms_factor
#print axioms sliceAtoms_cell
#print axioms attached_tree_atoms
#print axioms empty_and_reversed_control
#print axioms stop_ownership_control
end Sal.MRDTs.Instances.NotionCoreMachineSlices
