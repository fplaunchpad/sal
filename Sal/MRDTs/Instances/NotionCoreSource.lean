import Sal.MRDTs.Instances.NotionCoreSpec

/-! Materialized interval normal form for the create/split/insert/delete core.
An instance is an ordered partition of physical atoms into slices. Blocks own
one active slice, optionally below a permanently empty fresh title root.
This file proves normal-form preservation and projection calculations. It does
not prove extraction of this partition from JavaScript's RGA/endpoint tree.
-/
namespace Sal.MRDTs.Instances.NotionCoreSource
open NotionCoreSpec (Address Slot)

inductive Kind where
  | text (value : Nat) (deleted : Bool)
  | split
  deriving DecidableEq, Repr

structure Atom where
  address : Address
  kind : Kind
  deriving DecidableEq, Repr

def Atom.slot (atom : Atom) : Slot :=
  match atom.kind with
  | .text value deleted => ⟨atom.address, value, !deleted⟩
  | .split => ⟨atom.address, 0, false⟩

/-- Interval boundaries are kept separately from the atoms strictly inside.
The start marker is retained as an address but never rendered. -/
structure Slice where
  start : Address
  atoms : List Atom
  deriving DecidableEq, Repr

def Slice.anchor (slice : Slice) : Slot := ⟨slice.start, 0, false⟩
def Slice.slots (slice : Slice) : List Slot := slice.anchor :: slice.atoms.map Atom.slot

def Slice.traversal (slice : Slice) : List Address :=
  slice.start :: slice.atoms.map Atom.address

/-- The partition order is instance traversal order, independent of block order.
Each noninitial slice start denotes the physical split marker between cells. -/
def instanceTraversal (partition : List Slice) : List Address :=
  partition.flatMap Slice.traversal

inductive RootShape where
  | own
  | attached (emptyTitleInstance : Nat)
  deriving DecidableEq, Repr

structure Block where
  id : Nat
  shape : RootShape
  active : Slice
  deriving DecidableEq, Repr

def Block.project (block : Block) : NotionCoreSpec.Block :=
  ⟨block.id, match block.shape with
    | .own => block.active.slots
    | .attached inst => NotionCoreSpec.root inst :: block.active.slots⟩

/-- Root-only blocks use their own START interval. Attached blocks retain a
separate permanently empty root, distinct from the active interval instance. -/
def Block.Normal (block : Block) : Prop :=
  (∀ atom ∈ block.active.atoms, atom.address.1 = block.active.start.1) ∧
  match block.shape with
  | .own => block.active.start.2 = .start
  | .attached inst => inst ≠ block.active.start.1

/-- Insert a physical marker at a traversal coordinate inside the active slice,
split that interval, and detach the right interval into a fresh title root.
The source-derived provenance lemma must justify the coordinate's relation to
the identity-addressed origin. The coordinate counts retained physical atoms. -/
def splitSlice (slice : Slice) (position : Nat) (marker : Address) : Slice × Slice :=
  (⟨slice.start, slice.atoms.take position⟩,
   ⟨marker, slice.atoms.drop position⟩)

def splitBlock (block : Block) (position : Nat) (marker : Address)
    (target freshInstance : Nat) : Block × Block :=
  let (left, right) := splitSlice block.active position marker
  ({block with active := left}, ⟨target, .attached freshInstance, right⟩)

/-- The source's marker insertion changes the instance traversal at exactly the
selected interval coordinate. Existing partition cells retain their order. -/
theorem split_partition_traversal (before after : List Slice) (slice : Slice)
    (position : Nat) (marker : Address) :
    instanceTraversal (before ++ [(splitSlice slice position marker).1,
      (splitSlice slice position marker).2] ++ after) =
    instanceTraversal before ++
      (slice.start :: ((slice.atoms.take position).map Atom.address ++
        marker :: (slice.atoms.drop position).map Atom.address)) ++
      instanceTraversal after := by
  simp [instanceTraversal, Slice.traversal, splitSlice, List.append_assoc]

/-- Marker insertion preserves every old physical address in order. -/
theorem split_partition_erases_marker (slice : Slice) (position : Nat) :
    (slice.atoms.take position).map Atom.address ++
      (slice.atoms.drop position).map Atom.address = slice.atoms.map Atom.address := by
  rw [← List.map_append, List.take_append_drop]

theorem split_normal (block : Block) (position : Nat) (marker : Address)
    (target freshInstance : Nat) (normal : block.Normal)
    (sameInstance : marker.1 = block.active.start.1)
    (fresh : freshInstance ≠ marker.1) :
    (splitBlock block position marker target freshInstance).1.Normal ∧
    (splitBlock block position marker target freshInstance).2.Normal := by
  rcases normal with ⟨atoms, shape⟩
  constructor
  · refine ⟨?_, shape⟩
    intro atom member
    exact atoms atom (List.mem_of_mem_take member)
  · refine ⟨?_, fresh⟩
    intro atom member
    exact (atoms atom (List.mem_of_mem_drop member)).trans sameInstance.symm

/-- Projecting the two intervals yields a retained-prefix/suffix cut. This is
computed from physical interval splitting, rather than assumed by a relation. -/
theorem split_slice_projection (slice : Slice) (position : Nat) (marker : Address) :
    (splitSlice slice position marker).1.slots = slice.slots.take (position + 1) ∧
    (splitSlice slice position marker).2.slots =
      (⟨marker, 0, false⟩ : Slot) :: slice.slots.drop (position + 1) := by
  simp [splitSlice, Slice.slots, Slice.anchor, List.map_take, List.map_drop]

/-- The instance-address lookup establishes which retained coordinate is cut.
This premise is address arithmetic; it does not assert an observation equation. -/
theorem split_slice_identity_projection (slice : Slice) (origin : Address)
    (position : Nat) (marker : Address)
    (located : (slice.slots.map Slot.address).idxOf origin = position) :
    (splitSlice slice position marker).1.slots = (NotionCoreSpec.cutAfter slice.slots origin).1 ∧
    (splitSlice slice position marker).2.slots =
      (⟨marker, 0, false⟩ : Slot) :: (NotionCoreSpec.cutAfter slice.slots origin).2 := by
  simpa [NotionCoreSpec.cutAfter, located] using split_slice_projection slice position marker

theorem cutAfter_invisible_prefix (head : Slot) (slots : List Slot) (origin : Address)
    (distinct : head.address ≠ origin) :
    NotionCoreSpec.cutAfter (head :: slots) origin =
      (head :: (NotionCoreSpec.cutAfter slots origin).1,
        (NotionCoreSpec.cutAfter slots origin).2) := by
  simp [NotionCoreSpec.cutAfter, distinct, Nat.add_assoc]

/-- Block wrappers preserve the independent identity split, including the
otherwise invisible own-instance root of an attached interval. -/
theorem split_block_identity_projection (block : Block) (origin : Address)
    (position : Nat) (marker : Address) (target freshInstance : Nat)
    (located : (block.active.slots.map Slot.address).idxOf origin = position)
    (notEmptyRoot : ∀ inst, block.shape = .attached inst →
      (NotionCoreSpec.root inst).address ≠ origin) :
    (splitBlock block position marker target freshInstance).1.project.slots =
      (NotionCoreSpec.cutAfter block.project.slots origin).1 ∧
    (splitBlock block position marker target freshInstance).2.project.slots =
      NotionCoreSpec.root freshInstance :: (⟨marker, 0, false⟩ : Slot) ::
        (NotionCoreSpec.cutAfter block.project.slots origin).2 := by
  have interval := split_slice_identity_projection block.active origin position marker located
  cases shape : block.shape with
  | own =>
    simpa [splitBlock, Block.project, shape] using interval
  | attached inst =>
    have prefixEq := cutAfter_invisible_prefix (NotionCoreSpec.root inst)
      block.active.slots origin (notEmptyRoot inst shape)
    simp only [splitBlock, Block.project, shape]
    rw [prefixEq]
    simp [interval.1, interval.2]

/-- Empty-root wrappers do not change rendered text. -/
theorem project_visible (block : Block) :
    NotionCoreSpec.text block.project.slots = NotionCoreSpec.text block.active.slots := by
  cases h : block.shape <;> simp [Block.project, NotionCoreSpec.root, h]

/-- The displayed source split is precisely the active interval's visible
prefix and suffix, for every root shape and every retained coordinate. -/
theorem split_visible (block : Block) (position : Nat) (marker : Address)
    (target freshInstance : Nat) :
    NotionCoreSpec.text (splitBlock block position marker target freshInstance).1.project.slots =
      NotionCoreSpec.text (block.active.slots.take (position + 1)) ∧
    NotionCoreSpec.text (splitBlock block position marker target freshInstance).2.project.slots =
      NotionCoreSpec.text (block.active.slots.drop (position + 1)) := by
  rw [project_visible, project_visible]
  have split := split_slice_projection block.active position marker
  change NotionCoreSpec.text (splitSlice block.active position marker).1.slots = _ ∧
    NotionCoreSpec.text (splitSlice block.active position marker).2.slots = _
  rw [split.1, split.2]
  simp

/-- A coordinate-zero split transfers all text even with a separate empty
root. This excludes the measured merge-induced suffix-left-behind behavior
inside this normal form, without asserting that all source states have it. -/
theorem split_zero_control :
    let source : Block := ⟨1, .attached 9,
      ⟨(2, .event (1, 5)), [⟨(2, .event (1, 6)), .text 97 false⟩,
        ⟨(2, .event (1, 7)), .text 88 false⟩]⟩⟩
    let result := splitBlock source 0 (2, .event (1, 8)) 3 10
    (NotionCoreSpec.text result.1.project.slots, NotionCoreSpec.text result.2.project.slots) = ([], [97, 88]) ∧
    (NotionCoreSpec.text result.1.project.slots, NotionCoreSpec.text result.2.project.slots) ≠ ([88], [97]) := by
  simp [splitBlock, splitSlice, Block.project, Slice.slots, Slice.anchor, Atom.slot,
    NotionCoreSpec.root]

/-- Physical insertion inside an interval; sibling dominance supplies the
retained coordinate. Tree shape and interval ownership are unchanged. -/
def insertSlice (slice : Slice) (position : Nat) (fresh : List Atom) : Slice :=
  {slice with atoms := slice.atoms.take position ++ fresh ++ slice.atoms.drop position}

theorem insert_slice_projection (slice : Slice) (position : Nat) (fresh : List Atom) :
    (insertSlice slice position fresh).slots =
      slice.slots.take (position + 1) ++ fresh.map Atom.slot ++
        slice.slots.drop (position + 1) := by
  simp [insertSlice, Slice.slots, Slice.anchor, List.map_take, List.map_drop]

theorem insert_slice_identity_projection (slice : Slice) (origin : Address)
    (position : Nat) (fresh : List Atom)
    (located : (slice.slots.map Slot.address).idxOf origin = position) :
    (insertSlice slice position fresh).slots =
      NotionCoreSpec.insertSlots origin (fresh.map Atom.slot) slice.slots := by
  simpa [NotionCoreSpec.insertSlots, NotionCoreSpec.cutAfter, located] using
    insert_slice_projection slice position fresh

def eraseAtom (targets : List Address) (atom : Atom) : Atom :=
  {atom with kind := match atom.kind with
    | .text value deleted => .text value (deleted || targets.contains atom.address)
    | .split => .split}

def eraseSlice (targets : List Address) (slice : Slice) : Slice :=
  {slice with atoms := slice.atoms.map (eraseAtom targets)}

theorem erase_atom_projection (targets : List Address) (atom : Atom) :
    (eraseAtom targets atom).slot = NotionCoreSpec.eraseSlot targets atom.slot := by
  cases atom with
  | mk address kind =>
    cases kind with
    | split => simp [eraseAtom, Atom.slot, NotionCoreSpec.eraseSlot]
    | text value deleted =>
      cases deleted <;> cases targets.contains address <;>
        simp [eraseAtom, Atom.slot, NotionCoreSpec.eraseSlot]

theorem erase_slice_projection (targets : List Address) (slice : Slice) :
    (eraseSlice targets slice).slots =
      slice.slots.map (NotionCoreSpec.eraseSlot targets) := by
  have anchor : NotionCoreSpec.eraseSlot targets slice.anchor = slice.anchor := by
    simp [Slice.anchor, NotionCoreSpec.eraseSlot]
  simp only [eraseSlice, Slice.slots, List.map_map, List.map_cons]
  rw [anchor]
  congr 1
  exact List.map_congr_left fun atom _ => erase_atom_projection targets atom

theorem erase_preserves_traversal (targets : List Address) (slice : Slice) :
    (eraseSlice targets slice).traversal = slice.traversal := by
  simp [eraseSlice, Slice.traversal, eraseAtom]

theorem insert_normal (block : Block) (position : Nat) (fresh : List Atom)
    (normal : block.Normal)
    (sameInstance : ∀ atom ∈ fresh, atom.address.1 = block.active.start.1) :
    ({block with active := insertSlice block.active position fresh} : Block).Normal := by
  rcases normal with ⟨atoms, shape⟩
  refine ⟨?_, shape⟩
  intro atom member
  simp only [insertSlice, List.mem_append] at member
  rcases member with (member | member) | member
  · exact atoms atom (List.mem_of_mem_take member)
  · exact sameInstance atom member
  · exact atoms atom (List.mem_of_mem_drop member)

theorem erase_normal (block : Block) (targets : List Address) (normal : block.Normal) :
    ({block with active := eraseSlice targets block.active} : Block).Normal := by
  rcases normal with ⟨atoms, shape⟩
  refine ⟨?_, shape⟩
  intro atom member
  change atom ∈ block.active.atoms.map (eraseAtom targets) at member
  obtain ⟨old, oldMember, atomEq⟩ := List.mem_map.mp member
  rw [← atomEq]
  exact atoms old oldMember

namespace Endpoint
variable {Token : Type} [DecidableEq Token]

/-- Endpoint extraction on a linearized instance, including its sentinels.
This is a list counterpart of source `sliceItemBounds`, not RGA traversal. -/
def afterStart (start : Token) : List Token → List Token
  | [] => []
  | item :: rest => if item = start then rest else afterStart start rest

def beforeEnd (stop : Token) : List Token → List Token
  | [] => []
  | item :: rest => if item = stop then [] else item :: beforeEnd stop rest

def extract (start stop : Token) (traversal : List Token) : List Token :=
  beforeEnd stop (afterStart start traversal)

theorem afterStart_factor (start : Token) (before rest : List Token)
    (absent : start ∉ before) :
    afterStart start (before ++ start :: rest) = rest := by
  induction before with
  | nil => simp [afterStart]
  | cons item before ih =>
    simp only [List.mem_cons, not_or] at absent
    simp [afterStart, Ne.symm absent.1, ih absent.2]

theorem beforeEnd_factor (stop : Token) (inside after : List Token)
    (absent : stop ∉ inside) :
    beforeEnd stop (inside ++ stop :: after) = inside := by
  induction inside with
  | nil => simp [beforeEnd]
  | cons item inside ih =>
    simp only [List.mem_cons, not_or] at absent
    simp [beforeEnd, Ne.symm absent.1, ih absent.2]

/-- Endpoint lookup reconstructs a materialized interval from traversal
factorization and address exclusion; no observation equation is assumed. -/
theorem extract_factor (start stop : Token) (before inside after : List Token)
    (startAbsent : start ∉ before) (stopAbsent : stop ∉ inside) :
    extract start stop (before ++ start :: (inside ++ stop :: after)) = inside := by
  simp only [extract, afterStart_factor start before _ startAbsent]
  exact beforeEnd_factor stop inside after stopAbsent

/-- Inserting a fresh marker at a factored traversal coordinate produces the
left endpoint interval and right endpoint interval. The source provenance and
RGA lemmas must establish that marker insertion yields this traversal. -/
theorem split_extract (start stop marker : Token) (before left right after : List Token)
    (startAbsent : start ∉ before) (stopAbsent : stop ∉ right)
    (markerAbsent : marker ∉ before ++ start :: left) :
    let traversal := before ++ start :: (left ++ marker :: (right ++ stop :: after))
    extract start marker traversal = left ∧ extract marker stop traversal = right := by
  dsimp only
  constructor
  · exact extract_factor start marker before left (right ++ stop :: after)
      startAbsent (fun mem => markerAbsent (by simp [mem]))
  · have factored : before ++ start :: (left ++ marker :: (right ++ stop :: after)) =
        (before ++ start :: left) ++ marker :: (right ++ stop :: after) := by
      simp [List.append_assoc]
    rw [factored]
    exact extract_factor marker stop (before ++ start :: left) right after markerAbsent stopAbsent

end Endpoint

#print axioms split_normal
#print axioms split_slice_identity_projection
end Sal.MRDTs.Instances.NotionCoreSource
