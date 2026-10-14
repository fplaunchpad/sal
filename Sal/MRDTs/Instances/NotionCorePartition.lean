import Sal.MRDTs.Instances.NotionCoreSource
import Sal.MRDTs.Instances.NotionCoreSourceDocument
import Mathlib.Data.List.Nodup

/-! Raw endpoint-table extraction for one finite physical instance. Source
origin-graph extraction is separate: this file starts with an explicit raw
augmented physical traversal and endpoint/owner table, with a structural factorization
invariant. The materialized cells are recovered by actual endpoint scans. The traversal
includes a virtual START boundary atom; JavaScript keeps START outside its RGA
items. Endpoint-table order is physical interval order, not block display order.
-/
namespace Sal.MRDTs.Instances.NotionCorePartition
open NotionCoreSpec (Address)
open NotionCoreSource (Atom Slice)

structure Entry where
  owner : Nat
  start : Address
  deriving DecidableEq, Repr

structure Cell where
  owner : Nat
  slice : Slice
  deriving DecidableEq, Repr

structure State where
  physical : List Atom
  endpoints : List Entry
  deriving DecidableEq, Repr

def boundary (address : Address) : Atom := ⟨address, .split⟩
def Cell.entry (cell : Cell) : Entry := ⟨cell.owner, cell.slice.start⟩
def Cell.physical (cell : Cell) : List Atom := boundary cell.slice.start :: cell.slice.atoms
def flatten (cells : List Cell) : List Atom := cells.flatMap Cell.physical

def ids (physical : List Atom) : List (Option Address) :=
  physical.map (fun atom => some atom.address)

def lookup (physical : List Atom) (address : Address) : Option Atom :=
  physical.find? (fun atom => decide (atom.address = address))

/-- Actual endpoint scans over the raw traversal, with an explicit END sentinel.
The table supplies each interval's next endpoint. -/
def extractIds (physical : List Atom) (start : Address) (stop : Option Address) :
    List (Option Address) :=
  NotionCoreSource.Endpoint.extract (some start) stop (ids physical ++ [none])

def extract (physical : List Atom) (start : Address) (stop : Option Address) : List Atom :=
  (extractIds physical start stop).filterMap (fun address => address.bind (lookup physical))

def scanCells (physical : List Atom) : List Entry → List Cell
  | [] => []
  | entry :: rest =>
      ⟨entry.owner, ⟨entry.start, extract physical entry.start (rest.head?.map Entry.start)⟩⟩ ::
        scanCells physical rest

/-- Structural coverage and uniqueness of a raw endpoint state. This records
physical/table factorization, not equality with the result of `scanCells`. -/
def Represents (state : State) (cells : List Cell) : Prop :=
  state.physical = flatten cells ∧ state.endpoints = cells.map Cell.entry ∧
  (state.physical.map Atom.address).Nodup ∧ (cells.map Cell.owner).Nodup

private theorem middle_absent {α : Type} (before after : List α) (item : α)
    (unique : (before ++ item :: after).Nodup) : item ∉ before ∧ item ∉ after := by
  have absent := (List.nodup_cons.mp (List.nodup_middle.mp unique)).1
  exact ⟨fun member => absent (List.mem_append_left _ member),
    fun member => absent (List.mem_append_right _ member)⟩

private theorem some_absent (address : Address) (physical : List Atom)
    (absent : address ∉ physical.map Atom.address) : some address ∉ ids physical := by
  simpa only [ids, List.mem_map, Option.some.injEq] using absent

theorem lookup_member (physical : List Atom) (atom : Atom)
    (unique : (physical.map Atom.address).Nodup) (member : atom ∈ physical) :
    lookup physical atom.address = some atom := by
  induction physical with
  | nil => simp at member
  | cons head rest ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases List.mem_cons.mp member with rfl | member
      · simp [lookup]
      · have distinct : head.address ≠ atom.address := by
          intro equal
          exact unique.1 (List.mem_map.mpr ⟨atom, member, equal.symm⟩)
        simpa [lookup, distinct] using ih unique.2 member

/-- An arbitrary factored raw traversal, not a precomputed projected slice,
recovers its interior by scanning the explicit start and next/end endpoint. -/
theorem extractIds_factor (before inside after : List Atom) (start : Address)
    (stop : Option Address)
    (ending : (after = [] ∧ stop = none) ∨
      ∃ finish rest, after = boundary finish :: rest ∧ stop = some finish)
    (unique : (((before ++ boundary start :: inside) ++ after).map Atom.address).Nodup) :
    extractIds ((before ++ boundary start :: inside) ++ after) start stop = ids inside := by
  have startAbsent : start ∉ before.map Atom.address := by
    have shape : (before.map Atom.address ++ start ::
        (inside.map Atom.address ++ after.map Atom.address)).Nodup := by
      simpa only [List.map_append, List.map_cons, boundary, List.append_assoc] using unique
    exact (middle_absent _ _ _ shape).1
  rcases ending with ⟨rfl, rfl⟩ | ⟨finish, rest, rfl, rfl⟩
  · have factor : ids (before ++ boundary start :: inside) ++ [none] =
        ids before ++ some start :: (ids inside ++ none :: []) := by
      simp [ids, boundary, List.append_assoc]
    unfold extractIds
    rw [List.append_nil, factor]
    apply NotionCoreSource.Endpoint.extract_factor
    · exact some_absent _ _ startAbsent
    · simp [ids]
  · have finishAbsent : finish ∉ inside.map Atom.address := by
      have shape : ((before ++ boundary start :: inside).map Atom.address ++
          finish :: rest.map Atom.address).Nodup := by
        simpa only [List.map_append, List.map_cons, boundary] using unique
      have absent := (middle_absent _ _ _ shape).1
      intro member
      exact absent (by simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]; exact Or.inr (Or.inr member))
    have factor : ids ((before ++ boundary start :: inside) ++ boundary finish :: rest) ++ [none] =
        ids before ++ some start :: (ids inside ++ some finish :: (ids rest ++ [none])) := by
      simp [ids, boundary, List.append_assoc]
    unfold extractIds
    rw [factor]
    exact NotionCoreSource.Endpoint.extract_factor _ _ _ _ _
      (some_absent _ _ startAbsent) (some_absent _ _ finishAbsent)

theorem extract_factor (before inside after : List Atom) (start : Address)
    (stop : Option Address)
    (ending : (after = [] ∧ stop = none) ∨
      ∃ finish rest, after = boundary finish :: rest ∧ stop = some finish)
    (unique : (((before ++ boundary start :: inside) ++ after).map Atom.address).Nodup) :
    extract ((before ++ boundary start :: inside) ++ after) start stop = inside := by
  unfold extract
  rw [extractIds_factor before inside after start stop ending unique]
  simp only [ids, List.filterMap_map]
  trans inside.filterMap some
  · apply List.filterMap_congr
    intro atom member
    exact lookup_member _ atom unique (by simp [member])
  · simp

theorem extract_cell (before after : List Cell) (cell : Cell)
    (unique : ((flatten (before ++ cell :: after)).map Atom.address).Nodup) :
    extract (flatten (before ++ cell :: after)) cell.slice.start
      (after.head?.map (fun cell => cell.slice.start)) = cell.slice.atoms := by
  have factor : flatten (before ++ cell :: after) =
      (flatten before ++ boundary cell.slice.start :: cell.slice.atoms) ++ flatten after := by
    simp [flatten, Cell.physical, List.append_assoc]
  have ending : (flatten after = [] ∧ after.head?.map (fun cell => cell.slice.start) = none) ∨
      ∃ finish rest, flatten after = boundary finish :: rest ∧
        after.head?.map (fun cell => cell.slice.start) = some finish := by
    cases after with
    | nil => exact Or.inl ⟨rfl, rfl⟩
    | cons next rest => exact Or.inr ⟨next.slice.start, next.slice.atoms ++ flatten rest, rfl, rfl⟩
  rw [factor] at unique ⊢
  exact extract_factor _ _ _ _ _ ending unique

private theorem scanCells_suffix (before after : List Cell)
    (unique : ((flatten (before ++ after)).map Atom.address).Nodup) :
    scanCells (flatten (before ++ after)) (after.map Cell.entry) = after := by
  induction after generalizing before with
  | nil => rfl
  | cons cell rest ih =>
      have stop : (rest.map Cell.entry).head?.map Entry.start =
          rest.head?.map (fun cell => cell.slice.start) := by cases rest <;> rfl
      have head := extract_cell before rest cell unique
      have tail := ih (before ++ [cell]) (by simpa only [List.append_assoc, List.singleton_append] using unique)
      simp only [List.map_cons, scanCells, Cell.entry, stop, head]
      rw [show flatten (before ++ cell :: rest) = flatten ((before ++ [cell]) ++ rest) from
        by simp only [List.append_assoc, List.singleton_append]]
      rw [tail]

/-- Every materialized interval is recovered from an arbitrary raw state
satisfying the structural endpoint factorization and uniqueness invariant. -/
theorem extraction_correct {state : State} {cells : List Cell}
    (representation : Represents state cells) : scanCells state.physical state.endpoints = cells := by
  rcases representation with ⟨physical, table, unique, _⟩
  rw [physical, table]
  exact scanCells_suffix [] cells (by simpa only [physical, List.nil_append] using unique)

def semanticCells (cells : List Cell) : NotionCoreSpec.Document :=
  cells.map fun cell => ⟨cell.owner, cell.slice.slots⟩

theorem semantic_addresses (cells : List Cell) :
    (semanticCells cells).flatMap (fun block => block.slots.map NotionCoreSpec.Slot.address) =
      (flatten cells).map Atom.address := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      simp only [semanticCells, List.map_cons, List.flatMap_cons, flatten, List.map_append,
        Cell.physical, List.map_cons]
      rw [show cell.slice.slots.map NotionCoreSpec.Slot.address =
        cell.slice.start :: cell.slice.atoms.map Atom.address from by
          exact NotionCoreSourceDocument.active_addresses cell.slice]
      exact congrArg (_ ++ ·) ih

def findCell (cells : List Cell) (origin : Address) : Option Cell :=
  cells.find? (fun cell => decide (origin ∈ cell.slice.traversal))

theorem findCell_of_member {cells : List Cell} (cell : Cell) (origin : Address)
    (unique : ((flatten cells).map Atom.address).Nodup)
    (member : cell ∈ cells) (active : origin ∈ cell.slice.traversal) :
    findCell cells origin = some cell := by
  obtain ⟨before, after, shape⟩ := List.append_of_mem member
  subst cells
  have semanticUnique : ((semanticCells before ++
      (⟨cell.owner, cell.slice.slots⟩ : NotionCoreSpec.Block) :: semanticCells after).flatMap
        (fun block => block.slots.map NotionCoreSpec.Slot.address)).Nodup := by
    simpa only [← semantic_addresses, semanticCells, List.map_append, List.map_cons] using unique
  have present : origin ∈ cell.slice.slots.map NotionCoreSpec.Slot.address := by
    simpa only [NotionCoreSourceDocument.active_addresses] using active
  have separated := (NotionCoreSpec.address_focus (semanticCells before) (semanticCells after)
    ⟨cell.owner, cell.slice.slots⟩ origin semanticUnique present).2
  apply List.find?_eq_some_iff_append.mpr
  refine ⟨by simp [active], before, after, rfl, ?_⟩
  intro other otherMember
  have absent := separated (⟨other.owner, other.slice.slots⟩ : NotionCoreSpec.Block)
    (List.mem_append_left _ (List.mem_map.mpr ⟨other, otherMember, rfl⟩))
  simp only [NotionCoreSourceDocument.active_addresses] at absent
  simp [absent]

/-- A physical identity belongs to at most one materialized cell and hence
one owner, even when the character is tombstoned. -/
theorem unique_cell {cells : List Cell} {left right : Cell} {origin : Address}
    (unique : ((flatten cells).map Atom.address).Nodup)
    (leftMember : left ∈ cells) (rightMember : right ∈ cells)
    (leftOwns : origin ∈ left.slice.traversal) (rightOwns : origin ∈ right.slice.traversal) :
    left = right := by
  have leftFound := findCell_of_member left origin unique leftMember leftOwns
  have rightFound := findCell_of_member right origin unique rightMember rightOwns
  rw [leftFound] at rightFound
  exact Option.some.inj rightFound

def locate (state : State) (origin : Address) : Option Cell :=
  findCell (scanCells state.physical state.endpoints) origin

theorem locate_of_member {state : State} {cells : List Cell} (cell : Cell) (origin : Address)
    (representation : Represents state cells) (member : cell ∈ cells)
    (active : origin ∈ cell.slice.traversal) : locate state origin = some cell := by
  rw [locate, extraction_correct representation]
  exact findCell_of_member cell origin (by simpa only [representation.1] using representation.2.2.1) member active

/-- Splice after the first physical/key occurrence. Origin membership is an
issuance guard; indices are computed by the executable search. -/
def spliceAfterBy {α β : Type} [BEq β] [LawfulBEq β] (key : α → β)
    (origin : β) (fresh : List α) (items : List α) : List α :=
  let index := (items.map key).idxOf origin + 1
  items.take index ++ fresh ++ items.drop index

theorem splice_context {α β : Type} [BEq β] [LawfulBEq β] (key : α → β)
    (before inside after : List α) (origin : β) (fresh : List α)
    (absent : origin ∉ before.map key) (present : origin ∈ inside.map key) :
    spliceAfterBy key origin fresh (before ++ inside ++ after) =
      before ++ spliceAfterBy key origin fresh inside ++ after := by
  have index : ((before ++ inside ++ after).map key).idxOf origin =
      before.length + (inside.map key).idxOf origin := by
    simp only [List.map_append, List.append_assoc]
    rw [List.idxOf_append, if_neg absent, List.idxOf_append, if_pos present, List.length_map]
    omega
  have bound : (inside.map key).idxOf origin + 1 ≤ inside.length := by
    have small := List.idxOf_lt_length_of_mem present
    simpa only [List.length_map] using Nat.succ_le_of_lt small
  dsimp only [spliceAfterBy]
  rw [index]
  rw [show before.length + (inside.map key).idxOf origin + 1 =
    before.length + ((inside.map key).idxOf origin + 1) from by omega]
  simp only [List.append_assoc]
  rw [List.take_length_add_append, List.drop_length_add_append,
    List.take_append_of_le_length bound, List.drop_append_of_le_length bound]
  simp [List.append_assoc]

def splitCell (cell : Cell) (origin marker : Address) (freshOwner : Nat) : List Cell :=
  let result := NotionCoreSource.splitSlice cell.slice (cell.slice.traversal.idxOf origin) marker
  [⟨cell.owner, result.1⟩, ⟨freshOwner, result.2⟩]

/-- A raw split searches the actual endpoint-extracted cells, inserts the
physical marker after its origin, and updates the endpoint row after its start.
It neither constructs nor reads a materialized output partition. -/
def split (state : State) (origin marker : Address) (freshOwner : Nat) : Option State :=
  match locate state origin with
  | none => none
  | some cell => some ⟨
      spliceAfterBy Atom.address origin [boundary marker] state.physical,
      spliceAfterBy Entry.start cell.slice.start [⟨freshOwner, marker⟩] state.endpoints⟩

private theorem cell_addresses (cell : Cell) :
    cell.physical.map Atom.address = cell.slice.traversal := rfl

private theorem prefix_absent (before inside after : List Atom) (origin : Address)
    (unique : ((before ++ inside ++ after).map Atom.address).Nodup)
    (present : origin ∈ inside.map Atom.address) : origin ∉ before.map Atom.address := by
  have shape : (before.map Atom.address ++ (inside.map Atom.address ++ after.map Atom.address)).Nodup := by
    simpa only [List.map_append, List.append_assoc] using unique
  have separated := (List.nodup_append'.mp shape).2.2
  intro collision
  exact List.disjoint_left.mp separated collision (List.mem_append_left _ present)

private theorem start_prefix_absent (before after : List Cell) (cell : Cell)
    (unique : ((flatten (before ++ cell :: after)).map Atom.address).Nodup) :
    cell.slice.start ∉ (before.map Cell.entry).map Entry.start := by
  have present : cell.slice.start ∈ cell.physical.map Atom.address := by simp [Cell.physical, boundary]
  have absent := prefix_absent (flatten before) cell.physical (flatten after) cell.slice.start
    (by simpa only [flatten, List.flatMap_append, List.flatMap_cons, List.append_assoc] using unique) present
  intro collision
  obtain ⟨entry, entryMem, startEq⟩ := List.mem_map.mp collision
  obtain ⟨other, otherMem, rfl⟩ := List.mem_map.mp entryMem
  apply absent
  exact List.mem_map.mpr ⟨boundary other.slice.start,
    List.mem_flatMap.mpr ⟨other, otherMem, by simp [Cell.physical]⟩, startEq⟩

theorem split_physical (before after : List Cell) (cell : Cell) (origin marker : Address)
    (freshOwner : Nat)
    (unique : ((flatten (before ++ cell :: after)).map Atom.address).Nodup)
    (active : origin ∈ cell.slice.traversal) :
    spliceAfterBy Atom.address origin [boundary marker] (flatten (before ++ cell :: after)) =
      flatten (before ++ splitCell cell origin marker freshOwner ++ after) := by
  have present : origin ∈ cell.physical.map Atom.address := by simpa only [cell_addresses] using active
  have absent := prefix_absent (flatten before) cell.physical (flatten after) origin
    (by simpa only [flatten, List.flatMap_append, List.flatMap_cons, List.append_assoc] using unique) present
  have context := splice_context Atom.address (flatten before) cell.physical (flatten after)
    origin [boundary marker] absent present
  simpa [flatten, splitCell, NotionCoreSource.splitSlice, Cell.physical, boundary,
    spliceAfterBy, NotionCoreSource.Slice.traversal, List.append_assoc] using context

theorem split_table (before after : List Cell) (cell : Cell) (origin marker : Address)
    (freshOwner : Nat)
    (unique : ((flatten (before ++ cell :: after)).map Atom.address).Nodup) :
    spliceAfterBy Entry.start cell.slice.start [⟨freshOwner, marker⟩]
        ((before ++ cell :: after).map Cell.entry) =
      (before ++ splitCell cell origin marker freshOwner ++ after).map Cell.entry := by
  have context := splice_context Entry.start (before.map Cell.entry) [cell.entry]
    (after.map Cell.entry) cell.slice.start [⟨freshOwner, marker⟩]
    (start_prefix_absent before after cell unique) (by simp [Cell.entry])
  simpa [splitCell, NotionCoreSource.splitSlice, Cell.entry, spliceAfterBy,
    List.map_append, List.append_assoc] using context

private theorem splice_singleton_nodup {α β : Type} [BEq β] [LawfulBEq β] (key : α → β)
    (items : List α) (fresh : α) (origin : β)
    (unique : (items.map key).Nodup) (absent : key fresh ∉ items.map key) :
    ((spliceAfterBy key origin [fresh] items).map key).Nodup := by
  simp only [spliceAfterBy, List.map_append, List.map_take, List.map_drop,
    List.map_cons, List.append_assoc, List.singleton_append]
  apply List.nodup_middle.mpr
  rw [List.take_append_drop]
  exact List.nodup_cons.mpr ⟨absent, unique⟩

/-- The raw physical splice and raw endpoint-table update refine the
materialized split. The containing interval comes from active membership and
global uniqueness; no desired output extraction/projection equality is assumed. -/
theorem split_represents {state : State} (before after : List Cell) (cell : Cell)
    (origin marker : Address) (freshOwner : Nat)
    (representation : Represents state (before ++ cell :: after))
    (active : origin ∈ cell.slice.traversal)
    (freshMarker : marker ∉ state.physical.map Atom.address)
    (freshBlock : freshOwner ∉ (before ++ cell :: after).map Cell.owner) :
    ∃ next, split state origin marker freshOwner = some next ∧
      Represents next (before ++ splitCell cell origin marker freshOwner ++ after) := by
  have located := locate_of_member cell origin representation (by simp) active
  have unique : ((flatten (before ++ cell :: after)).map Atom.address).Nodup := by
    simpa only [representation.1] using representation.2.2.1
  refine ⟨⟨spliceAfterBy Atom.address origin [boundary marker] state.physical,
    spliceAfterBy Entry.start cell.slice.start [⟨freshOwner, marker⟩] state.endpoints⟩,
    by simp only [split, located], ?_, ?_, ?_, ?_⟩
  · simpa only [representation.1] using split_physical before after cell origin marker freshOwner unique active
  · simpa only [representation.2.1] using split_table before after cell origin marker freshOwner unique
  · exact splice_singleton_nodup Atom.address state.physical (boundary marker) origin
      representation.2.2.1 freshMarker
  · have prior : ((before ++ [cell]).map Cell.owner ++ after.map Cell.owner).Nodup := by
      simpa only [List.map_append, List.map_cons, List.append_assoc, List.singleton_append] using representation.2.2.2
    have absent : freshOwner ∉ (before ++ [cell]).map Cell.owner ++ after.map Cell.owner := by
      simpa only [List.map_append, List.map_cons, List.append_assoc, List.singleton_append] using freshBlock
    have inserted := List.nodup_middle.mpr (List.nodup_cons.mpr ⟨absent, prior⟩)
    simpa [splitCell, NotionCoreSource.splitSlice, List.map_append, List.append_assoc] using inserted

/-- Every raw physical identity has exactly one cell/owner. This includes
retained starts, split markers and tombstoned characters. -/
theorem physical_unique_owner {state : State} {cells : List Cell} (origin : Address)
    (representation : Represents state cells)
    (present : origin ∈ state.physical.map Atom.address) :
    ∃! cell, cell ∈ cells ∧ origin ∈ cell.slice.traversal := by
  rw [representation.1] at present
  obtain ⟨atom, physicalMember, rfl⟩ := List.mem_map.mp present
  obtain ⟨cell, member, atomMember⟩ := List.mem_flatMap.mp physicalMember
  have active : atom.address ∈ cell.slice.traversal := by
    rw [← cell_addresses]
    exact List.mem_map.mpr ⟨atom, atomMember, rfl⟩
  refine ⟨cell, ⟨member, active⟩, ?_⟩
  intro other h
  exact unique_cell (by simpa only [representation.1] using representation.2.2.1)
    h.1 member h.2 active

/-- The affected interval is derived from raw origin membership and global
ownership, rather than supplied as a chosen final projection. -/
theorem split_refines {state : State} {cells : List Cell} (origin marker : Address)
    (freshOwner : Nat) (representation : Represents state cells)
    (present : origin ∈ state.physical.map Atom.address)
    (freshMarker : marker ∉ state.physical.map Atom.address)
    (freshBlock : freshOwner ∉ state.endpoints.map Entry.owner) :
    ∃ before cell after next,
      cells = before ++ cell :: after ∧ locate state origin = some cell ∧
      split state origin marker freshOwner = some next ∧
      Represents next (before ++ splitCell cell origin marker freshOwner ++ after) := by
  obtain ⟨cell, ownership, _⟩ := physical_unique_owner origin representation present
  obtain ⟨before, after, shape⟩ := List.append_of_mem ownership.1
  have located := locate_of_member cell origin representation ownership.1 ownership.2
  have freshOwner' : freshOwner ∉ cells.map Cell.owner := by
    simpa only [representation.2.1, List.map_map, Cell.entry, Function.comp_def] using freshBlock
  subst cells
  obtain ⟨next, executed, represented⟩ := split_represents before after cell origin marker freshOwner
    representation ownership.2 freshMarker freshOwner'
  exact ⟨before, cell, after, next, rfl, located, executed, represented⟩

def insertCell (cell : Cell) (origin : Address) (fresh : List Atom) : Cell :=
  {cell with slice := NotionCoreSource.insertSlice cell.slice (cell.slice.traversal.idxOf origin) fresh}

def insert (state : State) (origin : Address) (fresh : List Atom) : Option State :=
  match locate state origin with
  | none => none
  | some _ => some {state with physical := spliceAfterBy Atom.address origin fresh state.physical}

theorem insert_physical (before after : List Cell) (cell : Cell) (origin : Address)
    (fresh : List Atom)
    (unique : ((flatten (before ++ cell :: after)).map Atom.address).Nodup)
    (active : origin ∈ cell.slice.traversal) :
    spliceAfterBy Atom.address origin fresh (flatten (before ++ cell :: after)) =
      flatten (before ++ insertCell cell origin fresh :: after) := by
  have present : origin ∈ cell.physical.map Atom.address := by simpa only [cell_addresses] using active
  have absent := prefix_absent (flatten before) cell.physical (flatten after) origin
    (by simpa only [flatten, List.flatMap_append, List.flatMap_cons, List.append_assoc] using unique) present
  have context := splice_context Atom.address (flatten before) cell.physical (flatten after)
    origin fresh absent present
  simpa [flatten, insertCell, NotionCoreSource.insertSlice, Cell.physical, boundary,
    spliceAfterBy, NotionCoreSource.Slice.traversal, List.append_assoc] using context

theorem splice_nodup {α β : Type} [BEq β] [LawfulBEq β] (key : α → β)
    (items fresh : List α) (origin : β)
    (unique : (items.map key).Nodup) (newUnique : (fresh.map key).Nodup)
    (apart : List.Disjoint (items.map key) (fresh.map key)) :
    ((spliceAfterBy key origin fresh items).map key).Nodup := by
  have partition : (items.take ((items.map key).idxOf origin + 1)).map key ++
      (items.drop ((items.map key).idxOf origin + 1)).map key = items.map key := by
    rw [← List.map_append, List.take_append_drop]
  have permutation : ((spliceAfterBy key origin fresh items).map key).Perm
      (items.map key ++ fresh.map key) := by
    apply List.perm_iff_count.mpr
    intro x
    have counts := congrArg (List.count x) partition
    simp only [List.count_append] at counts
    simp only [spliceAfterBy, List.map_append, List.count_append]
    omega
  exact permutation.nodup_iff.mpr (List.nodup_append'.mpr ⟨unique, newUnique, apart⟩)

theorem insert_represents {state : State} (before after : List Cell) (cell : Cell)
    (origin : Address) (fresh : List Atom)
    (representation : Represents state (before ++ cell :: after))
    (active : origin ∈ cell.slice.traversal)
    (newUnique : (fresh.map Atom.address).Nodup)
    (apart : List.Disjoint (state.physical.map Atom.address) (fresh.map Atom.address)) :
    ∃ next, insert state origin fresh = some next ∧
      Represents next (before ++ insertCell cell origin fresh :: after) := by
  have located := locate_of_member cell origin representation (by simp) active
  have unique : ((flatten (before ++ cell :: after)).map Atom.address).Nodup := by
    simpa only [representation.1] using representation.2.2.1
  refine ⟨{state with physical := spliceAfterBy Atom.address origin fresh state.physical},
    by simp only [insert, located], ?_, ?_, ?_, ?_⟩
  · simpa only [representation.1] using insert_physical before after cell origin fresh unique active
  · simpa [insertCell, NotionCoreSource.insertSlice, Cell.entry, List.map_append] using representation.2.1
  · exact splice_nodup Atom.address state.physical fresh origin representation.2.2.1 newUnique apart
  · simpa [insertCell, List.map_append] using representation.2.2.2

/-- The published split path integrates its marker before routing it to a
slice. With the endpoint table still unchanged, that marker belongs exactly
to the old origin's interval. This is a transient interval containing a split
atom; the subsequent endpoint-table update makes it the new boundary. -/
theorem marker_routing_after_insert {state : State} {cells : List Cell}
    (origin marker : Address) (representation : Represents state cells)
    (present : origin ∈ state.physical.map Atom.address)
    (freshMarker : marker ∉ state.physical.map Atom.address) :
    ∃ cell, locate state origin = some cell ∧
      locate {state with physical := spliceAfterBy Atom.address origin [boundary marker] state.physical}
        marker = some (insertCell cell origin [boundary marker]) ∧
      (locate {state with physical := spliceAfterBy Atom.address origin [boundary marker] state.physical}
        marker).map Cell.owner = some cell.owner := by
  obtain ⟨cell, ownership, _⟩ := physical_unique_owner origin representation present
  have located := locate_of_member cell origin representation ownership.1 ownership.2
  obtain ⟨before, after, shape⟩ := List.append_of_mem ownership.1
  subst cells
  have apart : List.Disjoint (state.physical.map Atom.address) [marker] := by
    apply List.disjoint_left.mpr
    intro address member selected
    have equal : address = marker := List.mem_singleton.mp selected
    subst address
    exact freshMarker member
  obtain ⟨next, executed, represented⟩ := insert_represents before after cell origin [boundary marker]
    representation ownership.2 (by simp) apart
  simp only [insert, located] at executed
  have nextEq := Option.some.inj executed
  subst next
  have markerActive : marker ∈ (insertCell cell origin [boundary marker]).slice.traversal := by
    simp [insertCell, NotionCoreSource.insertSlice, NotionCoreSource.Slice.traversal, boundary]
  have routed := locate_of_member (insertCell cell origin [boundary marker]) marker represented
    (by simp) markerActive
  exact ⟨cell, located, routed, by rw [routed]; rfl⟩

def erase (state : State) (targets : List Address) : State :=
  {state with physical := state.physical.map (NotionCoreSource.eraseAtom targets)}

def eraseCell (targets : List Address) (cell : Cell) : Cell :=
  {cell with slice := NotionCoreSource.eraseSlice targets cell.slice}

@[simp] theorem erase_atom_address (targets : List Address) (atom : Atom) :
    (NotionCoreSource.eraseAtom targets atom).address = atom.address := by
  cases atom with | mk address kind => cases kind <;> rfl

theorem erase_represents {state : State} {cells : List Cell} (targets : List Address)
    (representation : Represents state cells) :
    Represents (erase state targets) (cells.map (eraseCell targets)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (erase state targets).physical =
      (flatten cells).map (NotionCoreSource.eraseAtom targets) from congrArg
        (List.map (NotionCoreSource.eraseAtom targets)) representation.1]
    simp only [flatten, List.map_flatMap, List.flatMap_map]
    congr 1
  · simpa only [erase, List.map_map, eraseCell, NotionCoreSource.eraseSlice,
      Cell.entry, Function.comp_def] using representation.2.1
  · simpa only [erase, List.map_map, Function.comp_def, erase_atom_address] using representation.2.2.1
  · simpa only [List.map_map, eraseCell, Function.comp_def] using representation.2.2.2

def InteriorText (cells : List Cell) : Prop :=
  ∀ cell ∈ cells, ∀ atom ∈ cell.slice.atoms,
    ∃ value deleted, atom.kind = .text value deleted

private theorem split_interior (before after : List Cell) (cell : Cell)
    (origin marker : Address) (freshOwner : Nat)
    (h : InteriorText (before ++ cell :: after)) :
    InteriorText (before ++ splitCell cell origin marker freshOwner ++ after) := by
  intro selected member atom atomMember
  simp only [List.mem_append] at member
  rcases member with (member | member) | member
  · exact h selected (by simp [member]) atom atomMember
  · simp only [splitCell, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact h cell (by simp) atom (List.mem_of_mem_take atomMember)
    · exact h cell (by simp) atom (List.mem_of_mem_drop atomMember)
  · exact h selected (by simp [member]) atom atomMember

private theorem insert_interior (before after : List Cell) (cell : Cell)
    (origin : Address) (fresh : List Atom)
    (h : InteriorText (before ++ cell :: after))
    (newText : ∀ atom ∈ fresh, ∃ value, atom.kind = .text value false) :
    InteriorText (before ++ insertCell cell origin fresh :: after) := by
  intro selected member atom atomMember
  rcases List.mem_append.mp member with member | member
  · exact h selected (by simp [member]) atom atomMember
  · rcases List.mem_cons.mp member with rfl | member
    · simp only [insertCell, NotionCoreSource.insertSlice, List.mem_append] at atomMember
      rcases atomMember with (member | member) | member
      · exact h cell (by simp) atom (List.mem_of_mem_take member)
      · obtain ⟨value, equal⟩ := newText atom member
        exact ⟨value, false, equal⟩
      · exact h cell (by simp) atom (List.mem_of_mem_drop member)
    · exact h selected (by simp [member]) atom atomMember

private theorem erase_interior (cells : List Cell) (targets : List Address) (h : InteriorText cells) :
    InteriorText (cells.map (eraseCell targets)) := by
  intro cell member atom atomMember
  obtain ⟨old, oldMember, cellEq⟩ := List.mem_map.mp member
  subst cell
  obtain ⟨prior, priorMember, atomEq⟩ := List.mem_map.mp atomMember
  obtain ⟨value, deleted, kind⟩ := h old oldMember prior priorMember
  subst atom
  exact ⟨value, deleted || targets.contains prior.address,
    by simp [NotionCoreSource.eraseAtom, kind]⟩

def initial (owner inst : Nat) : State :=
  ⟨[boundary (inst, .start)], [⟨owner, (inst, .start)⟩]⟩

def initialCell (owner inst : Nat) : Cell := ⟨owner, ⟨(inst, .start), []⟩⟩

theorem initial_represents (owner inst : Nat) : Represents (initial owner inst) [initialCell owner inst] := by
  exact ⟨rfl, rfl, by simp [initial], by simp⟩

/-- Actual raw endpoint execution with input freshness and source-shaped item
kinds. There is no materialized partition, output invariant, or projection
equality in these guards. Origin membership is checked by raw lookup itself. -/
inductive Reach : State → Prop where
  | init (owner inst : Nat) : Reach (initial owner inst)
  | split {state next : State} {origin marker : Address} {freshOwner : Nat} :
      Reach state → marker ∉ state.physical.map Atom.address →
      freshOwner ∉ state.endpoints.map Entry.owner → marker.1 = origin.1 →
      split state origin marker freshOwner = some next → Reach next
  | insert {state next : State} {origin : Address} {fresh : List Atom} :
      Reach state → (fresh.map Atom.address).Nodup →
      List.Disjoint (state.physical.map Atom.address) (fresh.map Atom.address) →
      (∀ atom ∈ fresh, atom.address.1 = origin.1 ∧ ∃ value, atom.kind = .text value false) →
      insert state origin fresh = some next → Reach next
  | erase {state : State} (targets : List Address) : Reach state → Reach (erase state targets)

private theorem located_materialized {state : State} {cells : List Cell} {cell : Cell} {origin : Address}
    (representation : Represents state cells) (located : locate state origin = some cell) :
    cell ∈ cells ∧ origin ∈ cell.slice.traversal := by
  rw [locate, extraction_correct representation] at located
  refine ⟨List.mem_of_find?_eq_some located, ?_⟩
  simpa only [findCell, decide_eq_true_eq] using List.find?_some located

/-- Arbitrarily many raw splits, run insertions and tombstoning deletions
preserve global endpoint coverage and unique ownership. Split markers occur
only at the table's interval boundaries because every interior atom is text. -/
theorem reachable_represents {state : State} (reachable : Reach state) :
    ∃ cells, Represents state cells ∧ InteriorText cells := by
  induction reachable with
  | init owner inst =>
      exact ⟨[initialCell owner inst], initial_represents owner inst,
        by simp [InteriorText, initialCell]⟩
  | @split state next origin marker freshOwner _ freshMarker freshOwnerName sameInstance accepted ih =>
      obtain ⟨cells, representation, interior⟩ := ih
      cases found : locate state origin with
      | none => simp [split, found] at accepted
      | some cell =>
          have ownership := located_materialized representation found
          obtain ⟨before, after, shape⟩ := List.append_of_mem ownership.1
          subst cells
          have freshBlock : freshOwner ∉ (before ++ cell :: after).map Cell.owner := by
            simpa only [representation.2.1, List.map_map, Cell.entry, Function.comp_def] using freshOwnerName
          obtain ⟨result, executed, represented⟩ := split_represents before after cell origin marker freshOwner
            representation ownership.2 freshMarker freshBlock
          rw [executed] at accepted
          have equal := Option.some.inj accepted
          subst next
          exact ⟨_, represented, split_interior before after cell origin marker freshOwner interior⟩
  | @insert state next origin fresh _ newUnique apart newShape accepted ih =>
      obtain ⟨cells, representation, interior⟩ := ih
      cases found : locate state origin with
      | none => simp [insert, found] at accepted
      | some cell =>
          have ownership := located_materialized representation found
          obtain ⟨before, after, shape⟩ := List.append_of_mem ownership.1
          subst cells
          obtain ⟨result, executed, represented⟩ := insert_represents before after cell origin fresh
            representation ownership.2 newUnique apart
          rw [executed] at accepted
          have equal := Option.some.inj accepted
          subst next
          exact ⟨_, represented, insert_interior before after cell origin fresh interior
            (fun atom member => (newShape atom member).2)⟩
  | erase targets _ ih =>
      obtain ⟨cells, representation, interior⟩ := ih
      exact ⟨_, erase_represents targets representation, erase_interior cells targets interior⟩

/-- The actual scan, rather than an existentially chosen projection, provides
the reachable partition and its global address uniqueness. -/
theorem reachable_extraction {state : State} (reachable : Reach state) :
    Represents state (scanCells state.physical state.endpoints) ∧
      InteriorText (scanCells state.physical state.endpoints) := by
  obtain ⟨cells, representation, interior⟩ := reachable_represents reachable
  rw [extraction_correct representation]
  exact ⟨representation, interior⟩

/-! Hand-derived endpoint and repeated-operation controls. The row order below
is physical interval order and does not assert a displayed block order. -/
private def start : Address := (0, .start)
private def a : Atom := ⟨(0, .event (0, 1)), .text 97 false⟩
private def b : Atom := ⟨(0, .event (0, 2)), .text 98 false⟩
private def c : Atom := ⟨(0, .event (0, 3)), .text 99 false⟩
private def x : Atom := ⟨(0, .event (2, 10)), .text 88 false⟩
private def deadB : Atom := ⟨b.address, .text 98 true⟩
private def m1 : Address := (0, .event (1, 10))
private def m2 : Address := (0, .event (3, 10))
private def s1 : State := ⟨[boundary start, a, b, c], [⟨10, start⟩]⟩
private def s2 : State := erase s1 [b.address]
private def s3 : State :=
  ⟨[boundary start, a, deadB, boundary m1, c], [⟨10, start⟩, ⟨11, m1⟩]⟩
private def s4 : State :=
  ⟨[boundary start, a, deadB, x, boundary m1, c], [⟨10, start⟩, ⟨11, m1⟩]⟩
private def s5 : State :=
  ⟨[boundary start, boundary m2, a, deadB, x, boundary m1, c],
    [⟨10, start⟩, ⟨12, m2⟩, ⟨11, m1⟩]⟩

/-- The raw scan excludes both endpoints, retains tombstones, and respects the
next physical interval. A scanner that leaves every atom in the first interval
fails the negative control. -/
theorem endpoint_scan_control :
    scanCells s3.physical s3.endpoints =
      [⟨10, ⟨start, [a, deadB]⟩⟩, ⟨11, ⟨m1, [c]⟩⟩] ∧
    scanCells s3.physical s3.endpoints ≠
      [⟨10, ⟨start, [a, deadB, boundary m1, c]⟩⟩, ⟨11, ⟨m1, []⟩⟩] := by decide

/-- The source's integrate-then-route order finds the new marker in the old
origin's cell, not in the new destination. This marker is transiently interior
because its endpoint row has not yet been installed. -/
theorem marker_routing_control :
    locate {s2 with physical := spliceAfterBy Atom.address b.address [boundary m1] s2.physical} m1 =
      some ⟨10, ⟨start, [a, deadB, boundary m1, c]⟩⟩ ∧
    (locate {s2 with physical := spliceAfterBy Atom.address b.address [boundary m1] s2.physical} m1).map Cell.owner ≠
      some 11 := by decide

/-- Routing is not constantly the first interval: inserting after c in the
second existing interval keeps the marker with owner 11, not owner 10. -/
theorem later_interval_marker_control :
    (locate {s3 with physical := spliceAfterBy Atom.address c.address [boundary m2] s3.physical} m2).map Cell.owner =
      some 11 ∧
    (locate {s3 with physical := spliceAfterBy Atom.address c.address [boundary m2] s3.physical} m2).map Cell.owner ≠
      some 10 := by decide

/-- A deleted origin still has an owner; it is not treated as missing. -/
theorem tombstone_owner_control :
    locate s3 b.address = some ⟨10, ⟨start, [a, deadB]⟩⟩ ∧
    locate s3 b.address ≠ none := by decide

/-- Actual raw execution exercises deletion followed by a hidden-origin split,
a run insertion at that same hidden origin, and a repeated START split. -/
theorem repeated_operations_control :
    Reach s5 ∧
    (scanCells s5.physical s5.endpoints).map
      (fun cell => (cell.owner, NotionCoreSpec.text cell.slice.slots)) =
      [(10, []), (12, [97, 88]), (11, [99])] ∧
    (scanCells s5.physical s5.endpoints).map
      (fun cell => (cell.owner, NotionCoreSpec.text cell.slice.slots)) ≠
      [(10, [97, 88]), (12, []), (11, [99])] := by
  have r0 : Reach (initial 10 0) := .init 10 0
  have r1 : Reach s1 := .insert (origin := start) (fresh := [a, b, c]) r0 (by decide)
    (by simp [initial, boundary, a, b, c])
    (by simp [a, b, c, start]) (by decide)
  have r2 : Reach s2 := .erase [b.address] r1
  have r3 : Reach s3 := .split (origin := b.address) (marker := m1) (freshOwner := 11) r2 (by decide) (by decide) rfl (by decide)
  have r4 : Reach s4 := .insert (origin := b.address) (fresh := [x]) r3 (by decide)
    (by simp [s3, boundary, start, a, deadB, b, m1, c, x])
    (by simp [x, b]) (by decide)
  have r5 : Reach s5 := .split (origin := start) (marker := m2) (freshOwner := 12) r4 (by decide) (by decide) rfl (by decide)
  exact ⟨r5, by decide, by decide⟩

#print axioms extraction_correct
#print axioms physical_unique_owner
#print axioms marker_routing_after_insert
#print axioms split_refines
#print axioms reachable_extraction

end Sal.MRDTs.Instances.NotionCorePartition
