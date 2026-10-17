import Sal.MRDTs.Instances.NotionCoreSpec

/-! Materialized interval normal form for the create/split/insert/delete/merge
core. An instance is an ordered partition of physical atoms into slices. A
block holds the slices of its chain in preorder: its own root interval first,
then the intervals that splits and merges attached below it. A dead title,
the root interval of a split destination, stays permanently empty. This file
proves normal-form preservation and projection calculations. It does not prove
extraction of this partition from JavaScript's RGA/endpoint tree.
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

/-- Insert a physical marker at a traversal coordinate inside a slice and split
that interval. The source-derived provenance lemma must justify the
coordinate's relation to the identity-addressed origin. The coordinate counts
retained physical atoms. -/
def splitSlice (slice : Slice) (position : Nat) (marker : Address) : Slice × Slice :=
  (⟨slice.start, slice.atoms.take position⟩,
   ⟨marker, slice.atoms.drop position⟩)

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

@[simp] theorem eraseSlice_nil (slice : Slice) : eraseSlice [] slice = slice := by
  cases slice with
  | mk start atoms =>
    simp only [eraseSlice, Slice.mk.injEq, true_and]
    conv_rhs => rw [← List.map_id atoms]
    apply List.map_congr_left
    intro atom _
    cases atom with
    | mk address kind => cases kind <;> simp [eraseAtom]

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

@[simp] theorem Atom.slot_address (atom : Atom) : atom.slot.address = atom.address := by
  cases atom with | mk address kind => cases kind <;> rfl

@[simp] theorem Slice.slots_addresses (slice : Slice) :
    slice.slots.map Slot.address = slice.traversal := by
  simp [Slice.slots, Slice.anchor, Slice.traversal]

/-- Cutting after an address of the first part leaves the second part whole. -/
theorem cutAfter_append_left (a b : List Slot) (origin : Address)
    (present : origin ∈ a.map Slot.address) :
    NotionCoreSpec.cutAfter (a ++ b) origin =
      ((NotionCoreSpec.cutAfter a origin).1, (NotionCoreSpec.cutAfter a origin).2 ++ b) := by
  have index : ((a ++ b).map Slot.address).idxOf origin = (a.map Slot.address).idxOf origin := by
    rw [List.map_append]
    exact List.idxOf_append_of_mem present
  have bound : (a.map Slot.address).idxOf origin + 1 ≤ a.length := by
    have within := List.idxOf_lt_length_of_mem present
    simp only [List.length_map] at within
    omega
  simp only [NotionCoreSpec.cutAfter, index]
  rw [List.take_append_of_le_length bound, List.drop_append_of_le_length bound]

/-- Cutting after an address absent from the first part keeps the first part whole. -/
theorem cutAfter_append_right (a b : List Slot) (origin : Address)
    (absent : origin ∉ a.map Slot.address) :
    NotionCoreSpec.cutAfter (a ++ b) origin =
      (a ++ (NotionCoreSpec.cutAfter b origin).1, (NotionCoreSpec.cutAfter b origin).2) := by
  have index : ((a ++ b).map Slot.address).idxOf origin =
      a.length + (b.map Slot.address).idxOf origin := by
    rw [List.map_append, List.idxOf_append_of_notMem absent]
    simp
  simp only [NotionCoreSpec.cutAfter, index, Nat.add_assoc]
  rw [List.take_length_add_append, List.drop_length_add_append]

/-- A block of the materialized source document: its name, the text instance
it was created with, and the slices of its chain in preorder. An alive
block's first slice is its own root interval; a block merged into another is
a tombstone that holds no slices. -/
structure Block where
  id : Nat
  inst : Nat
  slices : List Slice
  deriving DecidableEq, Repr

/-- Liveness is derived: a block is alive while it holds slices. -/
def Block.alive (block : Block) : Bool := !block.slices.isEmpty

def Block.slots (block : Block) : List Slot := block.slices.flatMap Slice.slots

def Block.traversal (block : Block) : List Address := block.slices.flatMap Slice.traversal

def Block.project (block : Block) : NotionCoreSpec.Block :=
  ⟨block.id, block.inst, block.slots, block.alive⟩

@[simp] theorem Block.slots_addresses (block : Block) :
    block.slots.map Slot.address = block.traversal := by
  simp [Block.slots, Block.traversal, List.map_flatMap]

/-- The slices of a chain followed by a slice that starts at a split marker
rather than opening an instance: the dead title roots of split destinations. -/
def deadSlices : List Slice → List Slice
  | [] => []
  | [_] => []
  | slice :: next :: rest =>
      (if next.start.2 = .start then [] else [slice]) ++ deadSlices (next :: rest)

/-- Chain normal form: atoms lie in their slice's instance, an alive block's
first slice is the root interval of its own instance, and every dead title is
an empty instance root. -/
def Block.Normal (block : Block) : Prop :=
  (∀ slice ∈ block.slices, ∀ atom ∈ slice.atoms, atom.address.1 = slice.start.1) ∧
  (∀ head ∈ block.slices.head?, head.start = (block.inst, .start)) ∧
  ∀ dead ∈ deadSlices block.slices, dead.start.2 = .start ∧ dead.atoms = []

/-- Cut a chain after `origin`: the slices before the one holding it stay,
that slice is split at the origin's coordinate, and its right part and every
later slice move. -/
def splitSlices (origin marker : Address) : List Slice → List Slice × List Slice
  | [] => ([], [])
  | slice :: rest =>
      if origin ∈ slice.traversal then
        ([(splitSlice slice (slice.traversal.idxOf origin) marker).1],
          (splitSlice slice (slice.traversal.idxOf origin) marker).2 :: rest)
      else
        ((slice :: (splitSlices origin marker rest).1), (splitSlices origin marker rest).2)

/-- The cut chain projects to the semantic cut after the origin's address,
with the marker's hidden slot heading the moved part. -/
theorem splitSlices_projection (origin marker : Address) (slices : List Slice)
    (present : origin ∈ slices.flatMap Slice.traversal) :
    (splitSlices origin marker slices).1.flatMap Slice.slots =
        (NotionCoreSpec.cutAfter (slices.flatMap Slice.slots) origin).1 ∧
    (splitSlices origin marker slices).2.flatMap Slice.slots =
        (⟨marker, 0, false⟩ : Slot) ::
          (NotionCoreSpec.cutAfter (slices.flatMap Slice.slots) origin).2 := by
  induction slices with
  | nil => simp at present
  | cons slice rest ih =>
    by_cases inside : origin ∈ slice.traversal
    · have cut := split_slice_identity_projection slice origin (slice.traversal.idxOf origin) marker
        (by rw [Slice.slots_addresses])
      have outer := cutAfter_append_left slice.slots (rest.flatMap Slice.slots) origin
        (by rw [Slice.slots_addresses]; exact inside)
      simp only [splitSlices, inside, ↓reduceIte, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, outer]
      exact ⟨cut.1, by rw [cut.2]; rfl⟩
    · have later : origin ∈ rest.flatMap Slice.traversal := by
        simp only [List.flatMap_cons, List.mem_append] at present
        exact present.resolve_left inside
      have outer := cutAfter_append_right slice.slots (rest.flatMap Slice.slots) origin
        (by rw [Slice.slots_addresses]; exact inside)
      obtain ⟨left, right⟩ := ih later
      simp only [splitSlices, inside, ↓reduceIte, List.flatMap_cons, outer]
      exact ⟨by rw [left], right⟩

/-- A chain whose only slice holding the origin is preceded by slices not
holding it is cut exactly at that slice. -/
theorem splitSlices_focus (origin marker : Address) (pre : List Slice) (slice : Slice)
    (post : List Slice) (absent : ∀ other ∈ pre, origin ∉ other.traversal)
    (held : origin ∈ slice.traversal) :
    splitSlices origin marker (pre ++ slice :: post) =
      (pre ++ [(splitSlice slice (slice.traversal.idxOf origin) marker).1],
        (splitSlice slice (slice.traversal.idxOf origin) marker).2 :: post) := by
  induction pre with
  | nil => simp [splitSlices, held]
  | cons first rest ih =>
    have outside := absent first (by simp)
    rw [List.cons_append, splitSlices, if_neg outside,
      ih (fun other member => absent other (List.mem_cons_of_mem _ member))]
    simp

theorem splitSlices_left_ne_nil (origin marker : Address) (slices : List Slice)
    (present : origin ∈ slices.flatMap Slice.traversal) :
    (splitSlices origin marker slices).1 ≠ [] := by
  cases slices with
  | nil => simp at present
  | cons slice rest =>
    unfold splitSlices
    split <;> simp

/-- Insert after `origin` in every slice that holds it; on a chain with
unique addresses that is exactly one slice. -/
def insertSlices (origin : Address) (fresh : List Atom) (slices : List Slice) : List Slice :=
  slices.map fun slice =>
    if origin ∈ slice.traversal then insertSlice slice (slice.traversal.idxOf origin) fresh
    else slice

theorem insertSlices_projection (origin : Address) (fresh : List Atom) (slices : List Slice)
    (unique : (slices.flatMap Slice.traversal).Nodup)
    (present : origin ∈ slices.flatMap Slice.traversal) :
    (insertSlices origin fresh slices).flatMap Slice.slots =
      NotionCoreSpec.insertSlots origin (fresh.map Atom.slot) (slices.flatMap Slice.slots) := by
  induction slices with
  | nil => simp at present
  | cons slice rest ih =>
    simp only [List.flatMap_cons] at unique present
    obtain ⟨_, restUnique, disjoint⟩ := List.nodup_append.mp unique
    by_cases inside : origin ∈ slice.traversal
    · have absent : origin ∉ rest.flatMap Slice.traversal := fun later =>
        disjoint origin inside origin later rfl
      have restSame : insertSlices origin fresh rest = rest := by
        unfold insertSlices
        conv_rhs => rw [← List.map_id rest]
        apply List.map_congr_left
        intro other member
        have outside : origin ∉ other.traversal := fun held =>
          absent (List.mem_flatMap.mpr ⟨other, member, held⟩)
        simp [outside]
      have cut := insert_slice_identity_projection slice origin (slice.traversal.idxOf origin) fresh
        (by rw [Slice.slots_addresses])
      have outer := cutAfter_append_left slice.slots (rest.flatMap Slice.slots) origin
        (by rw [Slice.slots_addresses]; exact inside)
      have head : insertSlices origin fresh (slice :: rest) =
          insertSlice slice (slice.traversal.idxOf origin) fresh :: insertSlices origin fresh rest := by
        simp [insertSlices, inside]
      rw [head, restSame, List.flatMap_cons, cut]
      simp only [NotionCoreSpec.insertSlots, List.flatMap_cons, outer, List.append_assoc]
    · have later : origin ∈ rest.flatMap Slice.traversal := (List.mem_append.mp present).resolve_left inside
      have outer := cutAfter_append_right slice.slots (rest.flatMap Slice.slots) origin
        (by rw [Slice.slots_addresses]; exact inside)
      have head : insertSlices origin fresh (slice :: rest) = slice :: insertSlices origin fresh rest := by
        simp [insertSlices, inside]
      rw [head, List.flatMap_cons, ih restUnique later]
      simp only [NotionCoreSpec.insertSlots, List.flatMap_cons, outer, List.append_assoc]

theorem eraseSlices_projection (targets : List Address) (slices : List Slice) :
    (slices.map (eraseSlice targets)).flatMap Slice.slots =
      (slices.flatMap Slice.slots).map (NotionCoreSpec.eraseSlot targets) := by
  simp [List.flatMap_map, List.map_flatMap, erase_slice_projection]

/-! Normal-form preservation. -/

theorem deadSlices_map (f : Slice → Slice) (start : ∀ slice, (f slice).start = slice.start)
    (slices : List Slice) : deadSlices (slices.map f) = (deadSlices slices).map f := by
  induction slices with
  | nil => rfl
  | cons slice rest ih =>
    cases rest with
    | nil => rfl
    | cons next tail =>
      simp only [List.map_cons] at ih ⊢
      simp only [deadSlices, ih, start]
      split <;> simp

theorem deadSlices_sub (slices : List Slice) : deadSlices slices ⊆ slices := by
  induction slices with
  | nil => simp [deadSlices]
  | cons slice rest ih =>
    cases rest with
    | nil => simp [deadSlices]
    | cons next tail =>
      intro dead member
      simp only [deadSlices, List.mem_append] at member
      rcases member with here | later
      · split at here <;> simp_all
      · exact List.mem_cons_of_mem _ (ih later)

/-- Appending a chain that opens an instance adds no dead title. -/
theorem deadSlices_append_open (pre : List Slice) (next : Slice) (post : List Slice)
    (opens : next.start.2 = .start) :
    deadSlices (pre ++ next :: post) = deadSlices pre ++ deadSlices (next :: post) := by
  induction pre with
  | nil => rfl
  | cons slice rest ih =>
    cases rest with
    | nil => simp [deadSlices, opens]
    | cons other tail =>
      simp only [List.cons_append] at ih ⊢
      simp only [deadSlices, ih, List.append_assoc]

/-- A slice holding a split origin that is not a dead title is followed, if
at all, by a slice opening an instance. -/
theorem deadSlices_cons_live (slice : Slice) (rest : List Slice)
    (live : slice ∉ deadSlices (slice :: rest)) :
    deadSlices (slice :: rest) = deadSlices rest ∧ ∀ next ∈ rest.head?, next.start.2 = .start := by
  cases rest with
  | nil => simp [deadSlices]
  | cons next tail =>
    by_cases opens : next.start.2 = .start
    · simp [deadSlices, opens]
    · simp [deadSlices, opens] at live

theorem erase_normal (block : Block) (targets : List Address) (normal : block.Normal) :
    ({block with slices := block.slices.map (eraseSlice targets)} : Block).Normal := by
  obtain ⟨atoms, head, dead⟩ := normal
  refine ⟨?_, ?_, ?_⟩
  · intro slice member atom inside
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp inside
    simpa [eraseAtom, eraseSlice] using atoms old oldMember original originalMember
  · intro first member
    cases slices : block.slices with
    | nil => simp [slices] at member
    | cons old rest =>
      simp only [slices, List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at member
      subst first
      simpa [eraseSlice] using head old (by simp [slices])
  · intro slice member
    rw [deadSlices_map (eraseSlice targets) (fun _ => rfl)] at member
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨opens, empty⟩ := dead old oldMember
    exact ⟨opens, by simp [eraseSlice, empty]⟩

theorem insert_normal (block : Block) (origin : Address) (fresh : List Atom)
    (normal : block.Normal)
    (sameInstance : ∀ atom ∈ fresh, atom.address.1 = origin.1)
    (live : ∀ dead ∈ deadSlices block.slices, origin ∉ dead.traversal) :
    ({block with slices := insertSlices origin fresh block.slices} : Block).Normal := by
  obtain ⟨atoms, head, dead⟩ := normal
  have startSame : ∀ slice : Slice,
      (if origin ∈ slice.traversal then insertSlice slice (slice.traversal.idxOf origin) fresh
        else slice).start = slice.start := by
    intro slice
    split <;> rfl
  refine ⟨?_, ?_, ?_⟩
  · intro slice member atom inside
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    rw [startSame old]
    by_cases holds : origin ∈ old.traversal
    · simp only [holds, ↓reduceIte, insertSlice, List.mem_append] at inside
      have originInst : origin.1 = old.start.1 := by
        rcases List.mem_cons.mp holds with equal | later
        · rw [equal]
        · obtain ⟨held, heldMember, rfl⟩ := List.mem_map.mp later
          exact atoms old oldMember held heldMember
      rcases inside with (inside | inside) | inside
      · exact atoms old oldMember atom (List.mem_of_mem_take inside)
      · exact (sameInstance atom inside).trans originInst
      · exact atoms old oldMember atom (List.mem_of_mem_drop inside)
    · simp only [holds, ↓reduceIte] at inside
      exact atoms old oldMember atom inside
  · intro first member
    cases slices : block.slices with
    | nil => simp [slices, insertSlices] at member
    | cons old rest =>
      simp only [slices, insertSlices, List.map_cons, List.head?_cons, Option.mem_def,
        Option.some.injEq] at member
      subst first
      rw [startSame]
      exact head old (by simp [slices])
  · intro slice member
    unfold insertSlices at member
    rw [deadSlices_map _ (fun slice => startSame slice)] at member
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    have untouched : origin ∉ old.traversal := live old oldMember
    simpa [untouched] using dead old oldMember

/-- Appending an alive normal chain below the last slice of a normal chain
keeps the holder normal. -/
theorem append_normal (holder source : Block) (holderNormal : holder.Normal)
    (sourceNormal : source.Normal) (holderAlive : holder.alive = true)
    (alive : source.alive = true) :
    ({holder with slices := holder.slices ++ source.slices} : Block).Normal := by
  obtain ⟨holderAtoms, holderHead, holderDead⟩ := holderNormal
  obtain ⟨sourceAtoms, sourceHead, sourceDead⟩ := sourceNormal
  cases sourceSlices : source.slices with
  | nil => simp [Block.alive, sourceSlices] at alive
  | cons root rest =>
    have opens : root.start.2 = .start := by
      rw [sourceHead root (by simp [sourceSlices])]
    refine ⟨?_, ?_, ?_⟩
    · intro slice member
      rcases List.mem_append.mp member with old | moved
      · exact holderAtoms slice old
      · exact sourceAtoms slice (sourceSlices ▸ moved)
    · intro first member
      cases holderSlices : holder.slices with
      | nil => simp [Block.alive, holderSlices] at holderAlive
      | cons old others =>
        simp only [holderSlices, List.cons_append, List.head?_cons, Option.mem_def,
          Option.some.injEq] at member
        subst first
        exact holderHead old (by simp [holderSlices])
    · intro slice member
      simp only at member
      rw [deadSlices_append_open _ _ _ opens, List.mem_append] at member
      rcases member with old | moved
      · exact holderDead slice old
      · exact sourceDead slice (sourceSlices ▸ moved)

theorem deadSlices_tail (slice : Slice) (rest : List Slice) :
    deadSlices rest ⊆ deadSlices (slice :: rest) := by
  cases rest with
  | nil => simp [deadSlices]
  | cons next tail => exact fun dead member => by simp [deadSlices, member]

/-- The parts of a cut chain: every kept slice is an old slice or the left
part of one, and the moved part is the right part of the slice holding the
origin followed by old slices. -/
theorem splitSlices_parts (origin marker : Address) (slices : List Slice)
    (present : origin ∈ slices.flatMap Slice.traversal) :
    (∀ kept ∈ (splitSlices origin marker slices).1,
      ∃ old ∈ slices, kept.start = old.start ∧ kept.atoms ⊆ old.atoms) ∧
    (∃ old ∈ slices, origin ∈ old.traversal ∧ ∃ right later,
      (splitSlices origin marker slices).2 = right :: later ∧ right.start = marker ∧
      right.atoms ⊆ old.atoms ∧ later ⊆ slices) ∧
    (splitSlices origin marker slices).1.head?.map Slice.start = slices.head?.map Slice.start := by
  induction slices with
  | nil => simp at present
  | cons slice rest ih =>
    by_cases inside : origin ∈ slice.traversal
    · simp only [splitSlices, inside, ↓reduceIte]
      refine ⟨?_, ⟨slice, by simp, inside, _, rest, rfl, rfl, ?_, fun x m => by simp [m]⟩, rfl⟩
      · intro kept member
        simp only [List.mem_singleton] at member
        subst kept
        exact ⟨slice, by simp, rfl, fun atom held => List.mem_of_mem_take held⟩
      · exact fun atom held => List.mem_of_mem_drop held
    · have later : origin ∈ rest.flatMap Slice.traversal := by
        simp only [List.flatMap_cons, List.mem_append] at present
        exact present.resolve_left inside
      obtain ⟨keptOld, ⟨old, oldMember, held, right, tail, moved, start, atoms, tailOld⟩, _⟩ := ih later
      simp only [splitSlices, inside, ↓reduceIte]
      refine ⟨?_, ⟨old, by simp [oldMember], held, right, tail, moved, start, atoms,
        fun x m => List.mem_cons_of_mem _ (tailOld m)⟩, rfl⟩
      intro kept member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨kept, by simp, rfl, fun _ held => held⟩
      · obtain ⟨old, oldMember, start, atoms⟩ := keptOld kept member
        exact ⟨old, List.mem_cons_of_mem _ oldMember, start, atoms⟩

/-- Cutting a chain at a live slice creates no dead title in either part. -/
theorem splitSlices_dead (origin marker : Address) (slices : List Slice)
    (present : origin ∈ slices.flatMap Slice.traversal)
    (live : ∀ dead ∈ deadSlices slices, origin ∉ dead.traversal) :
    (∀ dead ∈ deadSlices (splitSlices origin marker slices).1, dead ∈ deadSlices slices) ∧
    (∀ dead ∈ deadSlices (splitSlices origin marker slices).2, dead ∈ deadSlices slices) := by
  induction slices with
  | nil => simp at present
  | cons slice rest ih =>
    by_cases inside : origin ∈ slice.traversal
    · simp only [splitSlices, inside, ↓reduceIte]
      have notDead : slice ∉ deadSlices (slice :: rest) := fun dead => live slice dead inside
      obtain ⟨same, opens⟩ := deadSlices_cons_live slice rest notDead
      refine ⟨by simp [deadSlices], ?_⟩
      intro dead member
      cases rest with
      | nil => simp [deadSlices] at member
      | cons next tail =>
        have nextOpens : next.start.2 = .start := opens next rfl
        simp only [deadSlices, nextOpens, ↓reduceIte, List.nil_append] at member
        rw [same]
        exact member
    · have later : origin ∈ rest.flatMap Slice.traversal := by
        simp only [List.flatMap_cons, List.mem_append] at present
        exact present.resolve_left inside
      obtain ⟨left, right⟩ := ih later
        (fun dead member => live dead (deadSlices_tail slice rest member))
      simp only [splitSlices, inside, ↓reduceIte]
      refine ⟨?_, fun dead member => deadSlices_tail slice rest (right dead member)⟩
      have heads := (splitSlices_parts origin marker rest later).2.2
      obtain ⟨first, kept, keptEq⟩ : ∃ first kept, (splitSlices origin marker rest).1 = first :: kept := by
        cases h : (splitSlices origin marker rest).1 with
        | nil => exact absurd h (splitSlices_left_ne_nil origin marker rest later)
        | cons first kept => exact ⟨first, kept, rfl⟩
      obtain ⟨next, tail, restEq⟩ : ∃ next tail, rest = next :: tail := by
        cases rest with
        | nil => simp at later
        | cons next tail => exact ⟨next, tail, rfl⟩
      rw [keptEq, restEq] at heads
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at heads
      intro dead member
      rw [keptEq] at member left
      simp only [deadSlices, heads, List.mem_append] at member
      rw [restEq]
      simp only [deadSlices, List.mem_append]
      rcases member with here | there
      · exact Or.inl here
      · exact Or.inr (restEq ▸ left dead there)

theorem split_normal (block : Block) (origin marker : Address) (destination : Nat)
    (normal : block.Normal)
    (present : origin ∈ block.traversal)
    (sameInstance : marker.1 = origin.1) (markerEvent : marker.2 ≠ .start)
    (live : ∀ dead ∈ deadSlices block.slices, origin ∉ dead.traversal) :
    ({block with slices := (splitSlices origin marker block.slices).1} : Block).Normal ∧
    (⟨destination, destination, ⟨(destination, .start), []⟩ ::
      (splitSlices origin marker block.slices).2⟩ : Block).Normal := by
  obtain ⟨atoms, head, dead⟩ := normal
  obtain ⟨keptOld, ⟨old, oldMember, held, right, later, moved, rightStart, rightAtoms, laterOld⟩,
    heads⟩ := splitSlices_parts origin marker block.slices present
  obtain ⟨leftDead, rightDead⟩ := splitSlices_dead origin marker block.slices present live
  have originInst : origin.1 = old.start.1 := by
    rcases List.mem_cons.mp held with equal | inner
    · rw [equal]
    · obtain ⟨atom, atomMember, rfl⟩ := List.mem_map.mp inner
      exact atoms old oldMember atom atomMember
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro kept member atom inside
      obtain ⟨source, sourceMember, start, sub⟩ := keptOld kept member
      rw [start]
      exact atoms source sourceMember atom (sub inside)
    · intro first member
      have mapped := congrArg (Option.map Slice.start) (Option.mem_def.mp member)
      simp only at mapped
      rw [heads] at mapped
      cases slices : block.slices with
      | nil => simp [slices] at mapped
      | cons original rest =>
        simp only [slices, List.head?_cons, Option.map_some, Option.some.injEq] at mapped
        rw [← mapped]
        exact head original (by simp [slices])
    · intro kept member
      exact dead kept (leftDead kept member)
  · refine ⟨?_, by simp, ?_⟩
    · intro slice member atom inside
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simp at inside
      · rw [moved] at member
        rcases List.mem_cons.mp member with rfl | member
        · rw [rightStart, sameInstance, originInst]
          exact atoms old oldMember atom (rightAtoms inside)
        · exact atoms slice (laterOld member) atom inside
    · intro slice member
      simp only at member
      rw [moved] at member rightDead
      simp only [deadSlices, rightStart, markerEvent, ↓reduceIte, List.singleton_append,
        List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨rfl, rfl⟩
      · exact dead slice (rightDead slice member)

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

#print axioms split_slice_identity_projection
#print axioms splitSlices_projection
#print axioms insertSlices_projection
#print axioms split_normal
end Sal.MRDTs.Instances.NotionCoreSource
