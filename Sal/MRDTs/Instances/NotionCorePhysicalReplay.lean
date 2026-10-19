import Sal.MRDTs.Instances.NotionCoreOriginTree
import Sal.MRDTs.Instances.NotionCorePartition
import Mathlib.Logic.Equiv.List

/-! Typed integration of source origin-tree traversal and raw endpoint replay.
Semantic event names encode source sessions injectively, without claiming any
order preservation. Source comparator order remains in OriginTree's premises.
Parent-map extraction and issuance of the coupled invariants remain separate.
-/
namespace Sal.MRDTs.Instances.NotionCorePhysicalReplay
open NotionRunAllocation (Id)
open NotionCoreSpec (Address LocalId)
open NotionCoreSource (Atom)

/-- A semantic name, not a timestamp or an order-preserving session rank. -/
def localId (id : Id) : LocalId := .event (Encodable.encode id.session, id.counter)
def address (inst : Nat) (id : Id) : Address := (inst, localId id)

/-- The event key of an identity: the pair a split marker is named by in the
source command language. -/
def markerKey (id : Id) : Nat × Nat := (Encodable.encode id.session, id.counter)

theorem address_markerKey (inst : Nat) (id : Id) : address inst id = (inst, .event (markerKey id)) :=
  rfl

theorem localId_injective : Function.Injective localId := by
  intro a b equal
  have components : (Encodable.encode a.session, a.counter) =
      (Encodable.encode b.session, b.counter) := by simpa [localId] using equal
  have session : a.session = b.session := Encodable.encode_injective (congrArg Prod.fst components)
  have counter : a.counter = b.counter := congrArg Prod.snd components
  cases a; cases b; simp_all

theorem address_injective (inst : Nat) : Function.Injective (address inst) := by
  intro a b equal
  exact localId_injective (congrArg Prod.snd equal)

@[simp] theorem address_ne_start (inst : Nat) (id : Id) :
    address inst id ≠ (inst, .start) := by simp [address, localId]

def atom (inst : Nat) (item : NotionCoreOriginTree.Item) : Atom :=
  ⟨address inst item.id, match item.kind with
    | .text value deleted => .text value deleted
    | .split => .split⟩

def start (inst : Nat) : Atom := NotionCorePartition.boundary (inst, .start)
def physical (inst : Nat) (items : List NotionCoreOriginTree.Item) : List Atom :=
  start inst :: items.map (atom inst)
def augmented (inst : Nat) (forest : NotionCoreOriginTree.Forest) : List Atom :=
  physical inst (NotionCoreOriginTree.preorder forest)

def originAddress (inst : Nat) : NotionCoreOriginTree.Origin → Address
  | .start => (inst, .start)
  | .item id => address inst id

@[simp] theorem atom_address (inst : Nat) (item : NotionCoreOriginTree.Item) :
    (atom inst item).address = address inst item.id := rfl
@[simp] theorem start_address (inst : Nat) : (start inst).address = (inst, .start) := rfl

private theorem idxOf_map_injective {A B : Type} [BEq A] [LawfulBEq A] [BEq B] [LawfulBEq B]
    (f : A → B) (injective : Function.Injective f) (value : A) (items : List A) :
    (items.map f).idxOf (f value) = items.idxOf value := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    by_cases equal : item = value
    · simp [equal]
    · have apart : f item ≠ f value := fun h => equal (injective h)
      simp [equal, apart, ih]

theorem physical_origin_index (inst : Nat) (id : Id)
    (items : List NotionCoreOriginTree.Item) :
    ((physical inst items).map Atom.address).idxOf (address inst id) =
      (items.map NotionCoreOriginTree.Item.id).idxOf id + 1 := by
  have mapped : ((items.map (atom inst)).map Atom.address) =
      (items.map NotionCoreOriginTree.Item.id).map (address inst) := by
    simp [List.map_map, Function.comp_def]
  simp only [physical, List.map_cons, start_address, mapped]
  rw [List.idxOf_cons]
  have unequal : (((inst, .start) : Address) == address inst id) = false := by
    simp [address, localId]
  simp only [unequal, Bool.cond_false]
  exact congrArg (· + 1) (idxOf_map_injective (address inst) (address_injective inst) id
    (items.map NotionCoreOriginTree.Item.id))

/-- Transport the source's derived identity splice to the augmented raw
physical interval machine, including its virtual START atom. -/
theorem physical_splice (inst : Nat) (id : Id)
    (fresh items : List NotionCoreOriginTree.Item)
    (present : id ∈ items.map NotionCoreOriginTree.Item.id) :
    (NotionCoreOriginTree.spliceAfter id fresh items).map (physical inst) =
      some (NotionCorePartition.spliceAfterBy Atom.address (address inst id)
        (fresh.map (atom inst)) (physical inst items)) := by
  rw [NotionCoreOriginTree.spliceAfter_indices id fresh items present]
  simp only [Option.map_some, NotionCorePartition.spliceAfterBy]
  rw [physical_origin_index]
  simp [physical, List.map_take, List.map_drop, List.append_assoc]

def Present (origin : NotionCoreOriginTree.Origin) (forest : NotionCoreOriginTree.Forest) : Prop :=
  match origin with
  | .start => True
  | .item id => id ∈ (NotionCoreOriginTree.preorder forest).map NotionCoreOriginTree.Item.id

/-- Actual source-tree search and insertion transports to exactly the raw
splice used by endpoint replay. This is a physical-state equation, not a
rendering/correctness assumption. The tree theorem derives the context. -/
theorem tree_insert_physical (inst : Nat) (origin : NotionCoreOriginTree.Origin)
    (fresh : NotionCoreOriginTree.Tree) (forest : NotionCoreOriginTree.Forest)
    (ready : NotionCoreOriginTree.Ready origin fresh forest) (present : Present origin forest) :
    (NotionCoreOriginTree.insert origin fresh forest).map (augmented inst) =
      some (NotionCorePartition.spliceAfterBy Atom.address (originAddress inst origin)
        ((NotionCoreOriginTree.preorderTree fresh).map (atom inst)) (augmented inst forest)) := by
  have projected := NotionCoreOriginTree.insert_preorder origin fresh forest ready
  have transported := congrArg (Option.map (physical inst)) projected
  simp only [Option.map_map, Function.comp_def] at transported
  change (NotionCoreOriginTree.insert origin fresh forest).map (augmented inst) = _ at transported
  rw [transported]
  cases origin with
  | start =>
    simp [NotionCoreOriginTree.linearInsert, NotionCorePartition.spliceAfterBy,
      originAddress, augmented, physical]
  | item id =>
    exact physical_splice inst id _ _ present

theorem origin_present_physical (inst : Nat) (origin : NotionCoreOriginTree.Origin)
    (forest : NotionCoreOriginTree.Forest) (present : Present origin forest) :
    originAddress inst origin ∈ (augmented inst forest).map Atom.address := by
  cases origin with
  | start => simp [originAddress, augmented, physical]
  | item id =>
    obtain ⟨item, member, equal⟩ := List.mem_map.mp present
    apply List.mem_map.mpr
    refine ⟨atom inst item, ?_, ?_⟩
    · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨item, member, rfl⟩)
    · simpa [originAddress] using congrArg (address inst) equal

theorem fresh_addresses_unique (inst : Nat) (fresh : List NotionCoreOriginTree.Item)
    (unique : (fresh.map NotionCoreOriginTree.Item.id).Nodup) :
    ((fresh.map (atom inst)).map Atom.address).Nodup := by
  have mapped := unique.map (address_injective inst)
  simpa only [List.map_map, Function.comp_def, atom_address] using mapped

theorem physical_disjoint (inst : Nat) (old fresh : List NotionCoreOriginTree.Item)
    (apart : List.Disjoint (old.map NotionCoreOriginTree.Item.id)
      (fresh.map NotionCoreOriginTree.Item.id)) :
    List.Disjoint ((physical inst old).map Atom.address)
      ((fresh.map (atom inst)).map Atom.address) := by
  apply List.disjoint_left.mpr
  intro key oldMember freshMember
  simp only [physical, List.map_cons, start_address, List.map_map, Function.comp_def,
    atom_address, List.mem_cons] at oldMember freshMember
  obtain ⟨newItem, newMember, newKey⟩ := List.mem_map.mp freshMember
  rcases oldMember with isStart | oldMember
  · exact address_ne_start inst newItem.id (newKey.trans isStart)
  · obtain ⟨oldItem, oldMember, oldKey⟩ := List.mem_map.mp oldMember
    have same : oldItem.id = newItem.id := address_injective inst (oldKey.trans newKey.symm)
    exact List.disjoint_left.mp apart (List.mem_map.mpr ⟨oldItem, oldMember, same⟩)
      (List.mem_map.mpr ⟨newItem, newMember, rfl⟩)

/-- The represented raw partition remains coupled to the actual inserted
origin tree, and endpoint scanning recovers its computed materialized update.
The input equality couples two physical representations; no rendering law is
assumed. Source allocation must still derive freshness and Ready. -/
theorem tree_insert_partition (inst : Nat) (origin : NotionCoreOriginTree.Origin)
    (fresh : NotionCoreOriginTree.Tree) (old next : NotionCoreOriginTree.Forest)
    (state : NotionCorePartition.State) (cells : List NotionCorePartition.Cell)
    (coupled : state.physical = augmented inst old)
    (represented : NotionCorePartition.Represents state cells)
    (chained : NotionCorePartition.Chained cells)
    (ready : NotionCoreOriginTree.Ready origin fresh old) (present : Present origin old)
    (newUnique : ((NotionCoreOriginTree.preorderTree fresh).map NotionCoreOriginTree.Item.id).Nodup)
    (apart : List.Disjoint ((NotionCoreOriginTree.preorder old).map NotionCoreOriginTree.Item.id)
      ((NotionCoreOriginTree.preorderTree fresh).map NotionCoreOriginTree.Item.id))
    (accepted : NotionCoreOriginTree.insert origin fresh old = some next) :
    ∃ before cell after rawNext,
      cells = before ++ cell :: after ∧
      NotionCorePartition.insert state (originAddress inst origin)
        ((NotionCoreOriginTree.preorderTree fresh).map (atom inst)) = some rawNext ∧
      NotionCorePartition.Represents rawNext
        (before ++ NotionCorePartition.insertCell cell (originAddress inst origin)
          ((NotionCoreOriginTree.preorderTree fresh).map (atom inst)) :: after) ∧
      rawNext.physical = augmented inst next ∧
      NotionCorePartition.scanCells rawNext.physical rawNext.endpoints =
        before ++ NotionCorePartition.insertCell cell (originAddress inst origin)
          ((NotionCoreOriginTree.preorderTree fresh).map (atom inst)) :: after := by
  have rawPresent : originAddress inst origin ∈ state.physical.map Atom.address := by
    rw [coupled]
    exact origin_present_physical inst origin old present
  obtain ⟨cell, ownership, _⟩ := NotionCorePartition.physical_unique_owner
    (originAddress inst origin) represented rawPresent
  obtain ⟨before, after, shape⟩ := List.append_of_mem ownership.1
  subst cells
  have rawApart : List.Disjoint (state.physical.map Atom.address)
      (((NotionCoreOriginTree.preorderTree fresh).map (atom inst)).map Atom.address) := by
    rw [coupled]
    exact physical_disjoint inst _ _ apart
  obtain ⟨rawNext, executed, representedNext⟩ := NotionCorePartition.insert_represents
    before after cell (originAddress inst origin)
      ((NotionCoreOriginTree.preorderTree fresh).map (atom inst)) represented chained ownership.2
        (fresh_addresses_unique inst _ newUnique) rawApart
  have located := NotionCorePartition.locate_of_member cell (originAddress inst origin)
    represented chained ownership.1 ownership.2
  have rawPhysical : rawNext.physical = NotionCorePartition.spliceAfterBy Atom.address
      (originAddress inst origin) ((NotionCoreOriginTree.preorderTree fresh).map (atom inst))
        state.physical := by
    have equation := executed
    simp only [NotionCorePartition.insert, located, Option.some.injEq] at equation
    rw [← equation]
  have treePhysical := tree_insert_physical inst origin fresh old ready present
  rw [accepted] at treePhysical
  simp only [Option.map_some, Option.some.injEq] at treePhysical
  refine ⟨before, cell, after, rawNext, rfl, executed, representedNext, ?_,
    NotionCorePartition.extraction_correct representedNext
      (NotionCorePartition.insert_chained before after cell _ _ chained)⟩
  rw [rawPhysical, coupled, treePhysical]

theorem fresh_address (inst : Nat) (id : Id) (items : List NotionCoreOriginTree.Item)
    (absent : id ∉ items.map NotionCoreOriginTree.Item.id) :
    address inst id ∉ (physical inst items).map Atom.address := by
  intro member
  simp only [physical, List.map_cons, start_address, List.map_map, Function.comp_def,
    atom_address, List.mem_cons] at member
  rcases member with isStart | member
  · exact address_ne_start inst id isStart
  · obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
    exact absent (List.mem_map.mpr ⟨old, oldMember, address_injective inst same⟩)

def markerTree (id : Id) : NotionCoreOriginTree.Tree :=
  .node ⟨id, .split⟩ .nil

/-- The RGA part of a block split inserts one marker. Its actual tree
traversal is coupled to raw endpoint splitting, whose affected interval is
found by scanning and whose endpoint update/extraction is proved separately. -/
theorem tree_split_partition (inst : Nat) (origin : NotionCoreOriginTree.Origin)
    (marker : Id) (freshOwner : Nat) (old next : NotionCoreOriginTree.Forest)
    (state : NotionCorePartition.State) (cells : List NotionCorePartition.Cell)
    (coupled : state.physical = augmented inst old)
    (represented : NotionCorePartition.Represents state cells)
    (chained : NotionCorePartition.Chained cells)
    (ready : NotionCoreOriginTree.Ready origin (markerTree marker) old)
    (present : Present origin old)
    (freshMarker : marker ∉ (NotionCoreOriginTree.preorder old).map NotionCoreOriginTree.Item.id)
    (accepted : NotionCoreOriginTree.insert origin (markerTree marker) old = some next) :
    ∃ before cell after rawNext,
      cells = before ++ cell :: after ∧
      NotionCorePartition.locate state (originAddress inst origin) = some cell ∧
      NotionCorePartition.split state (originAddress inst origin) (address inst marker)
        freshOwner = some rawNext ∧
      NotionCorePartition.Represents rawNext
        (before ++ NotionCorePartition.splitCell cell (originAddress inst origin)
          (address inst marker) freshOwner ++ after) ∧
      rawNext.physical = augmented inst next ∧
      NotionCorePartition.scanCells rawNext.physical rawNext.endpoints =
        before ++ NotionCorePartition.splitCell cell (originAddress inst origin)
          (address inst marker) freshOwner ++ after := by
  have rawPresent : originAddress inst origin ∈ state.physical.map Atom.address := by
    rw [coupled]
    exact origin_present_physical inst origin old present
  have rawFresh : address inst marker ∉ state.physical.map Atom.address := by
    rw [coupled]
    exact fresh_address inst marker _ freshMarker
  obtain ⟨before, cell, after, rawNext, shape, located, executed, representedNext⟩ :=
    NotionCorePartition.split_refines (originAddress inst origin) (address inst marker)
      freshOwner represented chained rawPresent rawFresh
  have rawPhysical : rawNext.physical = NotionCorePartition.spliceAfterBy Atom.address
      (originAddress inst origin) [NotionCorePartition.boundary (address inst marker)]
        state.physical := by
    have equation := executed
    simp only [NotionCorePartition.split, located, Option.some.injEq] at equation
    rw [← equation]
  have treePhysical := tree_insert_physical inst origin (markerTree marker) old ready present
  rw [accepted] at treePhysical
  simp only [Option.map_some, Option.some.injEq, markerTree,
    NotionCoreOriginTree.preorderTree, NotionCoreOriginTree.preorder,
    List.map_cons, List.map_nil] at treePhysical
  change augmented inst next = NotionCorePartition.spliceAfterBy Atom.address
    (originAddress inst origin) [NotionCorePartition.boundary (address inst marker)]
      (augmented inst old) at treePhysical
  subst cells
  refine ⟨before, cell, after, rawNext, rfl, located, executed, representedNext, ?_,
    NotionCorePartition.extraction_correct representedNext
      (NotionCorePartition.split_chained before after cell _ _ freshOwner chained)⟩
  rw [rawPhysical, coupled, treePhysical]

/-- Match source `#splitText`'s actual order: insert the marker into the RGA,
then locate its containing interval using the old endpoint table. Its owner is
derived from scanning the actual inserted tree traversal. -/
theorem tree_marker_routes (inst : Nat) (origin : NotionCoreOriginTree.Origin)
    (marker : Id) (old next : NotionCoreOriginTree.Forest)
    (state : NotionCorePartition.State) (cells : List NotionCorePartition.Cell)
    (coupled : state.physical = augmented inst old)
    (represented : NotionCorePartition.Represents state cells)
    (chained : NotionCorePartition.Chained cells)
    (ready : NotionCoreOriginTree.Ready origin (markerTree marker) old)
    (present : Present origin old)
    (freshMarker : marker ∉ (NotionCoreOriginTree.preorder old).map NotionCoreOriginTree.Item.id)
    (accepted : NotionCoreOriginTree.insert origin (markerTree marker) old = some next) :
    ∃ cell, NotionCorePartition.locate state (originAddress inst origin) = some cell ∧
      NotionCorePartition.locate {state with physical := augmented inst next}
        (address inst marker) = some (NotionCorePartition.insertCell cell
          (originAddress inst origin) [NotionCorePartition.boundary (address inst marker)]) ∧
      (NotionCorePartition.locate {state with physical := augmented inst next}
        (address inst marker)).map NotionCorePartition.Cell.owner = some cell.owner := by
  have rawPresent : originAddress inst origin ∈ state.physical.map Atom.address := by
    rw [coupled]
    exact origin_present_physical inst origin old present
  have rawFresh : address inst marker ∉ state.physical.map Atom.address := by
    rw [coupled]
    exact fresh_address inst marker _ freshMarker
  have physicalEq := tree_insert_physical inst origin (markerTree marker) old ready present
  rw [accepted] at physicalEq
  simp only [Option.map_some, Option.some.injEq, markerTree,
    NotionCoreOriginTree.preorderTree, NotionCoreOriginTree.preorder,
    List.map_cons, List.map_nil] at physicalEq
  change augmented inst next = NotionCorePartition.spliceAfterBy Atom.address
    (originAddress inst origin) [NotionCorePartition.boundary (address inst marker)]
      (augmented inst old) at physicalEq
  have routed := NotionCorePartition.marker_routing_after_insert
    (originAddress inst origin) (address inst marker) represented chained rawPresent rawFresh
  rw [coupled, ← physicalEq] at routed
  exact routed

/-- The raw endpoint state and the actual empty source instance agree at
initialization, including the virtual START boundary. -/
theorem initial_coupled (owner inst : Nat) :
    (NotionCorePartition.initial owner inst).physical = augmented inst .nil := rfl

/-- PASS+FAIL: distinct source sessions retain distinct semantic identities,
even at the same counter. Event identities cannot alias virtual START. -/
theorem encoding_control :
    address 7 (⟨1, [65]⟩ : Id) = (7, .event (Encodable.encode ([65] : List Nat), 1)) ∧
    address 7 (⟨1, [65]⟩ : Id) ≠ address 7 ⟨1, [66]⟩ ∧
    address 7 (⟨1, [65]⟩ : Id) ≠ (7, .start) := by
  refine ⟨rfl, ?_, address_ne_start _ _⟩
  intro same
  exact (by decide : (⟨1, [65]⟩ : Id) ≠ ⟨1, [66]⟩) (address_injective 7 same)

/-- PASS+FAIL: inserting a single character at START produces that character
behind the virtual boundary; it does not leave only the empty sentinel. -/
theorem physical_start_control :
    let item := NotionCoreOriginTree.literal 1 97
    let result := (NotionCoreOriginTree.insert .start
      (NotionCoreOriginTree.runTree item []) .nil).map (augmented 7)
    result = some [start 7, atom 7 item] ∧ result ≠ some [start 7] := by
  simp [NotionCoreOriginTree.insert, NotionCoreOriginTree.insertChild,
    NotionCoreOriginTree.runTree, augmented, physical, NotionCoreOriginTree.preorder,
    NotionCoreOriginTree.preorderTree]

#print axioms tree_insert_physical
#print axioms tree_insert_partition
#print axioms tree_split_partition
#print axioms tree_marker_routes
end Sal.MRDTs.Instances.NotionCorePhysicalReplay
