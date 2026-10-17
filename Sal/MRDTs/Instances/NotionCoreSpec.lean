import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup

/-! Independent retained-identity sequential block editing. There are no
transactions, clocks, replay keys, slice trees, search labels, or source calls.
-/
namespace Sal.MRDTs.Instances.NotionCoreSpec

inductive LocalId where
  | start
  | event (id : Nat × Nat)
  deriving DecidableEq, Repr

abbrev Address := Nat × LocalId

structure Slot where
  address : Address
  value : Nat
  visible : Bool
  deriving DecidableEq, Repr

/-- A block of the document. `inst` is the text instance the block was
created with; its root slot is `root inst`. A tombstone (`alive = false`) is a
block that has been merged into another; it keeps its place in the document
order and its instance, holds no slots, and is absent from the view. -/
structure Block where
  id : Nat
  inst : Nat
  slots : List Slot
  alive : Bool := true
  deriving DecidableEq, Repr

abbrev Document := List Block

def root (inst : Nat) : Slot := ⟨(inst, .start), 0, false⟩
def boundary (inst : Nat) (id : Nat × Nat) : Slot := ⟨(inst, .event id), 0, false⟩
def character (inst : Nat) (id : Nat × Nat) (value : Nat) : Slot := ⟨(inst, .event id), value, true⟩

def text (slots : List Slot) : List Nat :=
  (slots.filter Slot.visible).map Slot.value

/-- The displayed document: the alive blocks in document order with their
visible text. Tombstones are filtered out. -/
def view (doc : Document) : List (Nat × List Nat) :=
  (doc.filter Block.alive).map fun b => (b.id, text b.slots)

@[simp] theorem text_nil : text [] = [] := rfl
@[simp] theorem text_append (a b : List Slot) : text (a ++ b) = text a ++ text b := by
  simp [text]
@[simp] theorem text_cons (slot : Slot) (rest : List Slot) :
    text (slot :: rest) = if slot.visible then slot.value :: text rest else text rest := by
  cases h : slot.visible <;> simp [text, h]

/-- Count retained slots through the nth visible character. Zero denotes the
beginning; oversized requests clamp. The client uses a separate bounds check. -/
def gapIndex : List Slot → Nat → Nat
  | _, 0 => 0
  | [], _ + 1 => 0
  | slot :: rest, n + 1 =>
      gapIndex rest (if slot.visible then n else n + 1) + 1

theorem gapIndex_le (slots : List Slot) (n : Nat) : gapIndex slots n ≤ slots.length := by
  induction slots generalizing n with
  | nil => cases n <;> simp [gapIndex]
  | cons slot rest ih =>
      cases n with
      | zero => simp [gapIndex]
      | succ n => simpa [gapIndex, Nat.add_comm] using Nat.succ_le_succ (ih _)

theorem text_take_gapIndex (slots : List Slot) (n : Nat) :
    text (slots.take (gapIndex slots n)) = (text slots).take n := by
  induction slots generalizing n with
  | nil => cases n <;> simp [gapIndex]
  | cons slot rest ih =>
      cases n with
      | zero => simp [gapIndex]
      | succ n =>
          cases h : slot.visible <;>
            simp [gapIndex, h, ih]

theorem text_drop_gapIndex (slots : List Slot) (n : Nat) :
    text (slots.drop (gapIndex slots n)) = (text slots).drop n := by
  induction slots generalizing n with
  | nil => cases n <;> simp [gapIndex]
  | cons slot rest ih =>
      cases n with
      | zero => simp [gapIndex]
      | succ n =>
          cases h : slot.visible <;>
            simp [gapIndex, h, ih]

/-- A block is headed by a retained invisible semantic anchor. Global address
uniqueness prevents ambiguous origins and duplicate prepared character IDs. -/
def Anchored (block : Block) : Prop :=
  ∃ head tail, block.slots = head :: tail ∧ head.visible = false

/-- Block names and slot addresses are unique over all blocks, tombstones
included, and every alive block is anchored. A tombstone holds no slots, so it
has no head anchor; the invariant does not constrain tombstones beyond
uniqueness. -/
def WellFormed (doc : Document) : Prop :=
  (doc.map Block.id).Nodup ∧
  (doc.flatMap (fun b => b.slots.map Slot.address)).Nodup ∧
  ∀ block ∈ doc, block.alive = true → Anchored block

/-- Every alive block is headed by its own root slot `root inst`, and every
tombstone holds no slots. On a document with unique slot addresses this makes
an alive block the holder of its own root, and makes every holder alive. -/
def Rooted (doc : Document) : Prop :=
  ∀ block ∈ doc, (block.alive = true → ∃ tail, block.slots = root block.inst :: tail) ∧
    (block.alive = false → block.slots = [])

/-- Preparation only reads the current block and a visible index. The selected
anchor is the retained head at zero or the requested predecessor character. -/
def prepareGap (slots : List Slot) (index : Nat) : Option Address :=
  match slots with
  | [] => none
  | head :: tail => (head :: tail)[gapIndex tail index]?.map Slot.address

/-- A local positional split's independent abstract effect. The retained
prefix includes the head anchor; display moves exactly the requested suffix. -/
def localSplit (head : Slot) (tail : List Slot) (index : Nat) : List Slot × List Slot :=
  ((head :: tail).take (gapIndex tail index + 1),
   (head :: tail).drop (gapIndex tail index + 1))

theorem localSplit_visible (head : Slot) (tail : List Slot) (index : Nat)
    (invisible : head.visible = false) :
    text (localSplit head tail index).1 = (text (head :: tail)).take index ∧
    text (localSplit head tail index).2 = (text (head :: tail)).drop index := by
  simp [localSplit, invisible, text_take_gapIndex, text_drop_gapIndex]

/-- Cut immediately after a stable semantic address. Missing addresses clamp
at the end; legal commands establish ownership before invoking this helper. -/
def cutAfter (slots : List Slot) (origin : Address) : List Slot × List Slot :=
  let index := (slots.map Slot.address).idxOf origin + 1
  (slots.take index, slots.drop index)

def preparedAnchor (head : Slot) (tail : List Slot) (index : Nat) : Address :=
  ((head :: tail).get ⟨gapIndex tail index, by
    simpa using Nat.lt_succ_of_le (gapIndex_le tail index)⟩).address

theorem cutAfter_prepared (head : Slot) (tail : List Slot) (index : Nat)
    (unique : ((head :: tail).map Slot.address).Nodup) :
    cutAfter (head :: tail) (preparedAnchor head tail index) = localSplit head tail index := by
  have bound : gapIndex tail index < (head :: tail).length :=
    by simpa using Nat.lt_succ_of_le (gapIndex_le tail index)
  have found : ((head :: tail).map Slot.address).idxOf
      ((head :: tail)[gapIndex tail index].address) = gapIndex tail index := by
    rw [← List.getElem_map Slot.address]
    exact List.Nodup.idxOf_getElem unique
      (gapIndex tail index) (by simpa only [List.length_map] using bound)
  change ((head :: tail).take (((head :: tail).map Slot.address).idxOf
      ((head :: tail)[gapIndex tail index].address) + 1),
    (head :: tail).drop (((head :: tail).map Slot.address).idxOf
      ((head :: tail)[gapIndex tail index].address) + 1)) = _
  rw [found]
  rfl

def insertSlots (origin : Address) (fresh : List Slot) (slots : List Slot) : List Slot :=
  let (pre, post) := cutAfter slots origin
  pre ++ fresh ++ post

theorem prepared_insert_visible (head : Slot) (tail fresh : List Slot) (index : Nat)
    (invisible : head.visible = false)
    (unique : ((head :: tail).map Slot.address).Nodup) :
    text (insertSlots (preparedAnchor head tail index) fresh (head :: tail)) =
      (text (head :: tail)).take index ++ text fresh ++
      (text (head :: tail)).drop index := by
  simp only [insertSlots, cutAfter_prepared _ _ _ unique]
  rw [text_append, text_append]
  exact congrArg₂ (· ++ ·)
    (congrArg (· ++ text fresh) (localSplit_visible head tail index invisible).1)
    (localSplit_visible head tail index invisible).2

theorem prepared_split_visible (head : Slot) (tail : List Slot) (index : Nat)
    (invisible : head.visible = false)
    (unique : ((head :: tail).map Slot.address).Nodup) :
    text (cutAfter (head :: tail) (preparedAnchor head tail index)).1 =
        (text (head :: tail)).take index ∧
    text (cutAfter (head :: tail) (preparedAnchor head tail index)).2 =
        (text (head :: tail)).drop index := by
  rw [cutAfter_prepared _ _ _ unique]
  exact localSplit_visible head tail index invisible

/-- A structural preparation witness: the address occurs at a retained index
whose prefix contains exactly the requested number of visible characters.
Invisible root/marker choices at the same visible gap are both admissible. -/
def PreparedGap (slots : List Slot) (origin : Address) (index : Nat) : Prop :=
  ∃ k, ∃ bound : k < slots.length,
    slots[k].address = origin ∧ (text (slots.take (k + 1))).length = index

theorem preparedGap_visible (slots : List Slot) (origin : Address) (index : Nat)
    (unique : (slots.map Slot.address).Nodup)
    (prepared : PreparedGap slots origin index) :
    text (cutAfter slots origin).1 = (text slots).take index ∧
    text (cutAfter slots origin).2 = (text slots).drop index := by
  obtain ⟨k, bound, rfl, count⟩ := prepared
  have found : (slots.map Slot.address).idxOf (slots[k].address) = k := by
    rw [← List.getElem_map Slot.address]
    exact List.Nodup.idxOf_getElem unique k (by simpa using bound)
  simp only [cutAfter, found]
  have parts : text slots = text (slots.take (k + 1)) ++ text (slots.drop (k + 1)) := by
    rw [← text_append, List.take_append_drop]
  rw [parts, ← count]
  simp

def owns (block : Block) (origin : Address) : Bool :=
  decide (origin ∈ block.slots.map Slot.address)

/-- The first semantic owner is unambiguous on `WellFormed` documents. -/
def owner (doc : Document) (origin : Address) : Option Block :=
  doc.find? (fun block => owns block origin)

def eraseSlot (targets : List Address) (slot : Slot) : Slot :=
  {slot with visible := slot.visible && !(targets.contains slot.address)}

def eraseSlots (targets : List Address) (slots : List Slot) : List Slot :=
  slots.map (eraseSlot targets)

theorem eraseSlots_unchanged (targets : List Address) (slots : List Slot)
    (outside : ∀ slot ∈ slots, slot.address ∉ targets) : eraseSlots targets slots = slots := by
  induction slots with
  | nil => rfl
  | cons slot rest ih =>
      have absent := outside slot (by simp)
      have equal : eraseSlot targets slot = slot := by
        cases slot
        simp_all [eraseSlot]
      simp only [eraseSlots, List.map_cons, equal]
      exact congrArg (slot :: ·) (ih (fun x hx => outside x (by simp [hx])))

theorem eraseSlots_empty_text (targets : List Address) (slots : List Slot)
    (covered : ∀ slot ∈ slots, slot.visible = true → slot.address ∈ targets) :
    text (eraseSlots targets slots) = [] := by
  induction slots with
  | nil => rfl
  | cons slot rest ih =>
      have tail := ih (fun x hx => covered x (by simp [hx]))
      have hidden : (eraseSlot targets slot).visible = false := by
        cases live : slot.visible with
        | false => simp [eraseSlot, live]
        | true => simp [eraseSlot, live, covered slot (by simp) live]
      simpa only [eraseSlots, List.map_cons, text_cons, hidden, Bool.false_eq_true,
        ↓reduceIte] using tail

/-- Select exactly the currently visible characters in a retained interval. -/
def targetsIn (slots : List Slot) : List Address :=
  (slots.filter Slot.visible).map Slot.address

theorem erase_interval_visible (pre middle post : List Slot)
    (unique : (((pre ++ middle) ++ post).map Slot.address).Nodup) :
    text (eraseSlots (targetsIn middle) ((pre ++ middle) ++ post)) = text pre ++ text post := by
  have outer := List.nodup_append'.mp (show
      ((pre.map Slot.address ++ middle.map Slot.address) ++ post.map Slot.address).Nodup
      from by simpa only [List.map_append] using unique)
  have inner := List.nodup_append'.mp outer.1
  have target_sub : ∀ address ∈ targetsIn middle, address ∈ middle.map Slot.address := by
    intro address member
    obtain ⟨slot, selected, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨slot, (List.mem_filter.mp selected).1, rfl⟩
  have pre_out : ∀ slot ∈ pre, slot.address ∉ targetsIn middle := by
    intro slot member selected
    exact List.disjoint_left.mp inner.2.2
      (List.mem_map.mpr ⟨slot, member, rfl⟩) (target_sub _ selected)
  have post_out : ∀ slot ∈ post, slot.address ∉ targetsIn middle := by
    intro slot member selected
    exact List.disjoint_left.mp outer.2.2
      (List.mem_append_right _ (target_sub _ selected))
      (List.mem_map.mpr ⟨slot, member, rfl⟩)
  have covered : ∀ slot ∈ middle, slot.visible = true → slot.address ∈ targetsIn middle := by
    intro slot member live
    exact List.mem_map.mpr ⟨slot, List.mem_filter.mpr ⟨member, live⟩, rfl⟩
  simp only [eraseSlots, List.map_append, text_append]
  rw [show pre.map (eraseSlot (targetsIn middle)) = pre from
    eraseSlots_unchanged _ _ pre_out,
    show post.map (eraseSlot (targetsIn middle)) = post from
    eraseSlots_unchanged _ _ post_out,
    show text (middle.map (eraseSlot (targetsIn middle))) = [] from
    eraseSlots_empty_text _ _ covered]
  simp

def prepareDelete (slots : List Slot) (start count : Nat) : List Address :=
  let rest := slots.drop (gapIndex slots start)
  targetsIn (rest.take (gapIndex rest count))

/-- Exact local range deletion, derived from address uniqueness, visible gap
scanning, and selection of visible identities. Bounds are clamped by lists. -/
theorem prepared_delete_visible (slots : List Slot) (start count : Nat)
    (unique : (slots.map Slot.address).Nodup) :
    text (eraseSlots (prepareDelete slots start count) slots) =
      (text slots).take start ++ (text slots).drop (start + count) := by
  let pre := slots.take (gapIndex slots start)
  let rest := slots.drop (gapIndex slots start)
  let middle := rest.take (gapIndex rest count)
  let post := rest.drop (gapIndex rest count)
  have split : (pre ++ middle) ++ post = slots := by
    dsimp [pre, middle, post]
    rw [List.append_assoc, List.take_append_drop]
    exact List.take_append_drop _ slots
  have checked := erase_interval_visible pre middle post (by simpa only [split] using unique)
  rw [split] at checked
  change text (eraseSlots (targetsIn middle) slots) = _
  rw [checked]
  dsimp [pre, post, rest]
  rw [text_take_gapIndex, text_drop_gapIndex, text_drop_gapIndex, List.drop_drop]

inductive Command where
  | create (id inst : Nat) (after : Option Nat)
  | insert (origin : Address) (fresh : List Slot)
  | delete (targets : List Address)
  | split (origin : Address) (marker : Slot) (target : Nat)
  | merge (source target : Nat)
  deriving DecidableEq, Repr

def findBlock (doc : Document) (bid : Nat) : Option Block :=
  doc.find? (fun block => decide (block.id = bid))

/-- Independent command execution. A split appends its hidden marker and
suffix to an already created fresh target block; creation separately places
that block after the request's original block, alive or a tombstone.

A merge looks up the target's holder: the block whose slots contain the
target's root slot. Root slots move with merges and tombstones hold no slots,
so on rooted documents the holder is the target itself when it is alive, and
otherwise the alive block that absorbed it. If the source is alive and the
holder exists and is not the source, the holder's slots become its old slots
followed by the source's, including the source's hidden root, and the source
becomes a tombstone in place: no slots, `alive = false`. Any other merge,
including one whose holder is the source itself, leaves the document
unchanged. The target's liveness is not checked. -/
def step (doc : Document) (command : Command) : Option Document :=
  match command with
  | .create id inst after =>
      if id ∈ doc.map Block.id then none
      else let fresh : Block := ⟨id, inst, [root inst], true⟩
        match after with
        | none => some (fresh :: doc)
        | some previous =>
            if previous ∈ doc.map Block.id then
              some (doc.flatMap fun block => if block.id = previous then [block, fresh] else [block])
            else none
  | .insert origin fresh =>
      match owner doc origin with
      | none => none
      | some _ => some (doc.map fun block =>
          if owns block origin then {block with slots := insertSlots origin fresh block.slots} else block)
  | .delete targets => some (doc.map fun block =>
      {block with slots := block.slots.map (eraseSlot targets)})
  | .split origin marker target =>
      match owner doc origin with
      | none => none
      | some source =>
          if source.id = target ∨ target ∉ doc.map Block.id ∨ marker.visible = true then none
          else let (pre, post) := cutAfter source.slots origin
            some (doc.map fun block =>
              if block.id = source.id then {block with slots := pre}
              else if block.id = target then {block with slots := block.slots ++ marker :: post}
              else block)
  | .merge source target =>
      match findBlock doc source, findBlock doc target with
      | some src, some tgt =>
          match owner doc (root tgt.inst).address with
          | some holder =>
              if src.alive = true ∧ holder.id ≠ source then
                some (doc.map fun block =>
                  if block.id = holder.id then {block with slots := block.slots ++ src.slots}
                  else if block.id = source then {block with slots := [], alive := false}
                  else block)
              else some doc
          | none => some doc
      | _, _ => some doc

def execute (doc : Document) : List Command → Option Document
  | [] => some doc
  | command :: rest => (step doc command).bind fun next => execute next rest

/-- Structural separation of an origin from the other blocks. -/
def Avoids (doc : Document) (origin : Address) : Prop :=
  ∀ block ∈ doc, origin ∉ block.slots.map Slot.address

theorem address_focus (pre post : Document) (source : Block) (origin : Address)
    (unique : ((pre ++ source :: post).flatMap
      (fun b => b.slots.map Slot.address)).Nodup)
    (present : origin ∈ source.slots.map Slot.address) :
    (source.slots.map Slot.address).Nodup ∧ Avoids (pre ++ post) origin := by
  have nd : (((pre.flatMap (fun b => b.slots.map Slot.address)) ++
      source.slots.map Slot.address) ++ post.flatMap (fun b => b.slots.map Slot.address)).Nodup := by
    simpa only [List.flatMap_append, List.flatMap_cons, List.append_assoc] using unique
  have outer := List.nodup_append'.mp nd
  have inner := List.nodup_append'.mp outer.1
  refine ⟨inner.2.1, ?_⟩
  intro block member collision
  rcases List.mem_append.mp member with member | member
  · exact List.disjoint_left.mp inner.2.2
      (List.mem_flatMap.mpr ⟨block, member, collision⟩) present
  · exact List.disjoint_left.mp outer.2.2
      (List.mem_append_right _ present)
      (List.mem_flatMap.mpr ⟨block, member, collision⟩)

theorem owner_focus (pre post : Document) (source : Block) (origin : Address)
    (present : origin ∈ source.slots.map Slot.address)
    (outside : Avoids pre origin) :
    owner (pre ++ source :: post) origin = some source := by
  apply List.find?_eq_some_iff_append.mpr
  refine ⟨by simp [owns, present], pre, post, rfl, ?_⟩
  intro block member
  simp [owns, outside block member]

private theorem map_identity {α : Type} (f : α → α) (xs : List α)
    (unchanged : ∀ x ∈ xs, f x = x) : xs.map f = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.map_cons, unchanged x (by simp), ih (fun y hy => unchanged y (by simp [hy]))]

theorem step_insert_focus (pre post : Document) (source : Block) (origin : Address)
    (fresh : List Slot) (present : origin ∈ source.slots.map Slot.address)
    (outside : Avoids (pre ++ post) origin) :
    step (pre ++ source :: post) (.insert origin fresh) =
      some (pre ++ {source with slots := insertSlots origin fresh source.slots} :: post) := by
  have own := owner_focus pre post source origin present
    (fun b hb => outside b (List.mem_append_left _ hb))
  simp only [step, own]
  congr 1
  simp only [List.map_append, List.map_cons]
  have unchanged : ∀ b ∈ pre ++ post,
      (if owns b origin then {b with slots := insertSlots origin fresh b.slots} else b) = b := by
    intro b hb
    simp [owns, outside b hb]
  rw [map_identity _ pre (fun b hb => unchanged b (List.mem_append_left _ hb)),
    map_identity _ post (fun b hb => unchanged b (List.mem_append_right _ hb))]
  simp [owns, present]

/-- Full-document local insert correctness. The structural hypotheses say the
head is hidden and every semantic address occurs once; they do not assert the
visible editing effect. Preparation may insert any supplied character run. -/
theorem local_insert_document (pre post : Document) {blockInst : Nat} (bid : Nat)
    (head : Slot) (tail fresh : List Slot) (index : Nat)
    (invisible : head.visible = false)
    (unique : ((pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post).flatMap
      (fun b => b.slots.map Slot.address)).Nodup) :
    ∃ result, step (pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post)
        (.insert (preparedAnchor head tail index) fresh) = some result ∧
      view result = view pre ++ [(bid,
        (text (head :: tail)).take index ++ text fresh ++
        (text (head :: tail)).drop index)] ++ view post := by
  have bound : gapIndex tail index < (head :: tail).length := by
    simpa using Nat.lt_succ_of_le (gapIndex_le tail index)
  have present : preparedAnchor head tail index ∈ (head :: tail).map Slot.address := by
    exact List.mem_map.mpr ⟨_, List.getElem_mem bound, rfl⟩
  have structural := address_focus pre post ⟨bid, blockInst, head :: tail, true⟩ _ unique present
  refine ⟨_, step_insert_focus pre post ⟨bid, blockInst, head :: tail, true⟩ _ fresh present structural.2, ?_⟩
  simp only [view, List.filter_append, List.filter_cons, List.map_append, List.map_cons,
    ↓reduceIte]
  rw [prepared_insert_visible head tail fresh index invisible structural.1]
  simp [List.append_assoc]

theorem prepareDelete_subset (slots : List Slot) (start count : Nat) :
    ∀ address ∈ prepareDelete slots start count, address ∈ slots.map Slot.address := by
  intro address member
  obtain ⟨slot, selected, rfl⟩ := List.mem_map.mp member
  have selected := (List.mem_filter.mp selected).1
  exact List.mem_map.mpr ⟨slot, List.mem_of_mem_drop (List.mem_of_mem_take selected), rfl⟩

/-- Full-document local delete correctness. Address uniqueness proves that
selected identities cannot erase characters belonging to another block. -/
theorem local_delete_document (pre post : Document) {blockInst : Nat} (bid : Nat)
    (head : Slot) (tail : List Slot) (start count : Nat)
    (unique : ((pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post).flatMap
      (fun b => b.slots.map Slot.address)).Nodup) :
    ∃ result, step (pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post)
        (.delete (prepareDelete (head :: tail) start count)) = some result ∧
      view result = view pre ++ [(bid,
        (text (head :: tail)).take start ++
        (text (head :: tail)).drop (start + count))] ++ view post := by
  let targets := prepareDelete (head :: tail) start count
  have source_unique := (address_focus pre post ⟨bid, blockInst, head :: tail, true⟩ head.address unique
    (by simp)).1
  have unchanged : ∀ b ∈ pre ++ post,
      ({b with slots := b.slots.map (eraseSlot targets)} : Block) = b := by
    intro b hb
    have outside : ∀ slot ∈ b.slots, slot.address ∉ targets := by
      intro slot member selected
      have separated := (address_focus pre post ⟨bid, blockInst, head :: tail, true⟩ slot.address unique
        (prepareDelete_subset _ start count _ selected)).2
      exact separated b hb (List.mem_map.mpr ⟨slot, member, rfl⟩)
    rw [show b.slots.map (eraseSlot targets) = b.slots from
      eraseSlots_unchanged targets b.slots outside]
  refine ⟨pre ++ {id := bid, inst := blockInst, slots := eraseSlots targets (head :: tail)} :: post, ?_, ?_⟩
  · simp only [step, List.map_append, List.map_cons]
    congr 1
    rw [map_identity _ pre (fun b hb => unchanged b (List.mem_append_left _ hb)),
      map_identity _ post (fun b hb => unchanged b (List.mem_append_right _ hb))]
    rfl
  · simp only [view, List.filter_append, List.filter_cons, List.map_append, List.map_cons,
    ↓reduceIte]
    rw [prepared_delete_visible _ start count source_unique]
    simp [List.append_assoc]

theorem preparedGap_present {slots : List Slot} {origin : Address} {index : Nat}
    (prepared : PreparedGap slots origin index) : origin ∈ slots.map Slot.address := by
  obtain ⟨k, bound, rfl, _⟩ := prepared
  exact List.mem_map.mpr ⟨_, List.getElem_mem bound, rfl⟩

private theorem two_block_ids (pre post : Document) (source target : Block)
    (unique : ((pre ++ source :: target :: post).map Block.id).Nodup) :
    source.id ≠ target.id ∧
    ∀ b ∈ pre ++ post, b.id ≠ source.id ∧ b.id ≠ target.id := by
  have shape : (pre.map Block.id ++ source.id :: target.id :: post.map Block.id).Nodup := by
    simpa only [List.map_append, List.map_cons] using unique
  have outer := List.nodup_append'.mp shape
  have sourceAbsent := (List.nodup_cons.mp outer.2.1).1
  have targetAbsent := (List.nodup_cons.mp (List.nodup_cons.mp outer.2.1).2).1
  refine ⟨fun eq => sourceAbsent (by simp [eq]), ?_⟩
  intro b member
  rcases List.mem_append.mp member with member | member
  · have left : b.id ∈ pre.map Block.id := List.mem_map.mpr ⟨b, member, rfl⟩
    refine ⟨fun eq => List.disjoint_left.mp outer.2.2 left (by simp [eq]),
      fun eq => List.disjoint_left.mp outer.2.2 left (by simp [eq])⟩
  · have right : b.id ∈ post.map Block.id := List.mem_map.mpr ⟨b, member, rfl⟩
    exact ⟨fun eq => sourceAbsent (by simp [← eq, right]),
      fun eq => targetAbsent (eq ▸ right)⟩

/-- The split command has the requested visible effect on a prepared local
gap and a newly created, empty successor block. Other blocks are unchanged.
The premises are address/block uniqueness, anchor position, empty target, and
that both blocks are alive; none assumes the split's visible result. -/
theorem local_split_document (pre post : Document) (source target : Block)
    (origin : Address) (index : Nat) (marker : Slot)
    (addresses : ((pre ++ source :: target :: post).flatMap
      (fun b => b.slots.map Slot.address)).Nodup)
    (blocks : ((pre ++ source :: target :: post).map Block.id).Nodup)
    (prepared : PreparedGap source.slots origin index)
    (emptyTarget : text target.slots = []) (hidden : marker.visible = false)
    (sourceLive : source.alive = true) (targetLive : target.alive = true) :
    ∃ result, step (pre ++ source :: target :: post)
        (.split origin marker target.id) = some result ∧
      view result = view pre ++ [(source.id, (text source.slots).take index),
        (target.id, (text source.slots).drop index)] ++ view post := by
  have present := preparedGap_present prepared
  have structural := address_focus pre (target :: post) source origin addresses present
  have own := owner_focus pre (target :: post) source origin present
    (fun b hb => structural.2 b (List.mem_append_left _ hb))
  have ids := two_block_ids pre post source target blocks
  have targetPresent : target.id ∈ (pre ++ source :: target :: post).map Block.id := by
    simp
  have valid : ¬ (source.id = target.id ∨
      target.id ∉ (pre ++ source :: target :: post).map Block.id ∨ marker.visible = true) := by
    simp [ids.1, hidden]
  let cut := cutAfter source.slots origin
  let result := pre ++ {source with slots := cut.1} ::
    {target with slots := target.slots ++ marker :: cut.2} :: post
  refine ⟨result, ?_, ?_⟩
  · simp only [step, own, valid, ↓reduceIte]
    congr 1
    have unchanged : ∀ b ∈ pre ++ post,
        (if b.id = source.id then {b with slots := cut.1}
         else if b.id = target.id then {b with slots := b.slots ++ marker :: cut.2}
         else b) = b := by
      intro b hb
      simp [(ids.2 b hb).1, (ids.2 b hb).2]
    simp only [List.map_append, List.map_cons]
    rw [map_identity _ pre (fun b hb => unchanged b (List.mem_append_left _ hb)),
      map_identity _ post (fun b hb => unchanged b (List.mem_append_right _ hb))]
    simp [result, cut, ids.1.symm]
  · have visible := preparedGap_visible source.slots origin index structural.1 prepared
    simp only [result, view, List.filter_append, List.filter_cons, sourceLive, targetLive,
      List.map_append, List.map_cons, text_append, text_cons, emptyTarget, hidden, Bool.false_eq_true, ↓reduceIte, List.nil_append]
    rw [visible.1, visible.2]
    simp [List.append_assoc]

theorem preparedAnchor_structural (head : Slot) (tail : List Slot) (index : Nat)
    (invisible : head.visible = false) (bound : index ≤ (text (head :: tail)).length) :
    PreparedGap (head :: tail) (preparedAnchor head tail index) index := by
  refine ⟨gapIndex tail index, by simpa using Nat.lt_succ_of_le (gapIndex_le tail index), rfl, ?_⟩
  have effect := (localSplit_visible head tail index invisible).1
  change text ((head :: tail).take (gapIndex tail index + 1)) = _ at effect
  rw [effect, List.length_take, Nat.min_eq_left bound]

private theorem block_id_focus (pre post : Document) (source : Block)
    (unique : ((pre ++ source :: post).map Block.id).Nodup) :
    ∀ b ∈ pre ++ post, b.id ≠ source.id := by
  have shape : (pre.map Block.id ++ source.id :: post.map Block.id).Nodup := by
    simpa only [List.map_append, List.map_cons] using unique
  have outer := List.nodup_append'.mp shape
  have absent := (List.nodup_cons.mp outer.2.1).1
  intro b member eq
  rcases List.mem_append.mp member with member | member
  · exact List.disjoint_left.mp outer.2.2 (List.mem_map.mpr ⟨b, member, rfl⟩) (by simp [eq])
  · exact absent (eq ▸ List.mem_map.mpr ⟨b, member, rfl⟩)

private theorem flatMap_singletons {α : Type} (f : α → List α) (xs : List α)
    (unchanged : ∀ x ∈ xs, f x = [x]) : xs.flatMap f = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons, unchanged x (by simp)]
      rw [ih (fun y hy => unchanged y (by simp [hy]))]
      rfl

theorem step_create_focus (pre post : Document) (source : Block) (bid inst : Nat)
    (blocks : ((pre ++ source :: post).map Block.id).Nodup)
    (fresh : bid ∉ (pre ++ source :: post).map Block.id) :
    step (pre ++ source :: post) (.create bid inst (some source.id)) =
      some (pre ++ source :: ⟨bid, inst, [root inst], true⟩ :: post) := by
  have present : source.id ∈ (pre ++ source :: post).map Block.id := by simp
  simp only [step, fresh, ↓reduceIte, present]
  congr 1
  simp only [List.flatMap_append, List.flatMap_cons, ↓reduceIte]
  have unchanged : ∀ b ∈ pre ++ post,
      (if b.id = source.id then [b, ⟨bid, inst, [root inst], true⟩] else [b]) = [b] := by
    intro b hb
    simp [block_id_focus pre post source blocks b hb]
  rw [flatMap_singletons _ pre (fun b hb => unchanged b (List.mem_append_left _ hb)),
    flatMap_singletons _ post (fun b hb => unchanged b (List.mem_append_right _ hb))]
  simp

private theorem nodup_insert_middle {α : Type} (pre post : List α) (fresh : α)
    (unique : (pre ++ post).Nodup) (absent : fresh ∉ pre ++ post) :
    (pre ++ fresh :: post).Nodup :=
  List.nodup_middle.mpr (List.nodup_cons.mpr ⟨absent, unique⟩)

/-- The complete independent local split client: create a successor and issue
an identity-addressed split from an alive block. Fresh block/root names and
uniqueness establish the preconditions of the command theorem, rather than
assuming its result. -/
theorem local_split_client (pre post : Document) (source : Block)
    (origin : Address) (index bid inst : Nat) (marker : Slot)
    (addresses : ((pre ++ source :: post).flatMap
      (fun b => b.slots.map Slot.address)).Nodup)
    (blocks : ((pre ++ source :: post).map Block.id).Nodup)
    (prepared : PreparedGap source.slots origin index)
    (freshBlock : bid ∉ (pre ++ source :: post).map Block.id)
    (freshRoot : (root inst).address ∉ (pre ++ source :: post).flatMap
      (fun b => b.slots.map Slot.address))
    (hidden : marker.visible = false) (live : source.alive = true) :
    ∃ result, execute (pre ++ source :: post)
        [.create bid inst (some source.id), .split origin marker bid] = some result ∧
      view result = view pre ++ [(source.id, (text source.slots).take index),
        (bid, (text source.slots).drop index)] ++ view post := by
  have created := step_create_focus pre post source bid inst blocks freshBlock
  have addresses' : ((pre ++ source :: ⟨bid, inst, [root inst], true⟩ :: post).flatMap
      (fun b => b.slots.map Slot.address)).Nodup := by
    have inserted := nodup_insert_middle
      (pre.flatMap (fun b => b.slots.map Slot.address) ++ source.slots.map Slot.address)
      (post.flatMap (fun b => b.slots.map Slot.address)) (root inst).address
      (by simpa only [List.flatMap_append, List.flatMap_cons, List.append_assoc] using addresses)
      (by simpa only [List.flatMap_append, List.flatMap_cons, List.append_assoc] using freshRoot)
    simpa only [List.flatMap_append, List.flatMap_cons, List.map_cons, List.map_nil,
      List.singleton_append, List.append_assoc] using inserted
  have blocks' : ((pre ++ source :: ⟨bid, inst, [root inst], true⟩ :: post).map Block.id).Nodup := by
    have inserted := nodup_insert_middle (pre.map Block.id ++ [source.id]) (post.map Block.id) bid
      (by simpa only [List.map_append, List.map_cons, List.append_assoc, List.singleton_append] using blocks)
      (by simpa only [List.map_append, List.map_cons, List.append_assoc, List.singleton_append] using freshBlock)
    simpa only [List.map_append, List.map_cons, List.append_assoc, List.singleton_append] using inserted
  obtain ⟨result, executed, visible⟩ := local_split_document pre post source
    ⟨bid, inst, [root inst], true⟩ origin index marker addresses' blocks' prepared (by simp [root]) hidden live rfl
  refine ⟨result, ?_, visible⟩
  simp only [execute, created, Option.bind_some, executed]

/-- Allocate a character run from independently fresh semantic names and the
requested character values. Names carry no traversal or transaction order. -/
def characterRun (inst : Nat) (entries : List ((Nat × Nat) × Nat)) : List Slot :=
  entries.map (fun entry => character inst entry.1 entry.2)

@[simp] theorem text_characterRun (inst : Nat) (entries : List ((Nat × Nat) × Nat)) :
    text (characterRun inst entries) = entries.map Prod.snd := by
  induction entries with
  | nil => rfl
  | cons entry entries ih => simpa [characterRun, character] using congrArg (entry.2 :: ·) ih

/-- The local insertion client prepares the requested visible character run;
its theorem states the values requested by the caller rather than a projection
of an arbitrary supplied implementation state. Fresh names are required for
subsequent structural-invariant preservation, but not this immediate effect. -/
theorem local_insert_client (pre post : Document) {blockInst : Nat} (bid inst : Nat)
    (head : Slot) (tail : List Slot) (entries : List ((Nat × Nat) × Nat)) (index : Nat)
    (invisible : head.visible = false)
    (unique : ((pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post).flatMap
      (fun b => b.slots.map Slot.address)).Nodup) :
    ∃ result, step (pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post)
        (.insert (preparedAnchor head tail index) (characterRun inst entries)) = some result ∧
      view result = view pre ++ [(bid,
        (text (head :: tail)).take index ++ entries.map Prod.snd ++
        (text (head :: tail)).drop index)] ++ view post := by
  simpa only [text_characterRun] using local_insert_document pre post bid head tail
    (characterRun inst entries) index invisible unique

theorem prepareGap_succeeds (head : Slot) (tail : List Slot) (index : Nat) :
    prepareGap (head :: tail) index = some (preparedAnchor head tail index) := by
  have bound : gapIndex tail index < (head :: tail).length := by
    simpa using Nat.lt_succ_of_le (gapIndex_le tail index)
  simp only [prepareGap, List.getElem?_eq_getElem bound, Option.map_some]
  rfl

def prepareInsert (doc : Document) (bid index inst : Nat)
    (entries : List ((Nat × Nat) × Nat)) : Option Command := do
  let block ← findBlock doc bid
  if index ≤ (text block.slots).length then
    let origin ← prepareGap block.slots index
    pure (.insert origin (characterRun inst entries))
  else none

def prepareDeleteRequest (doc : Document) (bid start stop : Nat) : Option Command := do
  let block ← findBlock doc bid
  if start ≤ stop ∧ stop ≤ (text block.slots).length then
    pure (.delete (prepareDelete block.slots start (stop - start)))
  else none

def prepareSplit (doc : Document) (bid index freshBlock freshInstance : Nat)
    (markerId : Nat × Nat) : Option (List Command) := do
  let block ← findBlock doc bid
  if index ≤ (text block.slots).length then
    let origin ← prepareGap block.slots index
    pure [.create freshBlock freshInstance (some bid),
      .split origin (boundary origin.1 markerId) freshBlock]
  else none

theorem findBlock_focus (pre post : Document) (source : Block)
    (blocks : ((pre ++ source :: post).map Block.id).Nodup) :
    findBlock (pre ++ source :: post) source.id = some source := by
  apply List.find?_eq_some_iff_append.mpr
  refine ⟨by simp, pre, post, rfl, ?_⟩
  intro block member
  simp [block_id_focus pre post source blocks block (List.mem_append_left _ member)]

theorem prepareInsert_success (pre post : Document) {blockInst : Nat} (bid inst index : Nat)
    (head : Slot) (tail : List Slot) (entries : List ((Nat × Nat) × Nat))
    (blocks : ((pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post).map Block.id).Nodup)
    (bound : index ≤ (text (head :: tail)).length) :
    prepareInsert (pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post) bid index inst entries =
      some (.insert (preparedAnchor head tail index) (characterRun inst entries)) := by
  simp [prepareInsert, findBlock_focus pre post ⟨bid, blockInst, head :: tail, true⟩ blocks, prepareGap_succeeds]
  simpa only [text_cons] using bound

theorem prepareDelete_success (pre post : Document) {blockInst : Nat} (bid start stop : Nat)
    (slots : List Slot)
    (blocks : ((pre ++ ⟨bid, blockInst, slots, true⟩ :: post).map Block.id).Nodup)
    (bound : start ≤ stop ∧ stop ≤ (text slots).length) :
    prepareDeleteRequest (pre ++ ⟨bid, blockInst, slots, true⟩ :: post) bid start stop =
      some (.delete (prepareDelete slots start (stop - start))) := by
  simp [prepareDeleteRequest, findBlock_focus pre post ⟨bid, blockInst, slots, true⟩ blocks, bound]

theorem prepareSplit_success (pre post : Document) {blockInst : Nat} (bid index freshBlock freshInstance : Nat)
    (head : Slot) (tail : List Slot) (markerId : Nat × Nat)
    (blocks : ((pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post).map Block.id).Nodup)
    (bound : index ≤ (text (head :: tail)).length) :
    prepareSplit (pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post) bid index freshBlock freshInstance markerId =
      some [.create freshBlock freshInstance (some bid),
        .split (preparedAnchor head tail index)
          (boundary (preparedAnchor head tail index).1 markerId) freshBlock] := by
  simp [prepareSplit, findBlock_focus pre post ⟨bid, blockInst, head :: tail, true⟩ blocks, prepareGap_succeeds]
  simpa only [text_cons] using bound
/-- Executable positional preparation followed by command execution inserts
exactly the requested values on the addressed block. -/
theorem prepared_insert_effect (pre post : Document) {blockInst : Nat} (bid inst index : Nat)
    (head : Slot) (tail : List Slot) (entries : List ((Nat × Nat) × Nat))
    (addresses : ((pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post).flatMap
      (fun b => b.slots.map Slot.address)).Nodup)
    (blocks : ((pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post).map Block.id).Nodup)
    (hidden : head.visible = false) (bound : index ≤ (text (head :: tail)).length) :
    ∃ command result,
      prepareInsert (pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post) bid index inst entries = some command ∧
      step (pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post) command = some result ∧
      view result = view pre ++ [(bid, (text (head :: tail)).take index ++
        entries.map Prod.snd ++ (text (head :: tail)).drop index)] ++ view post := by
  obtain ⟨result, executed, visible⟩ := local_insert_client pre post bid inst head tail entries index hidden addresses
  exact ⟨_, result, prepareInsert_success pre post bid inst index head tail entries blocks bound,
    executed, visible⟩

/-- Executable range preparation and execution delete exactly [start,stop),
with the start and stop expressed in the current visible block. -/
theorem prepared_delete_effect (pre post : Document) {blockInst : Nat} (bid start stop : Nat)
    (head : Slot) (tail : List Slot)
    (addresses : ((pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post).flatMap
      (fun b => b.slots.map Slot.address)).Nodup)
    (blocks : ((pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post).map Block.id).Nodup)
    (bound : start ≤ stop ∧ stop ≤ (text (head :: tail)).length) :
    ∃ command result,
      prepareDeleteRequest (pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post) bid start stop = some command ∧
      step (pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post) command = some result ∧
      view result = view pre ++ [(bid, (text (head :: tail)).take start ++
        (text (head :: tail)).drop stop)] ++ view post := by
  obtain ⟨result, executed, visible⟩ := local_delete_document pre post bid head tail start (stop - start) addresses
  refine ⟨_, result, prepareDelete_success pre post bid start stop (head :: tail) blocks bound,
    executed, ?_⟩
  have count : start + (stop - start) = stop := by omega
  simpa only [count] using visible

/-- Executable positional split preparation and its atomic command sequence
have the ordinary local split effect. Fresh block and root names establish
the intermediate structural uniqueness needed by the split command. -/
theorem prepared_split_effect (pre post : Document) {blockInst : Nat} (bid index freshBlock freshInstance : Nat)
    (head : Slot) (tail : List Slot) (markerId : Nat × Nat)
    (addresses : ((pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post).flatMap
      (fun b => b.slots.map Slot.address)).Nodup)
    (blocks : ((pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post).map Block.id).Nodup)
    (hidden : head.visible = false) (bound : index ≤ (text (head :: tail)).length)
    (freshBlockName : freshBlock ∉ (pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post).map Block.id)
    (freshRootName : (root freshInstance).address ∉ (pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post).flatMap
      (fun b => b.slots.map Slot.address)) :
    ∃ commands result,
      prepareSplit (pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post) bid index freshBlock freshInstance markerId = some commands ∧
      execute (pre ++ ⟨bid, blockInst, head :: tail, true⟩ :: post) commands = some result ∧
      view result = view pre ++ [(bid, (text (head :: tail)).take index),
        (freshBlock, (text (head :: tail)).drop index)] ++ view post := by
  have prepared := preparedAnchor_structural head tail index hidden bound
  obtain ⟨result, executed, visible⟩ := local_split_client pre post ⟨bid, blockInst, head :: tail, true⟩
    (preparedAnchor head tail index) index freshBlock freshInstance
    (boundary (preparedAnchor head tail index).1 markerId)
    addresses blocks prepared freshBlockName freshRootName rfl rfl
  exact ⟨_, result, prepareSplit_success pre post bid index freshBlock freshInstance head tail markerId blocks bound,
    executed, visible⟩

/-! Hand-derived PASS+FAIL scenarios, independent of the source renderer. -/
private def abcd : Document :=
  [⟨10, 0, [root 0, character 0 (0, 1) 0, character 0 (0, 2) 1,
    character 0 (0, 3) 2, character 0 (0, 4) 3], true⟩]

private def splitAtTwo : List Command :=
  [.create 11 11 (some 10), .split (0, .event (0, 2)) (boundary 0 (1, 10)) 11]

/-- Splitting between b,c produces ab | cd; the split is effective. -/
theorem split_control :
    (execute abcd splitAtTwo).map view = some [(10, [0, 1]), (11, [2, 3])] ∧
    (execute abcd splitAtTwo).map view ≠ some [(10, [0, 1, 2, 3]), (11, [])] := by decide

/-- Prepared deletion hides original b,c even after splitting moves c into a
new block; it is neither a no-op nor confined to the original block. -/
theorem crossing_delete_control :
    (execute abcd (splitAtTwo ++ [.delete [(0, .event (0, 2)), (0, .event (0, 3))]])).map view =
      some [(10, [0]), (11, [3])] ∧
    (execute abcd (splitAtTwo ++ [.delete [(0, .event (0, 2)), (0, .event (0, 3))]])).map view ≠
      some [(10, [0]), (11, [2, 3])] := by decide

/-- Origin lookup follows b into the first new block, while creation places
the second new block after the original request block. The result is a|cd|b,
not a|b|cd. This distinguishes block identity from current anchor ownership. -/
theorem concurrent_split_witness_control :
    (execute abcd [.create 11 11 (some 10),
      .split (0, .event (0, 1)) (boundary 0 (1, 10)) 11,
      .create 12 12 (some 10),
      .split (0, .event (0, 2)) (boundary 0 (2, 10)) 12]).map view =
      some [(10, [0]), (12, [2, 3]), (11, [1])] ∧
    (execute abcd [.create 11 11 (some 10),
      .split (0, .event (0, 1)) (boundary 0 (1, 10)) 11,
      .create 12 12 (some 10),
      .split (0, .event (0, 2)) (boundary 0 (2, 10)) 12]).map view ≠
      some [(10, [0]), (11, [1]), (12, [2, 3])] := by decide

/-- Boundary insertion follows its selected sequential witness order. -/
theorem insert_boundary_control :
    (execute abcd (splitAtTwo ++ [.insert (0, .event (0, 2))
      [character 0 (2, 10) 4]])).map view = some [(10, [0, 1, 4]), (11, [2, 3])] ∧
    (execute abcd (splitAtTwo ++ [.insert (0, .event (0, 2))
      [character 0 (2, 10) 4]])).map view ≠ some [(10, [0, 1]), (11, [4, 2, 3])] := by decide

/-- Bounds are part of valid positional client requests. In particular this
spec deliberately rejects oversized deletion rather than inheriting JS slice
clamping. Valid nearby requests remain accepted. -/
theorem request_bounds_control :
    prepareInsert abcd 10 5 0 [((2, 10), 4)] = none ∧
    prepareInsert abcd 10 4 0 [((2, 10), 4)] ≠ none ∧
    prepareDeleteRequest abcd 10 0 5 = none ∧
    prepareDeleteRequest abcd 10 0 4 ≠ none ∧
    prepareSplit abcd 10 5 11 11 (1, 10) = none ∧
    prepareSplit abcd 10 2 11 11 (1, 10) ≠ none := by decide

#print axioms prepared_insert_effect
#print axioms prepared_delete_effect
#print axioms prepared_split_effect
#print axioms local_insert_document
#print axioms local_delete_document
#print axioms local_split_client

end Sal.MRDTs.Instances.NotionCoreSpec
