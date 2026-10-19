import Sal.MRDTs.Instances.NotionCoreSourceGuards

/-! The published client's selection rule on the core source normal form.
At zero it selects the first slice with a visible character, or the last
slice if none has one; at positive indices it selects the preceding visible
character. On a chain this skips every empty slice before the first visible
character, including a dead title root. Here that actual selection rule is
shown to prepare the required semantic gap.
-/
namespace Sal.MRDTs.Instances.NotionCorePreparation
open NotionCoreSpec (Address Slot PreparedGap)
open NotionCoreSource (Atom Slice Block)

def visibleAtom (atom : Atom) : Bool := match atom.kind with
  | .text _ deleted => !deleted
  | .split => false

def characters (slice : Slice) : List Atom := slice.atoms.filter visibleAtom

/-- A block's slices in chain preorder. -/
def nodes (block : Block) : List Slice := block.slices

def zeroOrigin : List Slice → Option Address
  | [] => none
  | [slice] => some slice.start
  | slice :: next :: rest =>
      if (characters slice).isEmpty then zeroOrigin (next :: rest) else some slice.start

def locate (block : Block) (index : Nat) : Option Address :=
  let chars := (nodes block).flatMap characters
  if index ≤ chars.length then
    match index with
    | 0 => zeroOrigin (nodes block)
    | n + 1 => chars[n]?.map Atom.address
  else none

@[simp] theorem visible_projection (atom : Atom) : atom.slot.visible = visibleAtom atom := by
  cases atom with | mk address kind => cases kind <;> rfl

theorem characters_projection (slice : Slice) :
    slice.slots.filter Slot.visible = (characters slice).map Atom.slot := by
  simp [Slice.slots, Slice.anchor, Slice.close, characters, List.filter_map, Function.comp_def,
    visible_projection]

/-- A selected visible character has a retained coordinate whose visible
prefix count is precisely its visible index plus one. -/
theorem filtered_coordinate (slots : List Slot) (n : Nat) (selected : Slot)
    (found : (slots.filter Slot.visible)[n]? = some selected) :
    ∃ k, ∃ bound : k < slots.length,
      slots[k] = selected ∧ (NotionCoreSpec.text (slots.take (k + 1))).length = n + 1 := by
  induction slots generalizing n with
  | nil => simp at found
  | cons head tail ih =>
    cases hidden : head.visible with
    | false =>
      simp only [List.filter_cons, hidden, Bool.false_eq_true, ↓reduceIte] at found
      obtain ⟨k, bound, selectedAt, count⟩ := ih n found
      refine ⟨k + 1, by simpa using Nat.succ_lt_succ bound, ?_, ?_⟩
      · simpa using selectedAt
      · simpa [NotionCoreSpec.text_cons, hidden, Nat.add_assoc] using count
    | true =>
      cases n with
      | zero =>
        simp [hidden] at found
        subst selected
        exact ⟨0, by simp, rfl, by simp [hidden]⟩
      | succ n =>
        simp only [List.filter_cons, hidden, ↓reduceIte, List.getElem?_cons_succ] at found
        obtain ⟨k, bound, selectedAt, count⟩ := ih n found
        refine ⟨k + 1, by simpa using Nat.succ_lt_succ bound, ?_, ?_⟩
        · simpa using selectedAt
        · simp [NotionCoreSpec.text_cons, hidden, Nat.add_assoc, count]

theorem prepared_hidden_prefix (head : Slot) (slots : List Slot) (origin : Address)
    (index : Nat) (hidden : head.visible = false) (prepared : PreparedGap slots origin index) :
    PreparedGap (head :: slots) origin index := by
  obtain ⟨k, bound, selected, count⟩ := prepared
  refine ⟨k + 1, by simpa using Nat.succ_lt_succ bound, ?_, ?_⟩
  · simpa using selected
  · simpa [NotionCoreSpec.text_cons, hidden, Nat.add_assoc] using count

/-- A prepared gap survives a prefix with no visible character. -/
theorem prepared_invisible_prefix (pre slots : List Slot) (origin : Address) (index : Nat)
    (invisible : NotionCoreSpec.text pre = []) (prepared : PreparedGap slots origin index) :
    PreparedGap (pre ++ slots) origin index := by
  obtain ⟨k, bound, selected, count⟩ := prepared
  refine ⟨pre.length + k, by simp [bound], ?_, ?_⟩
  · rw [List.getElem_append_right (by omega)]
    simpa using selected
  · rw [show pre.length + k + 1 = pre.length + (k + 1) by omega, List.take_length_add_append,
      NotionCoreSpec.text_append, invisible]
    simpa using count

theorem slice_text_characters (slice : Slice) :
    NotionCoreSpec.text slice.slots = (characters slice).map fun atom => atom.slot.value := by
  simp [NotionCoreSpec.text, characters_projection, List.map_map, Function.comp_def]

/-- The zero selection is a start boundary preceded only by invisible slots. -/
theorem zero_prepared (slices : List Slice) (origin : Address)
    (selected : zeroOrigin slices = some origin) :
    PreparedGap (slices.flatMap Slice.slots) origin 0 := by
  have head : ∀ (slice : Slice) (rest : List Slot),
      PreparedGap (slice.slots ++ rest) slice.start 0 := by
    intro slice rest
    exact ⟨0, by simp [Slice.slots], by simp [Slice.slots, Slice.anchor],
      by simp [Slice.slots, Slice.anchor]⟩
  induction slices with
  | nil => simp [zeroOrigin] at selected
  | cons slice rest ih =>
    cases rest with
    | nil =>
      simp only [zeroOrigin, Option.some.injEq] at selected
      subst origin
      simpa using head slice []
    | cons next tail =>
      simp only [zeroOrigin] at selected
      split at selected
      · rename_i empty
        have invisible : NotionCoreSpec.text slice.slots = [] := by
          rw [slice_text_characters, List.isEmpty_iff.mp empty]
          rfl
        rw [List.flatMap_cons]
        exact prepared_invisible_prefix _ _ origin 0 invisible (ih selected)
      · cases selected
        rw [List.flatMap_cons]
        exact head slice _

theorem zeroOrigin_some (slices : List Slice) (nonempty : slices ≠ []) :
    ∃ origin, zeroOrigin slices = some origin := by
  induction slices with
  | nil => exact absurd rfl nonempty
  | cons slice rest ih =>
    cases rest with
    | nil => exact ⟨_, rfl⟩
    | cons next tail =>
      simp only [zeroOrigin]
      split
      · exact ih (by simp)
      · exact ⟨_, rfl⟩

theorem block_characters (block : Block) :
    block.slots.filter Slot.visible = ((nodes block).flatMap characters).map Atom.slot := by
  simp [Block.slots, nodes, List.filter_flatMap, List.map_flatMap, characters_projection]

/-- Successful source location prepares a semantic gap over the whole chain,
including a start boundary after empty slices at zero. -/
theorem locate_prepared (block : Block) (index : Nat) (origin : Address)
    (located : locate block index = some origin) :
    PreparedGap block.project.slots origin index := by
  simp only [locate] at located
  split at located
  · cases index with
    | zero => exact zero_prepared (nodes block) origin located
    | succ n =>
      obtain ⟨atom, found, address⟩ := Option.map_eq_some_iff.mp located
      have mapped : (block.slots.filter Slot.visible)[n]? = some atom.slot := by
        rw [block_characters, List.getElem?_map, found]
        rfl
      obtain ⟨k, bound, selected, count⟩ := filtered_coordinate _ n _ mapped
      show PreparedGap block.slots origin (n + 1)
      exact ⟨k, bound, by rw [selected, NotionCoreSourceDocument.slot_address]; exact address, count⟩
  · simp at located

/-- A located origin is an address of the block's chain. -/
theorem locate_member (block : Block) (index : Nat) (origin : Address)
    (located : locate block index = some origin) : origin ∈ block.traversal := by
  obtain ⟨k, bound, selected, _⟩ := locate_prepared block index origin located
  rw [← NotionCoreSource.Block.slots_addresses]
  exact List.mem_map.mpr ⟨_, List.getElem_mem bound, selected⟩

theorem zeroOrigin_mem (slices : List Slice) (origin : Address)
    (selected : zeroOrigin slices = some origin) : ∃ slice ∈ slices, slice.start = origin := by
  induction slices with
  | nil => simp [zeroOrigin] at selected
  | cons slice rest ih =>
    cases rest with
    | nil =>
      simp only [zeroOrigin, Option.some.injEq] at selected
      exact ⟨slice, by simp, selected⟩
    | cons next tail =>
      simp only [zeroOrigin] at selected
      split at selected
      · obtain ⟨found, member, start⟩ := ih selected
        exact ⟨found, List.mem_cons_of_mem _ member, start⟩
      · exact ⟨slice, by simp, Option.some.inj selected⟩

/-- The two clauses of the source normal form that selection relies on:
every atom lies in its slice's instance, and slice starts and atoms are
positions rather than end slots. -/
def Placed (block : Block) : Prop :=
  (∀ slice ∈ block.slices, ∀ atom ∈ slice.atoms, atom.address.1 = slice.start.1) ∧
  (∀ slice ∈ block.slices, slice.start.2.isEnd = false ∧
    ∀ atom ∈ slice.atoms, atom.address.2.isEnd = false)

theorem normal_placed (block : Block) (normal : block.Normal) : Placed block :=
  ⟨normal.1, normal.2.2.2.2⟩

/-- On a placed block a located origin is a position, never a close slot. -/
theorem locate_position (block : Block) (index : Nat) (origin : Address)
    (placed : Placed block) (located : locate block index = some origin) :
    origin.2.isEnd = false := by
  have positions := placed.2
  simp only [locate] at located
  split at located
  · cases index with
    | zero =>
      obtain ⟨slice, member, rfl⟩ := zeroOrigin_mem (nodes block) origin located
      exact (positions slice member).1
    | succ n =>
      obtain ⟨atom, found, rfl⟩ := Option.map_eq_some_iff.mp located
      obtain ⟨slice, member, selected⟩ := List.mem_flatMap.mp (List.mem_of_getElem? found)
      exact (positions slice member).2 atom (List.mem_filter.mp selected).1
  · simp at located

/-- On a placed block every slice holding an address starts in its instance. -/
theorem placed_agrees (block : Block) (origin : Address) (placed : Placed block) :
    NotionCoreSource.InstanceAgrees origin block.slices := fun slice member held =>
  (NotionCoreSource.traversal_instance slice origin (placed.1 slice member) held).symm

/-- Every legal source insertion index of an alive block returns an address. -/
theorem locate_progress (block : Block) (index : Nat) (alive : block.alive = true)
    (bound : index ≤ ((nodes block).flatMap characters).length) :
    ∃ origin, locate block index = some origin := by
  simp only [locate, bound, ↓reduceIte]
  cases index with
  | zero =>
    apply zeroOrigin_some
    simpa [Block.alive, nodes] using alive
  | succ n =>
    have within : n < ((nodes block).flatMap characters).length := by omega
    simp only [List.getElem?_eq_getElem within, Option.map_some]
    exact ⟨_, rfl⟩

/-- The source's visible range selection, before per-instance range encoding. -/
def deleteTargets (block : Block) (start stop : Nat) : List Address :=
  (((nodes block).flatMap characters).drop start |>.take (stop - start)).map Atom.address

theorem filter_take_gap (slots : List Slot) (n : Nat) :
    (slots.take (NotionCoreSpec.gapIndex slots n)).filter Slot.visible =
      (slots.filter Slot.visible).take n := by
  induction slots generalizing n with
  | nil => cases n <;> simp [NotionCoreSpec.gapIndex]
  | cons slot rest ih =>
    cases n with
    | zero => simp [NotionCoreSpec.gapIndex]
    | succ n => cases h : slot.visible <;> simp [NotionCoreSpec.gapIndex, h, ih]

theorem filter_drop_gap (slots : List Slot) (n : Nat) :
    (slots.drop (NotionCoreSpec.gapIndex slots n)).filter Slot.visible =
      (slots.filter Slot.visible).drop n := by
  induction slots generalizing n with
  | nil => cases n <;> simp [NotionCoreSpec.gapIndex]
  | cons slot rest ih =>
    cases n with
    | zero => simp [NotionCoreSpec.gapIndex]
    | succ n => cases h : slot.visible <;> simp [NotionCoreSpec.gapIndex, h, ih]

theorem projected_characters (block : Block) :
    block.project.slots.filter Slot.visible = ((nodes block).flatMap characters).map Atom.slot :=
  block_characters block

/-- Identity selection agrees exactly; no rendered-string roundtrip is used.
The nonnegative bounded range domain is shared with the independent client.
Compression into same-session ID ranges is a separate message encoding step. -/
theorem delete_targets_projection (block : Block) (start stop : Nat) :
    deleteTargets block start stop =
      NotionCoreSpec.prepareDelete block.project.slots start (stop - start) := by
  simp only [deleteTargets, NotionCoreSpec.prepareDelete,
    NotionCoreSpec.targetsIn, filter_take_gap, filter_drop_gap, projected_characters,
    ← List.map_drop, ← List.map_take, List.map_map, Function.comp_def,
    NotionCoreSourceDocument.slot_address]

/-- Local insertion into an alive block works for the actual selected semantic
gap, not just the canonical independent helper's choice of an invisible
anchor. -/
theorem insert_at_prepared_gap (pre post : NotionCoreSpec.Document)
    (source : NotionCoreSpec.Block) (origin : Address) (index : Nat) (fresh : List Slot)
    (unique : ((pre ++ source :: post).flatMap
      (fun block => block.slots.map Slot.address)).Nodup)
    (prepared : PreparedGap source.slots origin index) (live : source.alive = true) :
    ∃ result, NotionCoreSpec.step (pre ++ source :: post) (.insert origin fresh) = some result ∧
      NotionCoreSpec.view result = NotionCoreSpec.view pre ++
        [(source.id, (NotionCoreSpec.text source.slots).take index ++
          NotionCoreSpec.text fresh ++ (NotionCoreSpec.text source.slots).drop index)] ++
        NotionCoreSpec.view post := by
  have present : origin ∈ source.slots.map Slot.address := by
    obtain ⟨k, bound, selected, _⟩ := prepared
    exact List.mem_map.mpr ⟨source.slots[k], List.getElem_mem bound, selected⟩
  have structural := NotionCoreSpec.address_focus pre post source origin unique present
  refine ⟨_, NotionCoreSpec.step_insert_focus pre post source origin fresh present structural.2, ?_⟩
  have cut := NotionCoreSpec.preparedGap_visible source.slots origin index structural.1 prepared
  simp only [NotionCoreSpec.view, List.filter_append, List.filter_cons, live, ↓reduceIte,
    List.map_append, List.map_cons, NotionCoreSpec.insertSlots, NotionCoreSpec.text_append, cut.1, cut.2,
    List.append_assoc, List.singleton_append]

def textRun (inst : Nat) (entries : List ((Nat × Nat) × Nat)) : List Atom :=
  entries.map fun entry => ⟨(inst, .event entry.1), .text entry.2 false⟩

theorem text_run_projection (inst : Nat) (entries : List ((Nat × Nat) × Nat)) :
    (textRun inst entries).map Atom.slot = NotionCoreSpec.characterRun inst entries := by
  simp [textRun, NotionCoreSpec.characterRun, Atom.slot, NotionCoreSpec.character,
    List.map_map, Function.comp_def]

/-- Source selection followed by the independently implemented physical insert
executes and has the requested whole-document effect. The instance comes from
the selected origin. Entry IDs are supplied; contiguous fresh allocation and
same-instance shape preservation remain separate from this immediate effect. -/
theorem source_insert_effect (pre post : NotionCoreSourceDocument.Document)
    (block : Block) (index : Nat) (entries : List ((Nat × Nat) × Nat))
    (unique : (NotionCoreInvariant.addresses
      (NotionCoreSourceDocument.project (pre ++ block :: post))).Nodup)
    (alive : block.alive = true) (placed : Placed block)
    (bound : index ≤ ((nodes block).flatMap characters).length) :
    ∃ origin result, locate block index = some origin ∧
      NotionCoreSourceDocument.step (pre ++ block :: post)
        (.insert origin (textRun origin.1 entries)) = some result ∧
      NotionCoreSpec.view (NotionCoreSourceDocument.project result) =
        NotionCoreSpec.view (NotionCoreSourceDocument.project pre) ++
        [(block.id, (NotionCoreSpec.text block.project.slots).take index ++
          entries.map Prod.snd ++ (NotionCoreSpec.text block.project.slots).drop index)] ++
        NotionCoreSpec.view (NotionCoreSourceDocument.project post) := by
  obtain ⟨origin, located⟩ := locate_progress block index alive bound
  have unique' : (((NotionCoreSourceDocument.project pre) ++ block.project ::
      NotionCoreSourceDocument.project post).flatMap
      (fun block => block.slots.map Slot.address)).Nodup := by
    simpa [NotionCoreSourceDocument.project, NotionCoreInvariant.addresses] using unique
  obtain ⟨semantic, accepted, answer⟩ := insert_at_prepared_gap
    (NotionCoreSourceDocument.project pre) (NotionCoreSourceDocument.project post)
    block.project origin index ((textRun origin.1 entries).map Atom.slot) unique'
    (locate_prepared block index origin located) alive
  have projected := NotionCoreSourceDocument.project_insert
    (pre ++ block :: post) origin (textRun origin.1 entries)
    (fun other member => NotionCoreSourceGuards.block_unique unique member)
    (locate_position block index origin placed located)
  rw [show NotionCoreSourceDocument.project (pre ++ block :: post) =
      NotionCoreSourceDocument.project pre ++ block.project ::
        NotionCoreSourceDocument.project post by simp [NotionCoreSourceDocument.project],
    accepted] at projected
  obtain ⟨result, executed, same⟩ := Option.map_eq_some_iff.mp projected
  refine ⟨origin, result, located, executed, ?_⟩
  rw [same]
  simpa only [NotionCoreSourceDocument.project_id, text_run_projection,
    NotionCoreSpec.text_characterRun] using answer

theorem project_anchored (block : Block) (alive : block.alive = true) :
    NotionCoreSpec.Anchored block.project := by
  cases slices : block.slices with
  | nil => simp [Block.alive, slices] at alive
  | cons first rest =>
    exact ⟨first.anchor, first.atoms.map Atom.slot ++ [first.close] ++ rest.flatMap Slice.slots,
      by simp [Block.project, Block.slots, slices, Slice.slots], rfl⟩

/-- The actual visible identity selection, before ID-range compression, gives
the exact deletion effect in the physical document. Unrelated blocks retain
their views. The theorem uses legal nonnegative half-open ranges. -/
theorem source_delete_effect (pre post : NotionCoreSourceDocument.Document)
    (block : Block) (start stop : Nat)
    (unique : (NotionCoreInvariant.addresses
      (NotionCoreSourceDocument.project (pre ++ block :: post))).Nodup)
    (alive : block.alive = true)
    (ordered : start ≤ stop) :
    ∃ result, NotionCoreSourceDocument.step (pre ++ block :: post)
        (.delete (deleteTargets block start stop)) = some result ∧
      NotionCoreSpec.view (NotionCoreSourceDocument.project result) =
        NotionCoreSpec.view (NotionCoreSourceDocument.project pre) ++
        [(block.id, (NotionCoreSpec.text block.project.slots).take start ++
          (NotionCoreSpec.text block.project.slots).drop stop)] ++
        NotionCoreSpec.view (NotionCoreSourceDocument.project post) := by
  obtain ⟨head, tail, slots, _⟩ := project_anchored block alive
  have blockEq : (⟨block.id, block.inst, head :: tail, true⟩ : NotionCoreSpec.Block) = block.project :=
    NotionCoreSourceDocument.spec_block_ext rfl slots.symm alive.symm rfl
  have unique' : ((NotionCoreSourceDocument.project pre ++
      (⟨block.id, block.inst, head :: tail, true⟩ : NotionCoreSpec.Block) :: NotionCoreSourceDocument.project post).flatMap
      (fun block => block.slots.map Slot.address)).Nodup := by
    simpa [blockEq, NotionCoreSourceDocument.project, NotionCoreInvariant.addresses] using unique
  obtain ⟨semantic, accepted, answer⟩ := NotionCoreSpec.local_delete_document
    (NotionCoreSourceDocument.project pre) (NotionCoreSourceDocument.project post)
    block.id head tail start (stop - start) unique'
  have projected := NotionCoreSourceDocument.project_delete
    (pre ++ block :: post) (deleteTargets block start stop)
  rw [delete_targets_projection, slots] at projected
  have input : NotionCoreSourceDocument.project (pre ++ block :: post) =
      NotionCoreSourceDocument.project pre ++ ⟨block.id, block.inst, head :: tail, true⟩ ::
        NotionCoreSourceDocument.project post := by simp [blockEq, NotionCoreSourceDocument.project]
  rw [input, accepted] at projected
  obtain ⟨result, executed, same⟩ := Option.map_eq_some_iff.mp projected
  refine ⟨result, ?_, ?_⟩
  · simpa only [← slots, ← delete_targets_projection] using executed
  · rw [same]
    simpa only [slots, Nat.add_sub_of_le ordered] using answer

/-- The source-selected origin produces the ordinary local split through the
independent command machine. -/
theorem source_split_message_effect (pre post : NotionCoreSourceDocument.Document)
    (block : Block) (index bid inst : Nat) (markerId : Nat × Nat)
    (unique : (NotionCoreInvariant.addresses
      (NotionCoreSourceDocument.project (pre ++ block :: post))).Nodup)
    (blocks : ((pre ++ block :: post).map Block.id).Nodup)
    (alive : block.alive = true)
    (bound : index ≤ ((nodes block).flatMap characters).length)
    (freshBlock : bid ∉ (pre ++ block :: post).map Block.id)
    (freshRoot : (NotionCoreSpec.root inst).address ∉ NotionCoreInvariant.addresses
      (NotionCoreSourceDocument.project (pre ++ block :: post)))
    (freshFinish : (NotionCoreSpec.finishSlot inst).address ∉ NotionCoreInvariant.addresses
      (NotionCoreSourceDocument.project (pre ++ block :: post))) :
    ∃ origin result, locate block index = some origin ∧
      NotionCoreSpec.execute (NotionCoreSourceDocument.project (pre ++ block :: post))
        [.create bid inst (some block.id), .split origin markerId bid] = some result ∧
      NotionCoreSpec.view result =
        NotionCoreSpec.view (NotionCoreSourceDocument.project pre) ++
        [(block.id, (NotionCoreSpec.text block.project.slots).take index),
          (bid, (NotionCoreSpec.text block.project.slots).drop index)] ++
        NotionCoreSpec.view (NotionCoreSourceDocument.project post) := by
  obtain ⟨origin, located⟩ := locate_progress block index alive bound
  have input : NotionCoreSourceDocument.project (pre ++ block :: post) =
      NotionCoreSourceDocument.project pre ++ block.project ::
        NotionCoreSourceDocument.project post := by simp [NotionCoreSourceDocument.project]
  obtain ⟨result, accepted, answer⟩ := NotionCoreSpec.local_split_client
    (NotionCoreSourceDocument.project pre) (NotionCoreSourceDocument.project post)
    block.project origin index bid inst markerId
    (by simpa only [NotionCoreInvariant.addresses, input] using unique)
    (by simpa [NotionCoreSourceDocument.project] using blocks)
    (locate_prepared block index origin located)
    (by simpa [NotionCoreSourceDocument.project] using freshBlock)
    (by simpa only [NotionCoreInvariant.addresses, input] using freshRoot)
    (by simpa only [NotionCoreInvariant.addresses, input] using freshFinish) alive
  exact ⟨origin, result, located, by simpa only [input] using accepted, answer⟩

theorem create_empty_target {doc created : NotionCoreSourceDocument.Document}
    (bid inst : Nat) (after : Option Nat)
    (accepted : NotionCoreSourceDocument.step doc (.create bid inst after) = some created) :
    ∃ target ∈ created, target.id = bid ∧ NotionCoreSourceDocument.EmptyRoot target := by
  by_cases duplicate : bid ∈ doc.map Block.id
  · simp [NotionCoreSourceDocument.step, duplicate] at accepted
  · cases after with
    | none =>
      simp only [NotionCoreSourceDocument.step, duplicate, ↓reduceIte,
        Option.some.injEq] at accepted
      subst created
      exact ⟨NotionCoreSourceDocument.freshBlock bid inst, by simp, rfl, rfl⟩
    | some previous =>
      by_cases present : previous ∈ doc.map Block.id
      · simp only [NotionCoreSourceDocument.step, duplicate, present, ↓reduceIte,
          Option.some.injEq] at accepted
        subst created
        obtain ⟨block, member, same⟩ := List.mem_map.mp present
        exact ⟨NotionCoreSourceDocument.freshBlock bid inst,
          List.mem_flatMap.mpr ⟨block, member, by simp [same]⟩, rfl, rfl⟩
      · simp [NotionCoreSourceDocument.step, duplicate, present] at accepted

/-- An independently legal split lifts to the physical interval transition
when its named destination is an empty source root, its origin is a position,
and the slices of the origin's owner holding it start in its instance. This
domain lemma inspects the physical transition; it does not assume that
transition succeeds. -/
theorem split_progress {doc : NotionCoreSourceDocument.Document}
    (origin : Address) (marker : Nat × Nat) (bid : Nat)
    (unique : (doc.map Block.id).Nodup)
    (empty : ∃ target ∈ doc, target.id = bid ∧ NotionCoreSourceDocument.EmptyRoot target)
    (position : origin.2.isEnd = false)
    (agrees : ∀ source, NotionCoreSourceDocument.owner doc origin = some source →
      NotionCoreSource.InstanceAgrees origin source.slices)
    (semantic : ∃ next, NotionCoreSpec.step (NotionCoreSourceDocument.project doc)
      (.split origin marker bid) = some next) :
    ∃ next, NotionCoreSourceDocument.step doc (.split origin marker bid) = some next := by
  obtain ⟨target, member, same, emptyRoot⟩ := empty
  have targetFound : doc.find? (fun block => block.id == bid) = some target := by
    obtain ⟨pre, post, shape⟩ := List.append_of_mem member
    apply List.find?_eq_some_iff_append.mpr
    refine ⟨by simp [same], pre, post, shape, ?_⟩
    intro earlier before
    have names : (pre.map Block.id ++ target.id :: post.map Block.id).Nodup := by
      simpa [shape] using unique
    have distinct : earlier.id ≠ bid := by
      intro collision
      exact List.disjoint_left.mp (List.nodup_append'.mp names).2.2
        (List.mem_map.mpr ⟨earlier, before, rfl⟩) (by simp [collision, same])
    simp [distinct]
  obtain ⟨next, accepted⟩ := semantic
  cases owned : NotionCoreSourceDocument.owner doc origin with
  | none =>
    have absent := NotionCoreSourceDocument.owner_project doc origin
    simp only [owned, Option.map_none] at absent
    simp [NotionCoreSpec.step, absent] at accepted
  | some source =>
    have found := NotionCoreSourceDocument.owner_project doc origin
    simp only [owned, Option.map_some] at found
    have different : source.id ≠ bid := by
      intro collision
      simp [NotionCoreSpec.step, found, collision] at accepted
    simp [NotionCoreSourceDocument.step, position, owned, targetFound, different, emptyRoot,
      agrees source owned]

theorem create_retains_block {doc created : NotionCoreSourceDocument.Document}
    (bid inst : Nat) (after : Option Nat) (block : Block)
    (member : block ∈ doc)
    (accepted : NotionCoreSourceDocument.step doc (.create bid inst after) = some created) :
    block ∈ created := by
  by_cases duplicate : bid ∈ doc.map Block.id
  · simp [NotionCoreSourceDocument.step, duplicate] at accepted
  · cases after with
    | none =>
      simp only [NotionCoreSourceDocument.step, duplicate, ↓reduceIte,
        Option.some.injEq] at accepted
      subst created
      exact List.mem_cons_of_mem _ member
    | some previous =>
      by_cases present : previous ∈ doc.map Block.id
      · simp only [NotionCoreSourceDocument.step, duplicate, present, ↓reduceIte,
          Option.some.injEq] at accepted
        subst created
        exact List.mem_flatMap.mpr ⟨block, member, by split <;> simp⟩
      · simp [NotionCoreSourceDocument.step, duplicate, present] at accepted

/-- Physical source-normal-form create/split execution has the requested
prefix/suffix effect for the source's actual selected origin. The split cuts
the chain at the located slice: the slices before it and its left part stay,
and its right part with every later slice moves to the fresh block. -/
theorem source_split_effect (pre post : NotionCoreSourceDocument.Document)
    (block : Block) (index bid inst : Nat) (markerId : Nat × Nat)
    (unique : (NotionCoreInvariant.addresses
      (NotionCoreSourceDocument.project (pre ++ block :: post))).Nodup)
    (blocks : ((pre ++ block :: post).map Block.id).Nodup)
    (alive : block.alive = true) (placed : Placed block)
    (bound : index ≤ ((nodes block).flatMap characters).length)
    (freshBlock : bid ∉ (pre ++ block :: post).map Block.id)
    (freshRoot : (NotionCoreSpec.root inst).address ∉ NotionCoreInvariant.addresses
      (NotionCoreSourceDocument.project (pre ++ block :: post)))
    (freshFinish : (NotionCoreSpec.finishSlot inst).address ∉ NotionCoreInvariant.addresses
      (NotionCoreSourceDocument.project (pre ++ block :: post))) :
    ∃ origin created result, locate block index = some origin ∧
      NotionCoreSourceDocument.step (pre ++ block :: post)
        (.create bid inst (some block.id)) = some created ∧
      NotionCoreSourceDocument.step created (.split origin markerId bid) = some result ∧
      NotionCoreSpec.view (NotionCoreSourceDocument.project result) =
        NotionCoreSpec.view (NotionCoreSourceDocument.project pre) ++
        [(block.id, (NotionCoreSpec.text block.project.slots).take index),
          (bid, (NotionCoreSpec.text block.project.slots).drop index)] ++
        NotionCoreSpec.view (NotionCoreSourceDocument.project post) := by
  obtain ⟨origin, semanticResult, located, semanticRun, answer⟩ :=
    source_split_message_effect pre post block index bid inst markerId unique blocks alive bound
      freshBlock freshRoot freshFinish
  let before := NotionCoreSourceDocument.project (pre ++ block :: post)
  let middle := NotionCoreSourceDocument.project pre ++ block.project ::
    ⟨bid, inst, [NotionCoreSpec.root inst, NotionCoreSpec.finishSlot inst], true⟩ ::
      NotionCoreSourceDocument.project post
  have input : before = NotionCoreSourceDocument.project pre ++ block.project ::
      NotionCoreSourceDocument.project post := by simp [before, NotionCoreSourceDocument.project]
  have names : (before.map NotionCoreSpec.Block.id).Nodup := by
    simpa only [before, NotionCoreSourceDocument.project_ids] using blocks
  have fresh : bid ∉ before.map NotionCoreSpec.Block.id := by
    simpa only [before, NotionCoreSourceDocument.project_ids] using freshBlock
  have semanticCreate : NotionCoreSpec.step before (.create bid inst (some block.id)) = some middle := by
    rw [input]
    exact NotionCoreSpec.step_create_focus _ _ block.project bid inst (input ▸ names) (input ▸ fresh)
  have physicalCreate := NotionCoreSourceDocument.project_create
    (pre ++ block :: post) bid inst (some block.id)
  rw [semanticCreate] at physicalCreate
  obtain ⟨created, createdStep, createdProjection⟩ := Option.map_eq_some_iff.mp physicalCreate
  have oldWellFormed : NotionCoreSpec.WellFormed before := by
    refine ⟨names, unique, ?_⟩
    intro projected member live
    obtain ⟨old, _, equal⟩ := List.mem_map.mp member
    subst projected
    exact project_anchored old live
  have middleWellFormed : NotionCoreSpec.WellFormed middle := by
    apply NotionCoreInvariant.step_preserves oldWellFormed _ semanticCreate
    rw [input]
    exact .create_after _ _ _ bid inst (input ▸ fresh) (input ▸ freshRoot) (input ▸ freshFinish)
  have createdWellFormed : NotionCoreSpec.WellFormed (NotionCoreSourceDocument.project created) :=
    createdProjection ▸ middleWellFormed
  have semanticSplit : NotionCoreSpec.step middle
      (.split origin markerId bid) = some semanticResult := by
    have semanticCreate' : NotionCoreSpec.step
        (NotionCoreSourceDocument.project (pre ++ block :: post))
        (.create bid inst (some block.id)) = some middle := semanticCreate
    simpa [NotionCoreSpec.execute, semanticCreate'] using semanticRun
  have agrees : ∀ source, NotionCoreSourceDocument.owner created origin = some source →
      NotionCoreSource.InstanceAgrees origin source.slices := by
    intro source owned
    obtain ⟨sourceMember, held⟩ := NotionCoreSourceDocument.owner_some owned
    have same := NotionCoreSourceGuards.owner_unique createdWellFormed.2.1 sourceMember
      (create_retains_block bid inst (some block.id) block (by simp) createdStep) held
      (locate_member block index origin located)
    rw [same]
    exact placed_agrees block origin placed
  obtain ⟨result, splitStep⟩ := split_progress origin markerId bid
    (by simpa only [NotionCoreSourceDocument.project_ids] using createdWellFormed.1)
    (create_empty_target bid inst (some block.id) createdStep)
    (locate_position block index origin placed located) agrees
    ⟨semanticResult, by simpa only [createdProjection] using semanticSplit⟩
  have projectedStep := NotionCoreSourceGuards.step_sound
    (.split origin markerId bid) createdWellFormed splitStep
  change NotionCoreSpec.step (NotionCoreSourceDocument.project created)
    (.split origin markerId bid) = some (NotionCoreSourceDocument.project result) at projectedStep
  rw [createdProjection, semanticSplit] at projectedStep
  exact ⟨origin, created, result, located, createdStep, splitStep,
    (congrArg NotionCoreSpec.view (Option.some.inj projectedStep)).symm.trans answer⟩

private def destinationExample : Block :=
  ⟨10, 10, [⟨(10, .start), [], none⟩, ⟨(0, .event (1, 10)),
    [⟨(0, .event (0, 1)), .text 97 true⟩,
     ⟨(0, .event (0, 2)), .text 98 false⟩], none⟩]⟩

/-- Source zero preparation skips the empty dead title and uses the split
marker that follows it, including when all text is hidden. It does not use
the independent helper's choice of the block's head slot. -/
theorem zero_origin_control :
    locate destinationExample 0 = some (0, .event (1, 10)) ∧
    locate destinationExample 0 ≠ NotionCoreSpec.prepareGap destinationExample.project.slots 0 ∧
    locate {destinationExample with slices := [⟨(10, .start), [], none⟩, ⟨(0, .event (1, 10)),
      [⟨(0, .event (0, 1)), .text 97 true⟩], none⟩]} 0 = some (0, .event (1, 10)) := by decide

/-- The positive index selects the visible predecessor through tombstones;
the same source branch rejects an oversized insertion index. -/
theorem positive_origin_control :
    locate destinationExample 1 = some (0, .event (0, 2)) ∧
    locate destinationExample 1 ≠ some (0, .event (0, 1)) ∧
    locate destinationExample 2 = none := by decide

theorem range_selection_control :
    deleteTargets destinationExample 0 1 = [(0, .event (0, 2))] ∧
    deleteTargets destinationExample 0 1 ≠ [(0, .event (0, 1))] := by decide

/-- At zero in a split destination, the selected marker transfers every
remaining visible atom. The empty dead title must not capture the cut. -/
theorem physical_split_control :
    let result := do
      let origin ← locate destinationExample 0
      let created ← NotionCoreSourceDocument.step [destinationExample] (.create 11 11 (some 10))
      NotionCoreSourceDocument.step created (.split origin (1, 11) 11)
    result.map (fun doc => NotionCoreSpec.view (NotionCoreSourceDocument.project doc)) =
      some [(10, []), (11, [98])] ∧
    result.map (fun doc => NotionCoreSpec.view (NotionCoreSourceDocument.project doc)) ≠
      some [(10, [98]), (11, [])] := by decide

private def mergedExample : Block :=
  ⟨10, 10, [⟨(10, .start), [⟨(10, .event (0, 1)), .text 97 false⟩], none⟩,
    ⟨(20, .start), [⟨(20, .event (0, 2)), .text 98 false⟩], none⟩]⟩

/-- In a merged chain, positions count visible characters across slices:
index 1 selects a, and a split there keeps a, stopped at the marker, and moves
the marker's empty slice, ending at the finish of instance 10, and the
absorbed root with b into the fresh block, rather than leaving an empty
absorbed slice behind. -/
theorem merged_chain_control :
    locate mergedExample 1 = some (10, .event (0, 1)) ∧
    locate mergedExample 2 = some (20, .event (0, 2)) ∧
    (do
      let origin ← locate mergedExample 1
      let created ← NotionCoreSourceDocument.step [mergedExample] (.create 11 11 (some 10))
      NotionCoreSourceDocument.step created (.split origin (1, 11) 11)).map
        (fun (doc : NotionCoreSourceDocument.Document) => doc.map NotionCoreSource.Block.slices) =
      some [[⟨(10, .start), [⟨(10, .event (0, 1)), .text 97 false⟩], some (10, .event (1, 11))⟩],
        [⟨(11, .start), [], none⟩, ⟨(10, .event (1, 11)), [], none⟩,
          ⟨(20, .start), [⟨(20, .event (0, 2)), .text 98 false⟩], none⟩]] ∧
    locate mergedExample 1 ≠ some (20, .start) := by decide

#print axioms locate_prepared
#print axioms source_insert_effect
#print axioms source_delete_effect
#print axioms source_split_message_effect
#print axioms source_split_effect
end Sal.MRDTs.Instances.NotionCorePreparation
