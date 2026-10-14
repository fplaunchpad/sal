import Sal.MRDTs.Instances.NotionCoreSourceGuards

/-! The published client's selection rule on the core source normal form.
At zero it selects the first nonempty slice, or the last slice if all are empty;
at positive indices it selects the preceding visible character. This differs
from the independent helper at an attached block's zero position. Here that
actual selection rule is shown to prepare the required semantic gap.
Extraction of these one/two-node blocks from replay remains separate.
-/
namespace Sal.MRDTs.Instances.NotionCorePreparation
open NotionCoreSpec (Address Slot PreparedGap)
open NotionCoreSource (Atom Slice Block)

def visibleAtom (atom : Atom) : Bool := match atom.kind with
  | .text _ deleted => !deleted
  | .split => false

def characters (slice : Slice) : List Atom := slice.atoms.filter visibleAtom

/-- Core source tree preorder: own root alone, or empty title root and leaf. -/
def nodes (block : Block) : List Slice := match block.shape with
  | .own => [block.active]
  | .attached inst => [⟨(inst, .start), []⟩, block.active]

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

theorem nodes_characters (block : Block) :
    (nodes block).flatMap characters = characters block.active := by
  cases shape : block.shape <;> simp [nodes, shape, characters]

theorem zero_origin (block : Block) : zeroOrigin (nodes block) = some block.active.start := by
  cases shape : block.shape <;> simp [nodes, shape, zeroOrigin, characters]

theorem characters_projection (slice : Slice) :
    slice.slots.filter Slot.visible = (characters slice).map Atom.slot := by
  simp [Slice.slots, Slice.anchor, characters, List.filter_map, Function.comp_def, visible_projection]

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

/-- Successful source location prepares a semantic gap, including the active
leaf marker at zero rather than the unused title-root address. -/
theorem locate_active_prepared (block : Block) (index : Nat) (origin : Address)
    (located : locate block index = some origin) :
    PreparedGap block.active.slots origin index := by
  simp only [locate, nodes_characters] at located
  split at located
  · cases index with
    | zero =>
      rw [zero_origin] at located
      cases located
      exact ⟨0, by simp [Slice.slots], rfl, by simp [Slice.slots, Slice.anchor]⟩
    | succ n =>
      obtain ⟨atom, found, address⟩ := Option.map_eq_some_iff.mp located
      have mapped : (block.active.slots.filter Slot.visible)[n]? = some atom.slot := by
        rw [characters_projection, List.getElem?_map, found]
        rfl
      obtain ⟨k, bound, selected, count⟩ := filtered_coordinate _ n _ mapped
      exact ⟨k, bound, by rw [selected, NotionCoreSourceDocument.slot_address]; exact address, count⟩
  · simp at located
theorem locate_prepared (block : Block) (index : Nat) (origin : Address)
    (located : locate block index = some origin) :
    PreparedGap block.project.slots origin index := by
  have active := locate_active_prepared block index origin located
  cases shape : block.shape with
  | own => simpa [Block.project, shape] using active
  | attached inst =>
    simpa [Block.project, shape] using prepared_hidden_prefix (NotionCoreSpec.root inst) block.active.slots origin index rfl active

/-- Every legal source insertion index returns an address. -/
theorem locate_progress (block : Block) (index : Nat)
    (bound : index ≤ (characters block.active).length) :
    ∃ origin, locate block index = some origin := by
  simp only [locate, nodes_characters, bound, ↓reduceIte]
  cases index with
  | zero => exact ⟨_, zero_origin block⟩
  | succ n =>
    have within : n < (characters block.active).length := by omega
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
    block.project.slots.filter Slot.visible = (characters block.active).map Atom.slot := by
  cases shape : block.shape <;>
    simp [Block.project, shape, NotionCoreSpec.root, characters_projection]

/-- Identity selection agrees exactly; no rendered-string roundtrip is used.
The nonnegative bounded range domain is shared with the independent client.
Compression into same-session ID ranges is a separate message encoding step. -/
theorem delete_targets_projection (block : Block) (start stop : Nat) :
    deleteTargets block start stop =
      NotionCoreSpec.prepareDelete block.project.slots start (stop - start) := by
  simp only [deleteTargets, nodes_characters, NotionCoreSpec.prepareDelete,
    NotionCoreSpec.targetsIn, filter_take_gap, filter_drop_gap, projected_characters,
    ← List.map_drop, ← List.map_take, List.map_map, Function.comp_def,
    NotionCoreSourceDocument.slot_address]

/-- Local insertion works for the actual selected semantic gap, not just the
canonical independent helper's choice of an invisible anchor. -/
theorem insert_at_prepared_gap (pre post : NotionCoreSpec.Document)
    (source : NotionCoreSpec.Block) (origin : Address) (index : Nat) (fresh : List Slot)
    (unique : ((pre ++ source :: post).flatMap
      (fun block => block.slots.map Slot.address)).Nodup)
    (prepared : PreparedGap source.slots origin index) :
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
  simp only [NotionCoreSpec.view, List.map_append, List.map_cons,
    NotionCoreSpec.insertSlots, NotionCoreSpec.text_append, cut.1, cut.2,
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
    (bound : index ≤ (characters block.active).length) :
    ∃ origin result, locate block index = some origin ∧
      NotionCoreSourceDocument.step (pre ++ block :: post)
        (.insert origin (textRun origin.1 entries)) = some result ∧
      NotionCoreSpec.view (NotionCoreSourceDocument.project result) =
        NotionCoreSpec.view (NotionCoreSourceDocument.project pre) ++
        [(block.id, (NotionCoreSpec.text block.project.slots).take index ++
          entries.map Prod.snd ++ (NotionCoreSpec.text block.project.slots).drop index)] ++
        NotionCoreSpec.view (NotionCoreSourceDocument.project post) := by
  obtain ⟨origin, located⟩ := locate_progress block index bound
  obtain ⟨k, within, selected, _⟩ := locate_active_prepared block index origin located
  have active : origin ∈ block.active.traversal := by
    rw [← NotionCoreSourceDocument.active_addresses]
    exact List.mem_map.mpr ⟨_, List.getElem_mem within, selected⟩
  have safe := NotionCoreSourceGuards.originSafe_of_active unique
    (by simp : block ∈ pre ++ block :: post) active
  have unique' : (((NotionCoreSourceDocument.project pre) ++ block.project ::
      NotionCoreSourceDocument.project post).flatMap
      (fun block => block.slots.map Slot.address)).Nodup := by
    simpa [NotionCoreSourceDocument.project, NotionCoreInvariant.addresses] using unique
  obtain ⟨semantic, accepted, answer⟩ := insert_at_prepared_gap
    (NotionCoreSourceDocument.project pre) (NotionCoreSourceDocument.project post)
    block.project origin index ((textRun origin.1 entries).map Atom.slot) unique'
    (locate_prepared block index origin located)
  have projected := NotionCoreSourceDocument.project_insert
    (pre ++ block :: post) origin (textRun origin.1 entries) safe
  rw [show NotionCoreSourceDocument.project (pre ++ block :: post) =
      NotionCoreSourceDocument.project pre ++ block.project ::
        NotionCoreSourceDocument.project post by simp [NotionCoreSourceDocument.project],
    accepted] at projected
  obtain ⟨result, executed, same⟩ := Option.map_eq_some_iff.mp projected
  refine ⟨origin, result, located, executed, ?_⟩
  rw [same]
  simpa only [NotionCoreSourceDocument.project_id, text_run_projection,
    NotionCoreSpec.text_characterRun] using answer

theorem project_anchored (block : Block) : NotionCoreSpec.Anchored block.project := by
  cases shape : block.shape with
  | own => exact ⟨block.active.anchor, block.active.atoms.map Atom.slot, by simp [Block.project, shape, Slice.slots], rfl⟩
  | attached inst => exact ⟨NotionCoreSpec.root inst, block.active.slots, by simp [Block.project, shape], rfl⟩

/-- The actual visible identity selection, before ID-range compression, gives
the exact deletion effect in the physical document. Unrelated blocks retain
their views. The theorem uses legal nonnegative half-open ranges. -/
theorem source_delete_effect (pre post : NotionCoreSourceDocument.Document)
    (block : Block) (start stop : Nat)
    (unique : (NotionCoreInvariant.addresses
      (NotionCoreSourceDocument.project (pre ++ block :: post))).Nodup)
    (ordered : start ≤ stop) :
    ∃ result, NotionCoreSourceDocument.step (pre ++ block :: post)
        (.delete (deleteTargets block start stop)) = some result ∧
      NotionCoreSpec.view (NotionCoreSourceDocument.project result) =
        NotionCoreSpec.view (NotionCoreSourceDocument.project pre) ++
        [(block.id, (NotionCoreSpec.text block.project.slots).take start ++
          (NotionCoreSpec.text block.project.slots).drop stop)] ++
        NotionCoreSpec.view (NotionCoreSourceDocument.project post) := by
  obtain ⟨head, tail, slots, _⟩ := project_anchored block
  have blockEq : (⟨block.id, head :: tail⟩ : NotionCoreSpec.Block) = block.project :=
    NotionCoreSourceDocument.spec_block_ext rfl slots.symm
  have unique' : ((NotionCoreSourceDocument.project pre ++
      (⟨block.id, head :: tail⟩ : NotionCoreSpec.Block) :: NotionCoreSourceDocument.project post).flatMap
      (fun block => block.slots.map Slot.address)).Nodup := by
    simpa [blockEq, NotionCoreSourceDocument.project, NotionCoreInvariant.addresses] using unique
  obtain ⟨semantic, accepted, answer⟩ := NotionCoreSpec.local_delete_document
    (NotionCoreSourceDocument.project pre) (NotionCoreSourceDocument.project post)
    block.id head tail start (stop - start) unique'
  have projected := NotionCoreSourceDocument.project_delete
    (pre ++ block :: post) (deleteTargets block start stop)
  rw [delete_targets_projection, slots] at projected
  have input : NotionCoreSourceDocument.project (pre ++ block :: post) =
      NotionCoreSourceDocument.project pre ++ ⟨block.id, head :: tail⟩ ::
        NotionCoreSourceDocument.project post := by simp [blockEq, NotionCoreSourceDocument.project]
  rw [input, accepted] at projected
  obtain ⟨result, executed, same⟩ := Option.map_eq_some_iff.mp projected
  refine ⟨result, ?_, ?_⟩
  · simpa only [← slots, ← delete_targets_projection] using executed
  · rw [same]
    simpa only [slots, Nat.add_sub_of_le ordered] using answer

/-- The source-selected origin produces the ordinary local split through the
independent command machine. The later physical-model theorem lifts this
message effect; extracting the raw source create/split/move transaction remains
separate from both theorems. -/
theorem source_split_message_effect (pre post : NotionCoreSourceDocument.Document)
    (block : Block) (index bid inst : Nat) (markerId : Nat × Nat)
    (unique : (NotionCoreInvariant.addresses
      (NotionCoreSourceDocument.project (pre ++ block :: post))).Nodup)
    (blocks : ((pre ++ block :: post).map Block.id).Nodup)
    (bound : index ≤ (characters block.active).length)
    (freshBlock : bid ∉ (pre ++ block :: post).map Block.id)
    (freshRoot : (NotionCoreSpec.root inst).address ∉ NotionCoreInvariant.addresses
      (NotionCoreSourceDocument.project (pre ++ block :: post))) :
    ∃ origin result, locate block index = some origin ∧
      NotionCoreSpec.execute (NotionCoreSourceDocument.project (pre ++ block :: post))
        [.create bid inst (some block.id),
          .split origin (NotionCoreSpec.boundary origin.1 markerId) bid] = some result ∧
      NotionCoreSpec.view result =
        NotionCoreSpec.view (NotionCoreSourceDocument.project pre) ++
        [(block.id, (NotionCoreSpec.text block.project.slots).take index),
          (bid, (NotionCoreSpec.text block.project.slots).drop index)] ++
        NotionCoreSpec.view (NotionCoreSourceDocument.project post) := by
  obtain ⟨origin, located⟩ := locate_progress block index bound
  have input : NotionCoreSourceDocument.project (pre ++ block :: post) =
      NotionCoreSourceDocument.project pre ++ block.project ::
        NotionCoreSourceDocument.project post := by simp [NotionCoreSourceDocument.project]
  obtain ⟨result, accepted, answer⟩ := NotionCoreSpec.local_split_client
    (NotionCoreSourceDocument.project pre) (NotionCoreSourceDocument.project post)
    block.project origin index bid inst (NotionCoreSpec.boundary origin.1 markerId)
    (by simpa only [NotionCoreInvariant.addresses, input] using unique)
    (by simpa [NotionCoreSourceDocument.project] using blocks)
    (locate_prepared block index origin located)
    (by simpa [NotionCoreSourceDocument.project] using freshBlock)
    (by simpa only [NotionCoreInvariant.addresses, input] using freshRoot) rfl
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
      exact ⟨NotionCoreSourceDocument.freshBlock bid inst, by simp, rfl, ⟨rfl, rfl, rfl⟩⟩
    | some previous =>
      by_cases present : previous ∈ doc.map Block.id
      · simp only [NotionCoreSourceDocument.step, duplicate, present, ↓reduceIte,
          Option.some.injEq] at accepted
        subst created
        obtain ⟨block, member, same⟩ := List.mem_map.mp present
        exact ⟨NotionCoreSourceDocument.freshBlock bid inst,
          List.mem_flatMap.mpr ⟨block, member, by simp [same]⟩, rfl, ⟨rfl, rfl, rfl⟩⟩
      · simp [NotionCoreSourceDocument.step, duplicate, present] at accepted

/-- An independently legal split lifts to the physical interval transition
when its named destination is an empty source root. This domain lemma inspects
the physical transition; it does not assume that transition succeeds. -/
theorem split_progress {doc : NotionCoreSourceDocument.Document}
    (origin marker : Address) (bid : Nat)
    (safe : NotionCoreSourceDocument.OriginSafe doc origin)
    (unique : (doc.map Block.id).Nodup)
    (empty : ∃ target ∈ doc, target.id = bid ∧ NotionCoreSourceDocument.EmptyRoot target)
    (semantic : ∃ next, NotionCoreSpec.step (NotionCoreSourceDocument.project doc)
      (.split origin ⟨marker, 0, false⟩ bid) = some next) :
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
    have absent := NotionCoreSourceDocument.owner_project doc origin safe
    simp only [owned, Option.map_none] at absent
    simp [NotionCoreSpec.step, absent] at accepted
  | some source =>
    have found := NotionCoreSourceDocument.owner_project doc origin safe
    simp only [owned, Option.map_some] at found
    have different : source.id ≠ bid := by
      intro collision
      simp [NotionCoreSpec.step, found, collision] at accepted
    simp [NotionCoreSourceDocument.step, owned, targetFound, different, emptyRoot]

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
prefix/suffix effect for the source's actual selected origin. The split command
encapsulates marker insertion plus detachment into the fresh root; extracting
that encapsulation from the raw source tree remains a separate obligation. -/
theorem source_split_effect (pre post : NotionCoreSourceDocument.Document)
    (block : Block) (index bid inst : Nat) (markerId : Nat × Nat)
    (unique : (NotionCoreInvariant.addresses
      (NotionCoreSourceDocument.project (pre ++ block :: post))).Nodup)
    (blocks : ((pre ++ block :: post).map Block.id).Nodup)
    (bound : index ≤ (characters block.active).length)
    (freshBlock : bid ∉ (pre ++ block :: post).map Block.id)
    (freshRoot : (NotionCoreSpec.root inst).address ∉ NotionCoreInvariant.addresses
      (NotionCoreSourceDocument.project (pre ++ block :: post))) :
    ∃ origin created result, locate block index = some origin ∧
      NotionCoreSourceDocument.step (pre ++ block :: post)
        (.create bid inst (some block.id)) = some created ∧
      NotionCoreSourceDocument.step created (.split origin (origin.1, .event markerId) bid) = some result ∧
      NotionCoreSpec.view (NotionCoreSourceDocument.project result) =
        NotionCoreSpec.view (NotionCoreSourceDocument.project pre) ++
        [(block.id, (NotionCoreSpec.text block.project.slots).take index),
          (bid, (NotionCoreSpec.text block.project.slots).drop index)] ++
        NotionCoreSpec.view (NotionCoreSourceDocument.project post) := by
  obtain ⟨origin, semanticResult, located, semanticRun, answer⟩ :=
    source_split_message_effect pre post block index bid inst markerId unique blocks bound freshBlock freshRoot
  let before := NotionCoreSourceDocument.project (pre ++ block :: post)
  let middle := NotionCoreSourceDocument.project pre ++ block.project ::
    ⟨bid, [NotionCoreSpec.root inst]⟩ :: NotionCoreSourceDocument.project post
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
    intro projected member
    obtain ⟨old, _, equal⟩ := List.mem_map.mp member
    exact equal ▸ project_anchored old
  have middleWellFormed : NotionCoreSpec.WellFormed middle := by
    apply NotionCoreInvariant.step_preserves oldWellFormed _ semanticCreate
    rw [input]
    exact .create_after _ _ _ bid inst (input ▸ fresh) (input ▸ freshRoot)
  have createdWellFormed : NotionCoreSpec.WellFormed (NotionCoreSourceDocument.project created) :=
    createdProjection ▸ middleWellFormed
  obtain ⟨k, within, selected, _⟩ := locate_active_prepared block index origin located
  have active : origin ∈ block.active.traversal := by
    rw [← NotionCoreSourceDocument.active_addresses]
    exact List.mem_map.mpr ⟨_, List.getElem_mem within, selected⟩
  have oldMember := create_retains_block bid inst (some block.id) block
    (by simp : block ∈ pre ++ block :: post) createdStep
  have safe := NotionCoreSourceGuards.originSafe_of_active createdWellFormed.2.1 oldMember active
  have semanticSplit : NotionCoreSpec.step middle
      (.split origin (NotionCoreSpec.boundary origin.1 markerId) bid) = some semanticResult := by
    have semanticCreate' : NotionCoreSpec.step
        (NotionCoreSourceDocument.project (pre ++ block :: post))
        (.create bid inst (some block.id)) = some middle := semanticCreate
    simpa [NotionCoreSpec.execute, semanticCreate'] using semanticRun
  obtain ⟨result, splitStep⟩ := split_progress origin (origin.1, .event markerId) bid safe
    (by simpa only [NotionCoreSourceDocument.project_ids] using createdWellFormed.1)
    (create_empty_target bid inst (some block.id) createdStep)
    ⟨semanticResult, by simpa only [createdProjection, NotionCoreSpec.boundary] using semanticSplit⟩
  have projectedStep := NotionCoreSourceGuards.step_sound
    (.split origin (origin.1, .event markerId) bid) createdWellFormed splitStep
  change NotionCoreSpec.step (NotionCoreSourceDocument.project created)
    (.split origin (NotionCoreSpec.boundary origin.1 markerId) bid) =
      some (NotionCoreSourceDocument.project result) at projectedStep
  rw [createdProjection, semanticSplit] at projectedStep
  exact ⟨origin, created, result, located, createdStep, splitStep,
    (congrArg NotionCoreSpec.view (Option.some.inj projectedStep)).symm.trans answer⟩

private def attachedExample : Block :=
  ⟨10, .attached 10, ⟨(0, .event (1, 10)),
    [⟨(0, .event (0, 1)), .text 97 true⟩,
     ⟨(0, .event (0, 2)), .text 98 false⟩]⟩⟩

/-- Source zero preparation uses the active split marker, including when all
text is hidden. It does not use the independent helper's empty title root. -/
theorem zero_origin_control :
    locate attachedExample 0 = some (0, .event (1, 10)) ∧
    locate attachedExample 0 ≠ NotionCoreSpec.prepareGap attachedExample.project.slots 0 ∧
    locate {attachedExample with active := ⟨(0, .event (1, 10)),
      [⟨(0, .event (0, 1)), .text 97 true⟩]⟩} 0 = some (0, .event (1, 10)) := by decide

/-- The positive index selects the visible predecessor through tombstones;
the same source branch rejects an oversized insertion index. -/
theorem positive_origin_control :
    locate attachedExample 1 = some (0, .event (0, 2)) ∧
    locate attachedExample 1 ≠ some (0, .event (0, 1)) ∧
    locate attachedExample 2 = none := by decide

theorem range_selection_control :
    deleteTargets attachedExample 0 1 = [(0, .event (0, 2))] ∧
    deleteTargets attachedExample 0 1 ≠ [(0, .event (0, 1))] := by decide

/-- At zero in an attached block, the selected leaf marker transfers every
remaining visible atom. The unused own root must not capture the insertion. -/
theorem physical_split_control :
    let result := do
      let origin ← locate attachedExample 0
      let created ← NotionCoreSourceDocument.step [attachedExample] (.create 11 11 (some 10))
      NotionCoreSourceDocument.step created (.split origin (0, .event (1, 11)) 11)
    result.map (fun doc => NotionCoreSpec.view (NotionCoreSourceDocument.project doc)) =
      some [(10, []), (11, [98])] ∧
    result.map (fun doc => NotionCoreSpec.view (NotionCoreSourceDocument.project doc)) ≠
      some [(10, [98]), (11, [])] := by decide

#print axioms locate_prepared
#print axioms source_insert_effect
#print axioms source_delete_effect
#print axioms source_split_message_effect
#print axioms source_split_effect
end Sal.MRDTs.Instances.NotionCorePreparation
