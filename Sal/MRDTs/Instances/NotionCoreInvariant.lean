import Sal.MRDTs.Instances.NotionCoreSpec

/-! Structural semantic issuance and invariant preservation for the independent
core. Guards describe names, anchors and shape; none assumes a visible effect.
Deriving these guards for the pinned JavaScript issuer is a separate obligation.
-/
namespace Sal.MRDTs.Instances.NotionCoreInvariant
open NotionCoreSpec

abbrev addresses (doc : Document) : List Address :=
  doc.flatMap (fun block => block.slots.map Slot.address)

def FreshRun (doc : Document) (fresh : List Slot) : Prop :=
  (fresh.map Slot.address).Nodup ∧ List.Disjoint (addresses doc) (fresh.map Slot.address)

instance (doc : Document) (fresh : List Slot) : Decidable (FreshRun doc fresh) :=
  decidable_of_iff ((fresh.map Slot.address).Nodup ∧
    ∀ address ∈ addresses doc, address ∉ fresh.map Slot.address)
    (by simp only [FreshRun, List.disjoint_left])

private theorem append_permutation {α : Type} [DecidableEq α]
    (a b c : List α) : (a ++ b ++ c).Perm ((a ++ c) ++ b) := by
  apply List.perm_iff_count.mpr
  intro x
  simp only [List.count_append]
  omega

private theorem map_identity {α : Type} (f : α → α) (xs : List α)
    (unchanged : ∀ x ∈ xs, f x = x) : xs.map f = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.map_cons, unchanged x (by simp), ih (fun y hy => unchanged y (by simp [hy]))]

@[simp] theorem erase_address (targets : List Address) (slot : Slot) :
    (eraseSlot targets slot).address = slot.address := rfl

theorem anchored_erase (block : Block) (targets : List Address) (h : Anchored block) :
    Anchored {block with slots := block.slots.map (eraseSlot targets)} := by
  obtain ⟨head, tail, eq, hidden⟩ := h
  exact ⟨eraseSlot targets head, tail.map (eraseSlot targets), by simp [eq],
    by simp [eraseSlot, hidden]⟩

theorem delete_preserves (doc : Document) (targets : List Address) (h : WellFormed doc) :
    WellFormed (doc.map fun block => {block with slots := block.slots.map (eraseSlot targets)}) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.map_map, Function.comp_def] using h.1
  · simpa only [List.flatMap_map, List.map_map, Function.comp_def, erase_address] using h.2.1
  · intro block member
    obtain ⟨old, oldmem, equal⟩ := List.mem_map.mp member
    subst block
    exact anchored_erase old targets (h.2.2 old oldmem)

theorem anchored_insert (block : Block) (origin : Address) (fresh : List Slot)
    (h : Anchored block) : Anchored {block with slots := insertSlots origin fresh block.slots} := by
  obtain ⟨head, tail, eq, hidden⟩ := h
  let n := ((head :: tail).map Slot.address).idxOf origin
  refine ⟨head, tail.take n ++ fresh ++ tail.drop n, ?_, hidden⟩
  simp [eq, insertSlots, cutAfter, n, List.append_assoc]

private theorem nodup_fresh_append (doc : Document) (fresh : List Slot)
    (h : WellFormed doc) (names : FreshRun doc fresh) :
    (addresses doc ++ fresh.map Slot.address).Nodup :=
  List.nodup_append'.mpr ⟨h.2.1, names.1, names.2⟩

theorem insert_preserves (pre post : Document) (source : Block) (origin : Address)
    (fresh : List Slot) (h : WellFormed (pre ++ source :: post))
    (names : FreshRun (pre ++ source :: post) fresh) :
    WellFormed (pre ++ {source with slots := insertSlots origin fresh source.slots} :: post) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.map_append, List.map_cons] using h.1
  · have permutation :
        (addresses (pre ++ {source with slots := insertSlots origin fresh source.slots} :: post)).Perm
        (addresses (pre ++ source :: post) ++ fresh.map Slot.address) := by
      apply List.perm_iff_count.mpr
      intro x
      have partition :
          ((cutAfter source.slots origin).1.map Slot.address) ++
            ((cutAfter source.slots origin).2.map Slot.address) = source.slots.map Slot.address := by
        simp only [cutAfter]
        rw [← List.map_append, List.take_append_drop]
      have counts := congrArg (List.count x) partition
      simp only [List.count_append] at counts
      simp only [addresses, List.flatMap_append, List.flatMap_cons, insertSlots,
        List.map_append, List.count_append]
      omega
    exact permutation.nodup_iff.mpr (nodup_fresh_append _ _ h names)
  · intro block member
    rcases List.mem_append.mp member with member | member
    · exact h.2.2 block (List.mem_append_left _ member)
    · rcases List.mem_cons.mp member with rfl | member
      · exact anchored_insert source origin fresh (h.2.2 source (by simp))
      · exact h.2.2 block (by simp [member])

private theorem nodup_insert_middle {α : Type} (pre post : List α) (fresh : α)
    (unique : (pre ++ post).Nodup) (absent : fresh ∉ pre ++ post) :
    (pre ++ fresh :: post).Nodup :=
  List.nodup_middle.mpr (List.nodup_cons.mpr ⟨absent, unique⟩)

theorem create_preserves (pre post : Document) (bid inst : Nat)
    (h : WellFormed (pre ++ post))
    (freshBlock : bid ∉ (pre ++ post).map Block.id)
    (freshRoot : (root inst).address ∉ addresses (pre ++ post)) :
    WellFormed (pre ++ ⟨bid, [root inst]⟩ :: post) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.map_append, List.map_cons] using
      nodup_insert_middle (pre.map Block.id) (post.map Block.id) bid
        (by simpa only [List.map_append] using h.1)
        (by simpa only [List.map_append] using freshBlock)
  · simpa only [addresses, List.flatMap_append, List.flatMap_cons,
      List.map_cons, List.map_nil, List.singleton_append] using
      nodup_insert_middle (addresses pre) (addresses post) (root inst).address
        (by simpa only [addresses, List.flatMap_append] using h.2.1)
        (by simpa only [addresses, List.flatMap_append] using freshRoot)
  · intro block member
    rcases List.mem_append.mp member with member | member
    · exact h.2.2 block (List.mem_append_left _ member)
    · rcases List.mem_cons.mp member with rfl | member
      · exact ⟨root inst, [], rfl, rfl⟩
      · exact h.2.2 block (List.mem_append_right _ member)

def replaceSlots (doc : Document) (bid : Nat) (slots : List Slot) : Document :=
  doc.map fun block => if block.id = bid then {block with slots := slots} else block

def appendSlots (doc : Document) (bid : Nat) (fresh : List Slot) : Document :=
  doc.map fun block => if block.id = bid then {block with slots := block.slots ++ fresh} else block

private theorem id_ne_outside (pre post : Document) (source : Block)
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

theorem replace_focus (pre post : Document) (source : Block) (slots : List Slot)
    (unique : ((pre ++ source :: post).map Block.id).Nodup) :
    replaceSlots (pre ++ source :: post) source.id slots =
      pre ++ {source with slots := slots} :: post := by
  have unchanged : ∀ b ∈ pre ++ post,
      (if b.id = source.id then {b with slots := slots} else b) = b := by
    intro b hb
    simp [id_ne_outside pre post source unique b hb]
  simp only [replaceSlots, List.map_append, List.map_cons]
  rw [map_identity _ pre (fun b hb => unchanged b (List.mem_append_left _ hb)),
    map_identity _ post (fun b hb => unchanged b (List.mem_append_right _ hb))]
  simp

theorem append_focus (pre post : Document) (source : Block) (fresh : List Slot)
    (unique : ((pre ++ source :: post).map Block.id).Nodup) :
    appendSlots (pre ++ source :: post) source.id fresh =
      pre ++ {source with slots := source.slots ++ fresh} :: post := by
  have unchanged : ∀ b ∈ pre ++ post,
      (if b.id = source.id then {b with slots := b.slots ++ fresh} else b) = b := by
    intro b hb
    simp [id_ne_outside pre post source unique b hb]
  simp only [appendSlots, List.map_append, List.map_cons]
  rw [map_identity _ pre (fun b hb => unchanged b (List.mem_append_left _ hb)),
    map_identity _ post (fun b hb => unchanged b (List.mem_append_right _ hb))]
  simp

theorem anchored_cut (source : Block) (origin : Address) (h : Anchored source) :
    Anchored {source with slots := (cutAfter source.slots origin).1} := by
  obtain ⟨head, tail, eq, hidden⟩ := h
  refine ⟨head, tail.take (((head :: tail).map Slot.address).idxOf origin), ?_, hidden⟩
  simp [cutAfter, eq]

/-- Removing a split suffix preserves the old structural invariant. The removed
identities and a fresh marker are then a fresh run relative to the remainder.
This is the key ownership fact; no visible editing law is a premise. -/
theorem trim_preserves_and_fresh (pre post : Document) (source : Block)
    (origin : Address) (marker : Slot) (h : WellFormed (pre ++ source :: post))
    (freshMarker : marker.address ∉ addresses (pre ++ source :: post)) :
    let cut := cutAfter source.slots origin
    let reduced := pre ++ {source with slots := cut.1} :: post
    WellFormed reduced ∧ FreshRun reduced (marker :: cut.2) := by
  let cut := cutAfter source.slots origin
  let reduced := pre ++ {source with slots := cut.1} :: post
  have partition : cut.1.map Slot.address ++ cut.2.map Slot.address = source.slots.map Slot.address := by
    dsimp [cut, cutAfter]
    rw [← List.map_append, List.take_append_drop]
  have permutation : (addresses (pre ++ source :: post)).Perm
      (addresses reduced ++ cut.2.map Slot.address) := by
    apply List.perm_iff_count.mpr
    intro x
    have counts := congrArg (List.count x) partition
    simp only [List.count_append] at counts
    simp only [addresses, reduced, List.flatMap_append, List.flatMap_cons, List.count_append]
    omega
  have names := List.nodup_append'.mp (permutation.nodup_iff.mp h.2.1)
  have freshAll : marker.address ∉ addresses reduced ++ cut.2.map Slot.address := by
    intro collision
    exact freshMarker (permutation.mem_iff.mpr collision)
  have reducedWF : WellFormed reduced := by
    refine ⟨?_, names.1, ?_⟩
    · simpa only [reduced, List.map_append, List.map_cons] using h.1
    · intro block member
      rcases List.mem_append.mp member with member | member
      · exact h.2.2 block (List.mem_append_left _ member)
      · rcases List.mem_cons.mp member with rfl | member
        · exact anchored_cut source origin (h.2.2 source (by simp))
        · exact h.2.2 block (by simp [member])
  refine ⟨reducedWF, ?_, ?_⟩
  · exact List.nodup_cons.mpr ⟨fun member => freshAll (List.mem_append_right _ member), names.2.1⟩
  · apply List.disjoint_left.mpr
    intro address member selected
    rcases List.mem_cons.mp selected with rfl | selected
    · exact freshAll (List.mem_append_left _ member)
    · exact List.disjoint_left.mp names.2.2 member selected

/-- Structural split preservation, allowing arbitrary source/target block
positions and hidden origin anchors. The target is an allocated empty title
root. The marker is fresh, and the moved suffix becomes newly owned there. -/
theorem split_preserves (doc : Document) (source target : Block) (origin : Address)
    (marker : Slot) (inst : Nat) (h : WellFormed doc)
    (sourceMember : source ∈ doc) (targetMember : target ∈ doc)
    (distinct : source.id ≠ target.id) (emptyTarget : target.slots = [root inst])
    (freshMarker : marker.address ∉ addresses doc) :
    WellFormed (appendSlots
      (replaceSlots doc source.id (cutAfter source.slots origin).1)
      target.id (marker :: (cutAfter source.slots origin).2)) := by
  obtain ⟨pre, post, shape⟩ := List.append_of_mem sourceMember
  subst doc
  let cut := cutAfter source.slots origin
  let reduced := pre ++ {source with slots := cut.1} :: post
  have preserved := trim_preserves_and_fresh pre post source origin marker h freshMarker
  have reducedWF : WellFormed reduced := preserved.1
  have fresh : FreshRun reduced (marker :: cut.2) := preserved.2
  have targetOutside : target ∈ pre ++ post := by
    rcases List.mem_append.mp targetMember with member | member
    · exact List.mem_append_left _ member
    · rcases List.mem_cons.mp member with equal | member
      · exact False.elim (distinct (congrArg Block.id equal.symm))
      · exact List.mem_append_right _ member
  have targetReduced : target ∈ reduced := by
    rcases List.mem_append.mp targetOutside with member | member
    · exact List.mem_append_left _ member
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ member)
  obtain ⟨left, right, reducedShape⟩ := List.append_of_mem targetReduced
  have fresh' : FreshRun (left ++ target :: right) (marker :: cut.2) := by simpa only [reducedShape] using fresh
  have result := insert_preserves left right target (root inst).address (marker :: cut.2)
    (by simpa only [reducedShape] using reducedWF) fresh'
  have insertion : insertSlots (root inst).address (marker :: cut.2) target.slots =
      target.slots ++ marker :: cut.2 := by simp [emptyTarget, insertSlots, cutAfter]
  rw [insertion] at result
  rw [replace_focus pre post source _ h.1]
  change WellFormed (appendSlots reduced target.id (marker :: cut.2))
  rw [reducedShape, append_focus left right target _ (by simpa only [reducedShape] using reducedWF.1)]
  exact result

/-- Semantic issuance checks. They describe fresh names, known owners, and the
source's freshly created empty split destination. Hidden origins are allowed.
`create_after` and `insert` carry a location decomposition, equivalent to
membership in an invariant document; neither carries an output state. -/
inductive Admissible : Document → Command → Prop where
  | create_front (doc : Document) (bid inst : Nat)
      (freshBlock : bid ∉ doc.map Block.id)
      (freshRoot : (root inst).address ∉ addresses doc) :
      Admissible doc (.create bid inst none)
  | create_after (pre post : Document) (source : Block) (bid inst : Nat)
      (freshBlock : bid ∉ (pre ++ source :: post).map Block.id)
      (freshRoot : (root inst).address ∉ addresses (pre ++ source :: post)) :
      Admissible (pre ++ source :: post) (.create bid inst (some source.id))
  | insert (pre post : Document) (source : Block) (origin : Address) (fresh : List Slot)
      (present : origin ∈ source.slots.map Slot.address)
      (names : FreshRun (pre ++ source :: post) fresh) :
      Admissible (pre ++ source :: post) (.insert origin fresh)
  | delete (doc : Document) (targets : List Address) :
      Admissible doc (.delete targets)
  | split (doc : Document) (source target : Block) (origin : Address) (marker : Slot) (inst : Nat)
      (owner : NotionCoreSpec.owner doc origin = some source)
      (targetMember : target ∈ doc)
      (distinct : source.id ≠ target.id)
      (emptyTarget : target.slots = [root inst])
      (freshMarker : marker.address ∉ addresses doc)
      (hiddenMarker : marker.visible = false)
      (sameInstance : marker.address.1 = origin.1) :
      Admissible doc (.split origin marker target.id)

private theorem split_map (doc : Document) (source : Block) (origin : Address)
    (marker : Slot) (target : Nat) (distinct : source.id ≠ target) :
    (doc.map fun block =>
      if block.id = source.id then {block with slots := (cutAfter source.slots origin).1}
      else if block.id = target then
        {block with slots := block.slots ++ marker :: (cutAfter source.slots origin).2}
      else block) =
    appendSlots (replaceSlots doc source.id (cutAfter source.slots origin).1)
      target (marker :: (cutAfter source.slots origin).2) := by
  simp only [appendSlots, replaceSlots, List.map_map]
  apply List.map_congr_left
  intro block _
  by_cases hs : block.id = source.id
  · simp [hs, distinct]
  · by_cases ht : block.id = target <;> simp [hs, ht, distinct.symm]

/-- Every successful structurally admitted semantic step preserves the actual
`WellFormed` predicate. No output invariant appears in `Admissible`. -/
theorem step_preserves {doc next : Document} {command : Command}
    (h : WellFormed doc) (guard : Admissible doc command)
    (executed : step doc command = some next) : WellFormed next := by
  cases guard with
  | create_front doc bid inst freshBlock freshRoot =>
      simp only [step, freshBlock, ↓reduceIte] at executed
      have equal := Option.some.inj executed
      subst next
      exact create_preserves [] doc bid inst h freshBlock freshRoot
  | create_after pre post source bid inst freshBlock freshRoot =>
      rw [step_create_focus pre post source bid inst h.1 freshBlock] at executed
      have equal := Option.some.inj executed
      subst next
      simpa only [List.append_assoc, List.singleton_append] using
        create_preserves (pre ++ [source]) post bid inst
        (by simpa only [List.append_assoc, List.singleton_append] using h)
        (by simpa only [List.append_assoc, List.singleton_append] using freshBlock)
        (by simpa only [List.append_assoc, List.singleton_append] using freshRoot)
  | insert pre post source origin fresh present names =>
      have outside := (address_focus pre post source origin h.2.1 present).2
      rw [step_insert_focus pre post source origin fresh present outside] at executed
      have equal := Option.some.inj executed
      subst next
      exact insert_preserves pre post source origin fresh h names
  | delete doc targets =>
      simp only [step] at executed
      have equal := Option.some.inj executed
      subst next
      exact delete_preserves doc targets h
  | split doc source target origin marker inst owner targetMember distinct emptyTarget freshMarker hiddenMarker sameInstance =>
      have sourceMember : source ∈ doc := List.mem_of_find?_eq_some owner
      have targetPresent : target.id ∈ doc.map Block.id := List.mem_map.mpr ⟨target, targetMember, rfl⟩
      have valid : ¬ (source.id = target.id ∨ target.id ∉ doc.map Block.id ∨ marker.visible = true) := by
        simp [distinct, targetPresent, hiddenMarker]
      simp only [step, owner, valid, ↓reduceIte] at executed
      rw [split_map doc source origin marker target.id distinct] at executed
      have equal := Option.some.inj executed
      subst next
      exact split_preserves doc source target origin marker inst h sourceMember targetMember distinct emptyTarget freshMarker

/-- Structural admission never gets stuck on an invariant document. This is
separate from preservation so a vacuous failed transition cannot discharge it. -/
theorem admissible_progress {doc : Document} {command : Command}
    (h : WellFormed doc) (guard : Admissible doc command) :
    ∃ next, step doc command = some next := by
  cases guard with
  | create_front doc bid inst freshBlock freshRoot =>
      simp [step, freshBlock]
  | create_after pre post source bid inst freshBlock freshRoot =>
      exact ⟨_, step_create_focus pre post source bid inst h.1 freshBlock⟩
  | insert pre post source origin fresh present names =>
      exact ⟨_, step_insert_focus pre post source origin fresh present
        (address_focus pre post source origin h.2.1 present).2⟩
  | delete doc targets => exact ⟨_, rfl⟩
  | split doc source target origin marker inst owner targetMember distinct emptyTarget freshMarker hiddenMarker sameInstance =>
      have targetPresent : target.id ∈ doc.map Block.id := List.mem_map.mpr ⟨target, targetMember, rfl⟩
      simp [step, owner, distinct, targetPresent, hiddenMarker]

/-- Reachability uses actual successful command execution and the structural
issuance checks above. It does not assume `WellFormed` as a transition guard. -/
inductive Reach : Document → Prop where
  | init : Reach []
  | step {doc next : Document} {command : Command} : Reach doc →
      Admissible doc command → NotionCoreSpec.step doc command = some next → Reach next

theorem reachable_wellFormed {doc : Document} (reachable : Reach doc) : WellFormed doc := by
  induction reachable with
  | init => exact ⟨by simp, by simp, by simp⟩
  | step _ guard executed ih => exact step_preserves ih guard executed

private def slotA : Slot := character 0 (0, 1) 0
private def slotB : Slot := character 0 (0, 2) 1
private def oldBlock : Block := ⟨10, [root 0, slotA, slotB]⟩
private def deletedBlock : Block := ⟨10, [root 0, {slotA with visible := false}, slotB]⟩
private def targetBlock : Block := ⟨11, [root 1]⟩
private def marker : Slot := boundary 0 (1, 10)
private def afterSplit : Document :=
  [⟨10, [root 0, {slotA with visible := false}]⟩,
   ⟨11, [root 1, marker, slotB]⟩]

/-- PASS+FAIL: a nontrivial admitted execution deletes a, then splits after
its hidden identity. The split moves b, not the visible prefix, into the new
block. This also rules out a live-origin-only reading of admission. -/
theorem hidden_origin_control :
    Reach afterSplit ∧ view afterSplit = [(10, []), (11, [1])] ∧
    view afterSplit ≠ [(10, [1]), (11, [])] := by
  have one : Reach [⟨10, [root 0]⟩] :=
    .step .init (.create_front [] 10 0 (by decide) (by decide)) (by decide)
  have two : Reach [oldBlock] :=
    .step one (.insert [] [] ⟨10, [root 0]⟩ (root 0).address [slotA, slotB]
      (by decide) (by decide)) (by decide)
  have three : Reach [deletedBlock] :=
    .step two (.delete [oldBlock] [slotA.address]) (by decide)
  have four : Reach [deletedBlock, targetBlock] :=
    .step three (.create_after [] [] deletedBlock 11 1 (by decide) (by decide)) (by decide)
  have five : Reach afterSplit :=
    .step four (.split [deletedBlock, targetBlock] deletedBlock targetBlock slotA.address marker 1
      (by decide) (by simp) (by decide) rfl (by decide) rfl rfl) (by decide)
  exact ⟨five, by decide, by decide⟩

/-- Fresh character names are accepted; reusing the existing root name is
rejected by structural freshness even though its value is invisible. -/
theorem freshness_control :
    FreshRun [⟨10, [root 0]⟩] [slotA, slotB] ∧
    ¬ FreshRun [⟨10, [root 0]⟩] [root 0] := by decide

#print axioms admissible_progress
#print axioms step_preserves
#print axioms reachable_wellFormed

end Sal.MRDTs.Instances.NotionCoreInvariant
