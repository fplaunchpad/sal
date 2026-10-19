import Sal.MRDTs.Instances.NotionCoreSpecMerge

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
  · intro block member live
    obtain ⟨old, oldmem, equal⟩ := List.mem_map.mp member
    subst block
    exact anchored_erase old targets (h.2.2 old oldmem live)

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
  · intro block member live
    rcases List.mem_append.mp member with member | member
    · exact h.2.2 block (List.mem_append_left _ member) live
    · rcases List.mem_cons.mp member with rfl | member
      · exact anchored_insert source origin fresh (h.2.2 source (by simp) live)
      · exact h.2.2 block (by simp [member]) live

private theorem nodup_insert_middle {α : Type} (pre post : List α) (fresh : α)
    (unique : (pre ++ post).Nodup) (absent : fresh ∉ pre ++ post) :
    (pre ++ fresh :: post).Nodup :=
  List.nodup_middle.mpr (List.nodup_cons.mpr ⟨absent, unique⟩)

theorem create_preserves (pre post : Document) (bid inst : Nat)
    (h : WellFormed (pre ++ post))
    (freshBlock : bid ∉ (pre ++ post).map Block.id)
    (freshRoot : (root inst).address ∉ addresses (pre ++ post))
    (freshFinish : (finishSlot inst).address ∉ addresses (pre ++ post)) :
    WellFormed (pre ++ ⟨bid, inst, [root inst, finishSlot inst], true⟩ :: post) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.map_append, List.map_cons] using
      nodup_insert_middle (pre.map Block.id) (post.map Block.id) bid
        (by simpa only [List.map_append] using h.1)
        (by simpa only [List.map_append] using freshBlock)
  · have finished := nodup_insert_middle (addresses pre) (addresses post) (finishSlot inst).address
      (by simpa only [addresses, List.flatMap_append] using h.2.1)
      (by simpa only [addresses, List.flatMap_append] using freshFinish)
    have outside : (root inst).address ∉ addresses pre ++ addresses post := by
      simpa only [addresses, List.flatMap_append] using freshRoot
    have inserted := nodup_insert_middle (addresses pre)
      ((finishSlot inst).address :: addresses post) (root inst).address finished (by
        simp only [List.mem_append, List.mem_cons, not_or] at outside ⊢
        exact ⟨outside.1, by simp [root, finishSlot], outside.2⟩)
    simpa only [addresses, List.flatMap_append, List.flatMap_cons,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append] using inserted
  · intro block member live
    rcases List.mem_append.mp member with member | member
    · exact h.2.2 block (List.mem_append_left _ member) live
    · rcases List.mem_cons.mp member with rfl | member
      · exact ⟨root inst, [finishSlot inst], rfl, rfl⟩
      · exact h.2.2 block (List.mem_append_right _ member) live

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

/-- Appending a fresh run to a block preserves the structural invariant. -/
theorem append_preserves (pre post : Document) (target : Block) (fresh : List Slot)
    (h : WellFormed (pre ++ target :: post)) (names : FreshRun (pre ++ target :: post) fresh) :
    WellFormed (pre ++ {target with slots := target.slots ++ fresh} :: post) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.map_append, List.map_cons] using h.1
  · have permutation :
        (addresses (pre ++ {target with slots := target.slots ++ fresh} :: post)).Perm
        (addresses (pre ++ target :: post) ++ fresh.map Slot.address) := by
      apply List.perm_iff_count.mpr
      intro x
      simp only [addresses, List.flatMap_append, List.flatMap_cons, List.map_append,
        List.count_append]
      omega
    exact permutation.nodup_iff.mpr (nodup_fresh_append _ _ h names)
  · intro block member live
    rcases List.mem_append.mp member with member | member
    · exact h.2.2 block (List.mem_append_left _ member) live
    · rcases List.mem_cons.mp member with rfl | member
      · obtain ⟨head, tail, eq, hidden⟩ := h.2.2 target (by simp) live
        exact ⟨head, tail ++ fresh, by simp [eq], hidden⟩
      · exact h.2.2 block (by simp [member]) live

/-- Removing a split suffix and closing the remainder with a fresh close slot
preserves the structural invariant. The removed identities and a fresh marker
are then a fresh run relative to the remainder. This is the key ownership
fact; no visible editing law is a premise. -/
theorem trim_preserves_and_fresh (pre post : Document) (source : Block)
    (origin : Address) (marker close : Slot) (h : WellFormed (pre ++ source :: post))
    (freshMarker : marker.address ∉ addresses (pre ++ source :: post))
    (freshClose : close.address ∉ addresses (pre ++ source :: post))
    (distinct : marker.address ≠ close.address) :
    let cut := cutAfter source.slots origin
    let reduced := pre ++ {source with slots := cut.1 ++ [close]} :: post
    WellFormed reduced ∧ FreshRun reduced (marker :: cut.2) := by
  let cut := cutAfter source.slots origin
  let reduced := pre ++ {source with slots := cut.1 ++ [close]} :: post
  have partition : cut.1.map Slot.address ++ cut.2.map Slot.address = source.slots.map Slot.address := by
    dsimp [cut, cutAfter]
    rw [← List.map_append, List.take_append_drop]
  have permutation : (addresses (pre ++ source :: post) ++ [close.address]).Perm
      (addresses reduced ++ cut.2.map Slot.address) := by
    apply List.perm_iff_count.mpr
    intro x
    have counts := congrArg (List.count x) partition
    simp only [List.count_append] at counts
    simp only [addresses, reduced, List.flatMap_append, List.flatMap_cons, List.map_append,
      List.map_cons, List.map_nil, List.count_append]
    omega
  have closed : (addresses (pre ++ source :: post) ++ [close.address]).Nodup :=
    List.nodup_append'.mpr ⟨h.2.1, List.nodup_singleton _,
      List.disjoint_singleton.mpr freshClose⟩
  have names := List.nodup_append'.mp (permutation.nodup_iff.mp closed)
  have freshAll : marker.address ∉ addresses reduced ++ cut.2.map Slot.address := by
    intro collision
    rcases List.mem_append.mp (permutation.mem_iff.mpr collision) with old | new
    · exact freshMarker old
    · exact distinct (List.mem_singleton.mp new)
  have reducedWF : WellFormed reduced := by
    refine ⟨?_, names.1, ?_⟩
    · simpa only [reduced, List.map_append, List.map_cons] using h.1
    · intro block member live
      rcases List.mem_append.mp member with member | member
      · exact h.2.2 block (List.mem_append_left _ member) live
      · rcases List.mem_cons.mp member with rfl | member
        · obtain ⟨head, tail, eq, hidden⟩ := anchored_cut source origin (h.2.2 source (by simp) live)
          refine ⟨head, tail ++ [close], ?_, hidden⟩
          simp only at eq
          simp [cut, eq]
        · exact h.2.2 block (by simp [member]) live
  refine ⟨reducedWF, ?_, ?_⟩
  · exact List.nodup_cons.mpr ⟨fun member => freshAll (List.mem_append_right _ member), names.2.1⟩
  · apply List.disjoint_left.mpr
    intro address member selected
    rcases List.mem_cons.mp selected with rfl | selected
    · exact freshAll (List.mem_append_left _ member)
    · exact List.disjoint_left.mp names.2.2 member selected

/-- Structural split preservation, allowing arbitrary source/target block
positions and hidden origin anchors. The marker and the close slot are fresh;
the close slot ends the kept prefix, and the moved suffix becomes newly owned
by the target after the marker. -/
theorem split_preserves (doc : Document) (source target : Block) (origin : Address)
    (marker close : Slot) (h : WellFormed doc)
    (sourceMember : source ∈ doc) (targetMember : target ∈ doc)
    (distinct : source.id ≠ target.id)
    (freshMarker : marker.address ∉ addresses doc)
    (freshClose : close.address ∉ addresses doc)
    (separate : marker.address ≠ close.address) :
    WellFormed (appendSlots
      (replaceSlots doc source.id ((cutAfter source.slots origin).1 ++ [close]))
      target.id (marker :: (cutAfter source.slots origin).2)) := by
  obtain ⟨pre, post, shape⟩ := List.append_of_mem sourceMember
  subst doc
  let cut := cutAfter source.slots origin
  let reduced := pre ++ {source with slots := cut.1 ++ [close]} :: post
  have preserved := trim_preserves_and_fresh pre post source origin marker close h freshMarker
    freshClose separate
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
  have result := append_preserves left right target (marker :: cut.2)
    (by simpa only [reducedShape] using reducedWF) fresh'
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
      (freshRoot : (root inst).address ∉ addresses doc)
      (freshFinish : (finishSlot inst).address ∉ addresses doc) :
      Admissible doc (.create bid inst none)
  | create_after (pre post : Document) (source : Block) (bid inst : Nat)
      (freshBlock : bid ∉ (pre ++ source :: post).map Block.id)
      (freshRoot : (root inst).address ∉ addresses (pre ++ source :: post))
      (freshFinish : (finishSlot inst).address ∉ addresses (pre ++ source :: post)) :
      Admissible (pre ++ source :: post) (.create bid inst (some source.id))
  | insert (pre post : Document) (source : Block) (origin : Address) (fresh : List Slot)
      (present : origin ∈ source.slots.map Slot.address)
      (names : FreshRun (pre ++ source :: post) fresh) :
      Admissible (pre ++ source :: post) (.insert origin fresh)
  | delete (doc : Document) (targets : List Address) :
      Admissible doc (.delete targets)
  | split (doc : Document) (source target : Block) (origin : Address) (marker : Nat × Nat)
      (inst : Nat)
      (owner : NotionCoreSpec.owner doc origin = some source)
      (targetMember : target ∈ doc)
      (distinct : source.id ≠ target.id)
      (emptyTarget : target.slots = [root inst, finishSlot inst])
      (freshMarker : (boundary origin.1 marker).address ∉ addresses doc)
      (freshClose : (closeSlot origin.1 marker).address ∉ addresses doc) :
      Admissible doc (.split origin marker target.id)
  | merge (doc : Document) (source : Nat) (anchor : Address) :
      Admissible doc (.merge source anchor)

private theorem split_map (doc : Document) (source : Block) (origin : Address)
    (marker close : Slot) (target : Nat) (distinct : source.id ≠ target) :
    (doc.map fun block =>
      if block.id = source.id then {block with slots := (cutAfter source.slots origin).1 ++ [close]}
      else if block.id = target then
        {block with slots := block.slots ++ marker :: (cutAfter source.slots origin).2}
      else block) =
    appendSlots (replaceSlots doc source.id ((cutAfter source.slots origin).1 ++ [close]))
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
  | create_front doc bid inst freshBlock freshRoot freshFinish =>
      simp only [step, freshBlock, ↓reduceIte] at executed
      have equal := Option.some.inj executed
      subst next
      exact create_preserves [] doc bid inst h freshBlock freshRoot freshFinish
  | create_after pre post source bid inst freshBlock freshRoot freshFinish =>
      rw [step_create_focus pre post source bid inst h.1 freshBlock] at executed
      have equal := Option.some.inj executed
      subst next
      simpa only [List.append_assoc, List.singleton_append] using
        create_preserves (pre ++ [source]) post bid inst
        (by simpa only [List.append_assoc, List.singleton_append] using h)
        (by simpa only [List.append_assoc, List.singleton_append] using freshBlock)
        (by simpa only [List.append_assoc, List.singleton_append] using freshRoot)
        (by simpa only [List.append_assoc, List.singleton_append] using freshFinish)
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
  | split doc source target origin marker inst owner targetMember distinct emptyTarget freshMarker freshClose =>
      have sourceMember : source ∈ doc := List.mem_of_find?_eq_some owner
      have targetPresent : target.id ∈ doc.map Block.id := List.mem_map.mpr ⟨target, targetMember, rfl⟩
      have valid : ¬ (source.id = target.id ∨ target.id ∉ doc.map Block.id) := by
        simp [distinct, targetPresent]
      simp only [step, owner, valid, ↓reduceIte] at executed
      rw [split_map doc source origin (boundary origin.1 marker) (closeSlot origin.1 marker)
        target.id distinct] at executed
      have equal := Option.some.inj executed
      subst next
      exact split_preserves doc source target origin _ _ h sourceMember targetMember distinct
        freshMarker freshClose (by simp [boundary, closeSlot])
  | merge doc source anchor => exact NotionCoreSpecMerge.merge_preserves h executed

/-- Structural admission never gets stuck on an invariant document. This is
separate from preservation so a vacuous failed transition cannot discharge it. -/
theorem admissible_progress {doc : Document} {command : Command}
    (h : WellFormed doc) (guard : Admissible doc command) :
    ∃ next, step doc command = some next := by
  cases guard with
  | create_front doc bid inst freshBlock freshRoot freshFinish =>
      simp [step, freshBlock]
  | create_after pre post source bid inst freshBlock freshRoot freshFinish =>
      exact ⟨_, step_create_focus pre post source bid inst h.1 freshBlock⟩
  | insert pre post source origin fresh present names =>
      exact ⟨_, step_insert_focus pre post source origin fresh present
        (address_focus pre post source origin h.2.1 present).2⟩
  | delete doc targets => exact ⟨_, rfl⟩
  | split doc source target origin marker inst owner targetMember distinct emptyTarget freshMarker freshClose =>
      have targetPresent : target.id ∈ doc.map Block.id := List.mem_map.mpr ⟨target, targetMember, rfl⟩
      simp [step, owner, distinct, targetPresent]
  | merge doc source anchor =>
      exact Option.ne_none_iff_exists'.mp (NotionCoreSpecMerge.merge_total doc source anchor)

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

private theorem same_block_id {doc : Document} (unique : (doc.map Block.id).Nodup)
    {a b : Block} (ha : a ∈ doc) (hb : b ∈ doc) (eq : a.id = b.id) : a = b := by
  induction doc with
  | nil => simp at ha
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact False.elim (unique.1 (List.mem_map.mpr ⟨b, hb, eq.symm⟩))
    · exact False.elim (unique.1 (List.mem_map.mpr ⟨a, ha, eq⟩))
    · exact ih unique.2 ha hb

private theorem take_succ_head (head : Slot) (tail : List Slot) (k : Nat) :
    ∃ rest, (head :: tail).take (k + 1) = head :: rest := ⟨tail.take k, rfl⟩

/-- Cutting or inserting after any address keeps the first slot first. -/
theorem cutAfter_head (head : Slot) (tail : List Slot) (origin : Address) :
    ∃ rest, (cutAfter (head :: tail) origin).1 = head :: rest :=
  take_succ_head head tail _

theorem insertSlots_head (head : Slot) (tail fresh : List Slot) (origin : Address) :
    ∃ rest, insertSlots origin fresh (head :: tail) = head :: rest := by
  obtain ⟨rest, eq⟩ := cutAfter_head head tail origin
  refine ⟨rest ++ fresh ++ (cutAfter (head :: tail) origin).2, ?_⟩
  simp only [insertSlots]
  rw [eq]
  rfl

private theorem rooted_cons {block : Block} {doc : Document}
    (head : (block.alive = true → ∃ tail, block.slots = root block.inst :: tail) ∧
      (block.alive = false → block.slots = []))
    (rest : Rooted doc) : Rooted (block :: doc) := by
  intro b member
  rcases List.mem_cons.mp member with rfl | member
  · exact head
  · exact rest b member

private theorem rooted_append {a b : Document} (left : Rooted a) (right : Rooted b) :
    Rooted (a ++ b) := by
  intro block member
  rcases List.mem_append.mp member with member | member
  · exact left block member
  · exact right block member

private theorem rooted_sub {a b : Document} (rooted : Rooted a) (sub : ∀ block ∈ b, block ∈ a) :
    Rooted b := fun block member => rooted block (sub block member)

private theorem fresh_rooted (bid inst : Nat) :
    Rooted [(⟨bid, inst, [root inst, finishSlot inst], true⟩ : Block)] := by
  intro b member
  simp only [List.mem_singleton] at member
  subst member
  exact ⟨fun _ => ⟨[finishSlot inst], rfl⟩, fun dead => by simp at dead⟩

/-- Rewriting an alive rooted block's slots to a list headed by its old first
slot keeps it rooted. -/
private theorem rooted_rehead {block : Block} {slots : List Slot}
    (rooted : Rooted [block]) (live : block.alive = true)
    (headed : ∀ head tail, block.slots = head :: tail → ∃ rest, slots = head :: rest) :
    Rooted [{block with slots := slots}] := by
  intro b member
  simp only [List.mem_singleton] at member
  subst member
  obtain ⟨tail, eq⟩ := (rooted block (by simp)).1 live
  obtain ⟨rest, eq'⟩ := headed _ _ eq
  exact ⟨fun _ => ⟨rest, eq'⟩, fun dead => by simp [live] at dead⟩

private theorem alive_of_owns {block : Block} {origin : Address} (rooted : Rooted [block])
    (present : origin ∈ block.slots.map Slot.address) : block.alive = true := by
  cases live : block.alive
  · have empty := (rooted block (by simp)).2 live
    simp [empty] at present
  · rfl

private theorem eraseSlot_root (targets : List Address) (inst : Nat) :
    eraseSlot targets (root inst) = root inst := by
  simp [eraseSlot, root]

/-- Every admitted step preserves `Rooted`. Split relies on its empty-target
guard: the target's only slot is its own root. -/
theorem step_preserves_rooted {doc next : Document} {command : Command}
    (h : WellFormed doc) (rooted : Rooted doc) (guard : Admissible doc command)
    (executed : step doc command = some next) : Rooted next := by
  cases guard with
  | create_front doc bid inst freshBlock freshRoot freshFinish =>
      simp only [step, freshBlock, ↓reduceIte] at executed
      have equal := Option.some.inj executed
      subst next
      exact rooted_append (fresh_rooted bid inst) rooted
  | create_after pre post source bid inst freshBlock freshRoot freshFinish =>
      rw [step_create_focus pre post source bid inst h.1 freshBlock] at executed
      have equal := Option.some.inj executed
      subst next
      refine rooted_append (rooted_sub rooted (fun b hb => by simp [hb])) ?_
      refine rooted_cons (rooted source (by simp)) ?_
      exact rooted_append (fresh_rooted bid inst) (rooted_sub rooted (fun b hb => by simp [hb]))
  | insert pre post source origin fresh present names =>
      have outside := (address_focus pre post source origin h.2.1 present).2
      rw [step_insert_focus pre post source origin fresh present outside] at executed
      have equal := Option.some.inj executed
      subst next
      have single : Rooted [source] := rooted_sub rooted (fun b hb => by simp_all)
      refine rooted_append (rooted_sub rooted (fun b hb => by simp [hb])) ?_
      refine rooted_append (rooted_rehead single (alive_of_owns single present) ?_)
        (rooted_sub rooted (fun b hb => by simp [hb]))
      intro head tail eq
      rw [eq]
      exact insertSlots_head head tail fresh origin
  | delete doc targets =>
      simp only [step] at executed
      have equal := Option.some.inj executed
      subst next
      intro block member
      obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
      obtain ⟨live, dead⟩ := rooted old oldMember
      refine ⟨fun alive => ?_, fun gone => ?_⟩
      · obtain ⟨tail, eq⟩ := live alive
        exact ⟨tail.map (eraseSlot targets), by simp [eq, eraseSlot_root]⟩
      · simp [dead gone]
  | split doc source target origin marker inst owner targetMember distinct emptyTarget freshMarker freshClose =>
      have sourceMember : source ∈ doc := List.mem_of_find?_eq_some owner
      have targetPresent : target.id ∈ doc.map Block.id := List.mem_map.mpr ⟨target, targetMember, rfl⟩
      have valid : ¬ (source.id = target.id ∨ target.id ∉ doc.map Block.id) := by
        simp [distinct, targetPresent]
      simp only [step, owner, valid, ↓reduceIte] at executed
      have equal := Option.some.inj executed
      subst next
      have present : origin ∈ source.slots.map Slot.address := by
        have found := List.find?_some owner
        simpa [NotionCoreSpec.owns] using found
      have sourceSingle : Rooted [source] := rooted_sub rooted (fun b hb => by simp_all)
      have sourceLive := alive_of_owns sourceSingle present
      have targetLive : target.alive = true := by
        cases live : target.alive
        · have empty := (rooted target targetMember).2 live
          rw [emptyTarget] at empty
          simp at empty
        · rfl
      have targetRoot : root inst = root target.inst := by
        obtain ⟨tail, eq⟩ := (rooted target targetMember).1 targetLive
        rw [emptyTarget] at eq
        exact (List.cons.inj eq).1
      intro block member
      obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
      by_cases isSource : old.id = source.id
      · have same := same_block_id h.1 oldMember sourceMember isSource
        subst old
        simp only [↓reduceIte]
        refine ⟨fun _ => ?_, fun dead => by simp [sourceLive] at dead⟩
        obtain ⟨tail, eq⟩ := (rooted source sourceMember).1 sourceLive
        rw [eq]
        obtain ⟨rest, cut⟩ := cutAfter_head (root source.inst) tail origin
        exact ⟨rest ++ [closeSlot origin.1 marker], by rw [cut]; rfl⟩
      · by_cases isTarget : old.id = target.id
        · have same := same_block_id h.1 oldMember targetMember isTarget
          subst old
          simp only [isSource, ↓reduceIte]
          refine ⟨fun _ => ⟨finishSlot inst :: boundary origin.1 marker ::
              (cutAfter source.slots origin).2, ?_⟩,
            fun dead => by simp [targetLive] at dead⟩
          simp [emptyTarget, targetRoot]
        · simp only [isSource, isTarget, ↓reduceIte]
          exact rooted old oldMember
  | merge doc source anchor =>
      exact NotionCoreSpecMerge.merge_preserves_rooted h.1 rooted executed

theorem reachable_rooted {doc : Document} (reachable : Reach doc) : Rooted doc := by
  induction reachable with
  | init => intro block member; simp at member
  | step prior guard executed ih =>
      exact step_preserves_rooted (reachable_wellFormed prior) ih guard executed

private def slotA : Slot := character 0 (0, 1) 0
private def slotB : Slot := character 0 (0, 2) 1
private def oldBlock : Block := ⟨10, 0, [root 0, slotA, slotB, finishSlot 0], true⟩
private def deletedBlock : Block :=
  ⟨10, 0, [root 0, {slotA with visible := false}, slotB, finishSlot 0], true⟩
private def targetBlock : Block := ⟨11, 1, [root 1, finishSlot 1], true⟩
private def afterSplit : Document :=
  [⟨10, 0, [root 0, {slotA with visible := false}, closeSlot 0 (1, 10)], true⟩,
   ⟨11, 1, [root 1, finishSlot 1, boundary 0 (1, 10), slotB, finishSlot 0], true⟩]

/-- PASS+FAIL: a nontrivial admitted execution deletes a, then splits after
its hidden identity. The split moves b, not the visible prefix, into the new
block. This also rules out a live-origin-only reading of admission. -/
theorem hidden_origin_control :
    Reach afterSplit ∧ view afterSplit = [(10, []), (11, [1])] ∧
    view afterSplit ≠ [(10, [1]), (11, [])] := by
  have one : Reach [⟨10, 0, [root 0, finishSlot 0], true⟩] :=
    .step .init (.create_front [] 10 0 (by decide) (by decide) (by decide)) (by decide)
  have two : Reach [oldBlock] :=
    .step one (.insert [] [] ⟨10, 0, [root 0, finishSlot 0], true⟩ (root 0).address [slotA, slotB]
      (by decide) (by decide)) (by decide)
  have three : Reach [deletedBlock] :=
    .step two (.delete [oldBlock] [slotA.address]) (by decide)
  have four : Reach [deletedBlock, targetBlock] :=
    .step three (.create_after [] [] deletedBlock 11 1 (by decide) (by decide) (by decide))
      (by decide)
  have five : Reach afterSplit :=
    .step four (.split [deletedBlock, targetBlock] deletedBlock targetBlock slotA.address (1, 10) 1
      (by decide) (by simp) (by decide) rfl (by decide) (by decide)) (by decide)
  exact ⟨five, by decide, by decide⟩

/-- Fresh character names are accepted; reusing the existing root name is
rejected by structural freshness even though its value is invisible. -/
theorem freshness_control :
    FreshRun [⟨10, 0, [root 0], true⟩] [slotA, slotB] ∧
    ¬ FreshRun [⟨10, 0, [root 0], true⟩] [root 0] := by decide

#print axioms admissible_progress
#print axioms step_preserves
#print axioms reachable_wellFormed
#print axioms step_preserves_rooted
#print axioms reachable_rooted

end Sal.MRDTs.Instances.NotionCoreInvariant
