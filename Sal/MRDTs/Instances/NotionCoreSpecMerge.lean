import Sal.MRDTs.Instances.NotionCoreSpec

/-! The block merge command of the independent sequential specification. A
merge appends the source's slots to the holder of the target's root slot, so a
merge into a block that was itself merged away lands in the block that
absorbed it. This file gives the no-op cases, the effect when the target is
alive and when it has been absorbed, the cycle case, placement of creations
after tombstones, conservation of visible characters and slot addresses, and
preservation of `WellFormed` and `Rooted`. -/
namespace Sal.MRDTs.Instances.NotionCoreSpecMerge
open NotionCoreSpec

/-- The block transformation applied by an effective merge: the holder is
extended with the source's slots and the source becomes a tombstone. -/
def absorb (holder : Nat) (src : Block) (block : Block) : Block :=
  if block.id = holder then {block with slots := block.slots ++ src.slots}
  else if block.id = src.id then {block with slots := [], alive := false}
  else block

/-- The flattened visible text of the alive blocks in document order. -/
def flatText (doc : Document) : List Nat :=
  (doc.filter Block.alive).flatMap fun b => text b.slots

/-- The flattened slot addresses of all blocks, tombstones included, in
document order. -/
def flatAddresses (doc : Document) : List Address :=
  doc.flatMap fun b => b.slots.map Slot.address

theorem findBlock_none {doc : Document} {bid : Nat} :
    findBlock doc bid = none ↔ bid ∉ doc.map Block.id := by
  simp [findBlock, List.find?_eq_none]

theorem findBlock_some {doc : Document} {bid : Nat} {block : Block}
    (found : findBlock doc bid = some block) : block ∈ doc ∧ block.id = bid :=
  ⟨List.mem_of_find?_eq_some found, by simpa using List.find?_some found⟩

/-- With unique block names, a member block is the one found under its name. -/
theorem findBlock_of_mem {doc : Document} {block : Block}
    (blocks : (doc.map Block.id).Nodup) (member : block ∈ doc) :
    findBlock doc block.id = some block := by
  cases found : findBlock doc block.id with
  | none =>
      exact absurd (List.mem_map.mpr ⟨block, member, rfl⟩) (findBlock_none.mp found)
  | some other =>
      obtain ⟨otherMem, otherId⟩ := findBlock_some found
      rw [List.inj_on_of_nodup_map blocks otherMem member otherId]

theorem owner_some {doc : Document} {origin : Address} {block : Block}
    (found : owner doc origin = some block) :
    block ∈ doc ∧ origin ∈ block.slots.map Slot.address :=
  ⟨List.mem_of_find?_eq_some found, by simpa [owns] using List.find?_some found⟩

/-- With unique slot addresses, the block containing an address is its owner. -/
theorem owner_of_mem {doc : Document} {block : Block} {origin : Address}
    (unique : (flatAddresses doc).Nodup) (member : block ∈ doc)
    (present : origin ∈ block.slots.map Slot.address) :
    owner doc origin = some block := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem member
  have separated := (address_focus pre post block origin unique present).2
  exact owner_focus pre post block origin present
    (fun b hb => separated b (List.mem_append_left _ hb))

/-- On a rooted document every block holding a slot is alive. -/
theorem rooted_holder_alive {doc : Document} {block : Block} (rooted : Rooted doc)
    (member : block ∈ doc) (nonempty : block.slots ≠ []) : block.alive = true := by
  cases live : block.alive with
  | true => rfl
  | false => exact absurd ((rooted block member).2 live) nonempty

/-- On a well-formed rooted document an alive block is the holder of its own
root slot. -/
theorem rooted_owner {doc : Document} {block : Block}
    (h : WellFormed doc) (rooted : Rooted doc)
    (member : block ∈ doc) (live : block.alive = true) :
    owner doc (root block.inst).address = some block := by
  obtain ⟨tail, eq⟩ := (rooted block member).1 live
  exact owner_of_mem h.2.1 member (by simp [eq])

private theorem slots_nonempty {block : Block} {origin : Address}
    (present : origin ∈ block.slots.map Slot.address) : block.slots ≠ [] := by
  intro empty
  simp [empty] at present

/-- Merging an absent source or into an absent target leaves the document
unchanged. -/
theorem merge_absent_noop (doc : Document) (source target : Nat)
    (absent : source ∉ doc.map Block.id ∨ target ∉ doc.map Block.id) :
    step doc (.merge source target) = some doc := by
  rcases absent with absent | absent
  · simp [step, findBlock_none.mpr absent]
  · cases found : findBlock doc source <;> simp [step, found, findBlock_none.mpr absent]

/-- Merge never fails. -/
theorem merge_total (doc : Document) (source target : Nat) :
    step doc (.merge source target) ≠ none := by
  simp only [step]
  split
  · split
    · split <;> simp
    · simp
  · simp

/-- Every merge result is the unchanged document or the absorption of a
present alive source into a holder distinct from it. -/
theorem merge_cases {doc next : Document} {source target : Nat}
    (executed : step doc (.merge source target) = some next) :
    next = doc ∨ ∃ src tgt hold : Block,
      findBlock doc source = some src ∧ findBlock doc target = some tgt ∧
      owner doc (root tgt.inst).address = some hold ∧
      src.alive = true ∧ hold.id ≠ source ∧ next = doc.map (absorb hold.id src) := by
  cases fs : findBlock doc source with
  | none =>
      simp only [step, fs] at executed
      exact Or.inl (Option.some.inj executed).symm
  | some src =>
      cases ft : findBlock doc target with
      | none =>
          simp only [step, fs, ft] at executed
          exact Or.inl (Option.some.inj executed).symm
      | some tgt =>
          cases fo : owner doc (root tgt.inst).address with
          | none =>
              simp only [step, fs, ft, fo] at executed
              exact Or.inl (Option.some.inj executed).symm
          | some hold =>
              obtain ⟨-, rfl⟩ := findBlock_some fs
              simp only [step, fs, ft, fo] at executed
              by_cases valid : src.alive = true ∧ hold.id ≠ src.id
              · rw [if_pos valid] at executed
                exact Or.inr ⟨src, tgt, hold, rfl, rfl, fo, valid.1, valid.2,
                  (Option.some.inj executed).symm⟩
              · rw [if_neg valid] at executed
                exact Or.inl (Option.some.inj executed).symm

/-- The effect of a merge whose source is alive and whose holder is another
block. -/
theorem merge_effective {doc : Document} {src tgt hold : Block}
    (blocks : (doc.map Block.id).Nodup) (srcMem : src ∈ doc) (tgtMem : tgt ∈ doc)
    (holder : owner doc (root tgt.inst).address = some hold)
    (srcLive : src.alive = true) (distinct : hold.id ≠ src.id) :
    step doc (.merge src.id tgt.id) = some (doc.map (absorb hold.id src)) := by
  simp only [step, findBlock_of_mem blocks srcMem, findBlock_of_mem blocks tgtMem, holder]
  rw [if_pos ⟨srcLive, distinct⟩]
  rfl

/-- A merge whose source is a tombstone leaves the document unchanged. -/
theorem merge_source_dead_noop {doc : Document} {src : Block} (target : Nat)
    (blocks : (doc.map Block.id).Nodup) (srcMem : src ∈ doc) (dead : src.alive = false) :
    step doc (.merge src.id target) = some doc := by
  obtain ⟨next, executed⟩ := Option.ne_none_iff_exists'.mp (merge_total doc src.id target)
  rcases merge_cases executed with rfl | ⟨src', -, -, fs, -, -, live, -, -⟩
  · exact executed
  · rw [findBlock_of_mem blocks srcMem] at fs
    cases fs
    simp [dead] at live

/-- A block merged into itself is unchanged: an alive block is the holder of
its own root, and a tombstone source is a no-op. -/
theorem merge_self_noop {doc : Document} (bid : Nat)
    (h : WellFormed doc) (rooted : Rooted doc) :
    step doc (.merge bid bid) = some doc := by
  obtain ⟨next, executed⟩ := Option.ne_none_iff_exists'.mp (merge_total doc bid bid)
  rcases merge_cases executed with rfl | ⟨src, tgt, hold, fs, ft, fo, live, distinct, -⟩
  · exact executed
  · rw [fs] at ft
    cases ft
    obtain ⟨srcMem, srcId⟩ := findBlock_some fs
    rw [rooted_owner h rooted srcMem live] at fo
    cases fo
    exact absurd srcId distinct

/-- When the target is alive the holder is the target itself, so the merge
appends the source's slots to the target: the rule specialises to the
target-alive merge. -/
theorem merge_alive_target {doc : Document} {src tgt : Block}
    (h : WellFormed doc) (rooted : Rooted doc) (srcMem : src ∈ doc) (tgtMem : tgt ∈ doc)
    (srcLive : src.alive = true) (tgtLive : tgt.alive = true) (distinct : src.id ≠ tgt.id) :
    step doc (.merge src.id tgt.id) = some (doc.map fun block =>
      if block.id = tgt.id then {block with slots := block.slots ++ src.slots}
      else if block.id = src.id then {block with slots := [], alive := false}
      else block) :=
  merge_effective h.1 srcMem tgtMem (rooted_owner h rooted tgtMem tgtLive) srcLive
    (Ne.symm distinct)

/-- When the target's root slot lies in a block other than the source, the
merge appends the source's slots to that block. In particular, a merge into a
tombstone lands in the alive block that absorbed it. -/
theorem merge_absorbed_target {doc : Document} {src tgt hold : Block}
    (h : WellFormed doc) (srcMem : src ∈ doc) (tgtMem : tgt ∈ doc) (holdMem : hold ∈ doc)
    (absorbed : (root tgt.inst).address ∈ hold.slots.map Slot.address)
    (srcLive : src.alive = true) (distinct : hold.id ≠ src.id) :
    step doc (.merge src.id tgt.id) = some (doc.map (absorb hold.id src)) :=
  merge_effective h.1 srcMem tgtMem (owner_of_mem h.2.1 holdMem absorbed) srcLive distinct

/-- When the target's root slot lies in the source's own slots, as after the
source absorbed the target, the merge is a no-op: absorbing would create a
cycle. -/
theorem merge_cycle_noop {doc : Document} {src tgt : Block}
    (h : WellFormed doc) (srcMem : src ∈ doc) (tgtMem : tgt ∈ doc)
    (absorbed : (root tgt.inst).address ∈ src.slots.map Slot.address) :
    step doc (.merge src.id tgt.id) = some doc := by
  obtain ⟨next, executed⟩ := Option.ne_none_iff_exists'.mp (merge_total doc src.id tgt.id)
  rcases merge_cases executed with rfl | ⟨src', tgt', hold, -, ft, fo, -, distinct, -⟩
  · exact executed
  · rw [findBlock_of_mem h.1 tgtMem] at ft
    cases ft
    rw [owner_of_mem h.2.1 srcMem absorbed] at fo
    cases fo
    exact absurd rfl distinct

private theorem three_ids (pre mid post : Document) (a b : Block)
    (unique : (pre ++ a :: mid ++ b :: post).map Block.id |>.Nodup) :
    a.id ≠ b.id ∧ ∀ x ∈ pre ++ mid ++ post, x.id ≠ a.id ∧ x.id ≠ b.id := by
  have perm : ((pre ++ a :: mid ++ b :: post).map Block.id).Perm
      (a.id :: b.id :: (pre ++ mid ++ post).map Block.id) := by
    apply List.perm_iff_count.mpr
    intro x
    simp only [List.map_append, List.map_cons, List.count_append, List.count_cons]
    omega
  have nd := perm.nodup_iff.mp unique
  have outer := List.nodup_cons.mp nd
  have inner := List.nodup_cons.mp outer.2
  refine ⟨fun eq => outer.1 (by simp [eq]), fun x member => ⟨?_, ?_⟩⟩
  · intro eq
    exact outer.1 (List.mem_cons_of_mem _ (eq ▸ List.mem_map.mpr ⟨x, member, rfl⟩))
  · intro eq
    exact inner.1 (eq ▸ List.mem_map.mpr ⟨x, member, rfl⟩)

private theorem rest_fixed (holder : Nat) (src : Block) (xs : Document)
    (other : ∀ x ∈ xs, x.id ≠ src.id ∧ x.id ≠ holder) :
    xs.map (absorb holder src) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx := other x (by simp)
      have rest := ih (fun y hy => other y (by simp [hy]))
      have kept : absorb holder src x = x := by simp [absorb, hx.1, hx.2]
      rw [List.map_cons, kept, rest]

/-- The two document shapes of an absorption, according to whether the
holder precedes the source or follows it. Both blocks keep their positions. -/
theorem absorb_shape {doc : Document} {src hold : Block}
    (blocks : (doc.map Block.id).Nodup) (srcMem : src ∈ doc) (holdMem : hold ∈ doc)
    (distinct : hold.id ≠ src.id) :
    ∃ pre mid post : Document,
      (doc = pre ++ hold :: mid ++ src :: post ∧
        doc.map (absorb hold.id src) = pre ++ {hold with slots := hold.slots ++ src.slots} ::
          mid ++ {src with slots := [], alive := false} :: post) ∨
      (doc = pre ++ src :: mid ++ hold :: post ∧
        doc.map (absorb hold.id src) = pre ++ {src with slots := [], alive := false} ::
          mid ++ {hold with slots := hold.slots ++ src.slots} :: post) := by
  have holdImage : absorb hold.id src hold = {hold with slots := hold.slots ++ src.slots} := by
    simp [absorb]
  have srcImage : absorb hold.id src src = {src with slots := [], alive := false} := by
    simp [absorb, Ne.symm distinct]
  obtain ⟨A, B, rfl⟩ := List.append_of_mem srcMem
  have holdMem' : hold ∈ A ∨ hold ∈ B := by
    rcases List.mem_append.mp holdMem with h | h
    · exact Or.inl h
    · rcases List.mem_cons.mp h with h | h
      · exact absurd (congrArg Block.id h) distinct
      · exact Or.inr h
  rcases holdMem' with inA | inB
  · obtain ⟨pre, mid, rfl⟩ := List.append_of_mem inA
    have shape : (pre ++ hold :: mid) ++ src :: B = pre ++ hold :: mid ++ src :: B := rfl
    rw [shape] at blocks ⊢
    have ids := three_ids pre mid B hold src blocks
    have fixed := fun xs (sub : ∀ x ∈ xs, x ∈ pre ++ mid ++ B) =>
      rest_fixed hold.id src xs (fun x hx => ⟨(ids.2 x (sub x hx)).2, (ids.2 x (sub x hx)).1⟩)
    refine ⟨pre, mid, B, Or.inl ⟨rfl, ?_⟩⟩
    simp only [List.map_append, List.map_cons, holdImage, srcImage,
      fixed pre (by intro x hx; simp [hx]), fixed mid (by intro x hx; simp [hx]),
      fixed B (by intro x hx; simp [hx])]
  · obtain ⟨mid, post, rfl⟩ := List.append_of_mem inB
    have shape : A ++ src :: (mid ++ hold :: post) = A ++ src :: mid ++ hold :: post := by simp
    rw [shape] at blocks ⊢
    have ids := three_ids A mid post src hold blocks
    have fixed := fun xs (sub : ∀ x ∈ xs, x ∈ A ++ mid ++ post) =>
      rest_fixed hold.id src xs (fun x hx => ⟨(ids.2 x (sub x hx)).1, (ids.2 x (sub x hx)).2⟩)
    refine ⟨A, mid, post, Or.inr ⟨rfl, ?_⟩⟩
    simp only [List.map_append, List.map_cons, holdImage, srcImage,
      fixed A (by intro x hx; simp [hx]), fixed mid (by intro x hx; simp [hx]),
      fixed post (by intro x hx; simp [hx])]

/-- Every merge result is the unchanged document or one of the two focused
shapes, the latter only for an alive source and a distinct holder that holds
at least one slot. -/
theorem merge_shape {doc next : Document} {source target : Nat}
    (blocks : (doc.map Block.id).Nodup)
    (executed : step doc (.merge source target) = some next) :
    next = doc ∨ ∃ pre mid post : Document, ∃ hold src : Block,
      src.id = source ∧ src.alive = true ∧ hold.id ≠ src.id ∧ hold ∈ doc ∧ hold.slots ≠ [] ∧
      ((doc = pre ++ hold :: mid ++ src :: post ∧
          next = pre ++ {hold with slots := hold.slots ++ src.slots} :: mid ++
            {src with slots := [], alive := false} :: post) ∨
       (doc = pre ++ src :: mid ++ hold :: post ∧
          next = pre ++ {src with slots := [], alive := false} :: mid ++
            {hold with slots := hold.slots ++ src.slots} :: post)) := by
  rcases merge_cases executed with rfl | ⟨src, tgt, hold, fs, -, fo, live, distinct, rfl⟩
  · exact Or.inl rfl
  · obtain ⟨srcMem, rfl⟩ := findBlock_some fs
    obtain ⟨holdMem, present⟩ := owner_some fo
    obtain ⟨pre, mid, post, shape⟩ := absorb_shape blocks srcMem holdMem distinct
    refine Or.inr ⟨pre, mid, post, hold, src, rfl, live, distinct, holdMem,
      slots_nonempty present, ?_⟩
    rcases shape with ⟨eq, image⟩ | ⟨eq, image⟩
    · exact Or.inl ⟨eq, image⟩
    · exact Or.inr ⟨eq, image⟩

/-- An effective merge on a rooted document removes exactly one block from
the view. -/
theorem merge_view_count {doc : Document} {src tgt hold : Block}
    (blocks : (doc.map Block.id).Nodup) (rooted : Rooted doc)
    (srcMem : src ∈ doc) (tgtMem : tgt ∈ doc)
    (holder : owner doc (root tgt.inst).address = some hold)
    (srcLive : src.alive = true) (distinct : hold.id ≠ src.id) :
    ∃ next, step doc (.merge src.id tgt.id) = some next ∧
      (view next).length + 1 = (view doc).length := by
  refine ⟨_, merge_effective blocks srcMem tgtMem holder srcLive distinct, ?_⟩
  obtain ⟨holdMem, present⟩ := owner_some holder
  have holdLive := rooted_holder_alive rooted holdMem (slots_nonempty present)
  obtain ⟨pre, mid, post, shape⟩ := absorb_shape blocks srcMem holdMem distinct
  rcases shape with ⟨eq, image⟩ | ⟨eq, image⟩ <;> rw [image, eq] <;>
    simp [view, List.filter_append, srcLive, holdLive] <;> omega

/-- A slot projection that distributes over concatenation is conserved up to
permutation by moving one block's slots to the end of another's and emptying
the first. -/
private theorem moved_perm {α : Type} [DecidableEq α] (g : List Slot → List α)
    (distrib : ∀ a b, g (a ++ b) = g a ++ g b) (empty : g [] = [])
    (keep : Block → Bool) (pre mid post : Document) (hold src : Block)
    (holdKeep : keep {hold with slots := hold.slots ++ src.slots} = true)
    (holdKeep' : keep hold = true) (srcKeep : keep src = true) :
    (((pre ++ {hold with slots := hold.slots ++ src.slots} :: mid ++
        {src with slots := [], alive := false} :: post).filter keep).flatMap
        fun b => g b.slots).Perm
      (((pre ++ hold :: mid ++ src :: post).filter keep).flatMap fun b => g b.slots) ∧
    (((pre ++ {src with slots := [], alive := false} :: mid ++
        {hold with slots := hold.slots ++ src.slots} :: post).filter keep).flatMap
        fun b => g b.slots).Perm
      (((pre ++ src :: mid ++ hold :: post).filter keep).flatMap fun b => g b.slots) := by
  constructor <;>
  · apply List.perm_iff_count.mpr
    intro x
    simp only [List.filter_append, List.filter_cons, holdKeep, holdKeep', srcKeep, ↓reduceIte,
      List.flatMap_append, List.flatMap_cons, distrib, List.count_append]
    split <;> (try simp only [List.flatMap_cons, empty, List.nil_append]) <;> omega

private theorem merge_projection_perm {α : Type} [DecidableEq α] (g : List Slot → List α)
    (distrib : ∀ a b, g (a ++ b) = g a ++ g b) (empty : g [] = [])
    (keep : Block → Bool) {doc next : Document} {source target : Nat}
    (keepSlots : ∀ (b : Block) (slots : List Slot), keep {b with slots := slots} = keep b)
    (keepAlive : ∀ b ∈ doc, b.alive = true → keep b = true)
    (keepHolder : ∀ b ∈ doc, b.slots ≠ [] → keep b = true)
    (blocks : (doc.map Block.id).Nodup)
    (executed : step doc (.merge source target) = some next) :
    ((next.filter keep).flatMap fun b => g b.slots).Perm
      ((doc.filter keep).flatMap fun b => g b.slots) := by
  rcases merge_shape blocks executed with rfl | ⟨pre, mid, post, hold, src, -, srcLive, -,
      holdMem, nonempty, shape⟩
  · exact List.Perm.refl _
  · have srcMem : src ∈ doc := by rcases shape with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
    have holdKeep' := keepHolder hold holdMem nonempty
    have perms := moved_perm g distrib empty keep pre mid post hold src
      (by rw [keepSlots]; exact holdKeep') holdKeep' (keepAlive src srcMem srcLive)
    rcases shape with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact perms.1
    · exact perms.2

/-- Conservation of visible characters: on a rooted document the flattened
text of the alive blocks after a merge is a permutation of that before it. -/
theorem merge_text_conserved {doc next : Document} {source target : Nat}
    (blocks : (doc.map Block.id).Nodup) (rooted : Rooted doc)
    (executed : step doc (.merge source target) = some next) :
    (flatText next).Perm (flatText doc) :=
  merge_projection_perm text text_append text_nil Block.alive (fun _ _ => rfl)
    (fun _ _ h => h) (fun _ member nonempty => rooted_holder_alive rooted member nonempty)
    blocks executed

/-- Conservation of slot addresses over all blocks, including hidden roots
and markers. -/
theorem merge_addresses_perm {doc next : Document} {source target : Nat}
    (blocks : (doc.map Block.id).Nodup)
    (executed : step doc (.merge source target) = some next) :
    (flatAddresses next).Perm (flatAddresses doc) := by
  have perm := merge_projection_perm (fun slots => slots.map Slot.address)
    (fun _ _ => List.map_append ..) rfl (fun _ => true) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) blocks executed
  simpa [flatAddresses] using perm

/-- Pairwise distinct slot addresses over all blocks remain pairwise distinct
after a merge. -/
theorem merge_addresses_unique {doc next : Document} {source target : Nat}
    (blocks : (doc.map Block.id).Nodup)
    (unique : (flatAddresses doc).Nodup)
    (executed : step doc (.merge source target) = some next) :
    (flatAddresses next).Nodup :=
  (merge_addresses_perm blocks executed).nodup_iff.mpr unique

/-- Every merge preserves `WellFormed`. No issuance guard is needed: an
ineffective merge is a no-op, and an effective one keeps the holder's hidden
head and leaves block names unchanged. -/
theorem merge_preserves {doc next : Document} {source target : Nat}
    (h : WellFormed doc)
    (executed : step doc (.merge source target) = some next) : WellFormed next := by
  have addresses := merge_addresses_unique h.1 h.2.1 executed
  rcases merge_shape h.1 executed with rfl | ⟨pre, mid, post, hold, src, -, -, -, holdMem, -,
      shape⟩
  · exact h
  · have anchored : hold.alive = true →
        Anchored {hold with slots := hold.slots ++ src.slots} := by
      intro live
      obtain ⟨head, tail, eq, hidden⟩ := h.2.2 hold holdMem live
      exact ⟨head, tail ++ src.slots, by simp [eq], hidden⟩
    rcases shape with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨by simpa using h.1, addresses, ?_⟩
      intro b member live
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with (member | rfl | member) | rfl | member
      · exact h.2.2 b (by simp [member]) live
      · exact anchored live
      · exact h.2.2 b (by simp [member]) live
      · simp at live
      · exact h.2.2 b (by simp [member]) live
    · refine ⟨by simpa using h.1, addresses, ?_⟩
      intro b member live
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with (member | rfl | member) | rfl | member
      · exact h.2.2 b (by simp [member]) live
      · simp at live
      · exact h.2.2 b (by simp [member]) live
      · exact anchored live
      · exact h.2.2 b (by simp [member]) live

/-- Every merge preserves `Rooted`: the holder keeps its root at the head, and
the source becomes a tombstone with no slots. -/
theorem merge_preserves_rooted {doc next : Document} {source target : Nat}
    (blocks : (doc.map Block.id).Nodup) (rooted : Rooted doc)
    (executed : step doc (.merge source target) = some next) : Rooted next := by
  rcases merge_shape blocks executed with rfl | ⟨pre, mid, post, hold, src, -, -, -, holdMem,
      nonempty, shape⟩
  · exact rooted
  · have holdLive := rooted_holder_alive rooted holdMem nonempty
    have extended : Rooted [{hold with slots := hold.slots ++ src.slots}] := by
      intro _ member
      obtain ⟨tail, eq⟩ := (rooted hold holdMem).1 holdLive
      simp only [List.mem_singleton] at member
      subst member
      exact ⟨fun _ => ⟨tail ++ src.slots, by simp [eq]⟩, fun dead => by simp [holdLive] at dead⟩
    have tomb : Rooted [{src with slots := [], alive := false}] := by
      intro b member
      simp only [List.mem_singleton] at member
      subst member
      exact ⟨fun live => by simp at live, fun _ => rfl⟩
    rcases shape with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro b member
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with (member | rfl | member) | rfl | member
      · exact rooted b (by simp [member])
      · exact extended _ (by simp)
      · exact rooted b (by simp [member])
      · exact tomb _ (by simp)
      · exact rooted b (by simp [member])
    · intro b member
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with (member | rfl | member) | rfl | member
      · exact rooted b (by simp [member])
      · exact tomb _ (by simp)
      · exact rooted b (by simp [member])
      · exact extended _ (by simp)
      · exact rooted b (by simp [member])

/-- After an effective merge on a well-formed rooted document, the source's
root slot sits inside the extended holder, after its first slot, and the
extended holder is the holder of the source's root. A later merge into the
source therefore lands in the block that absorbed it. -/
theorem merge_root_absorbed {doc : Document} {src tgt hold : Block}
    (h : WellFormed doc) (rooted : Rooted doc) (srcMem : src ∈ doc) (tgtMem : tgt ∈ doc)
    (holder : owner doc (root tgt.inst).address = some hold)
    (srcLive : src.alive = true) (distinct : hold.id ≠ src.id) :
    (∃ head tail, hold.slots ++ src.slots = head :: tail ∧
      head.address ≠ (root src.inst).address ∧ (root src.inst).address ∈ tail.map Slot.address) ∧
    owner (doc.map (absorb hold.id src)) (root src.inst).address =
      some {hold with slots := hold.slots ++ src.slots} := by
  have executed := merge_effective h.1 srcMem tgtMem holder srcLive distinct
  have unique := merge_addresses_unique h.1 h.2.1 executed
  obtain ⟨holdMem, present⟩ := owner_some holder
  have holdLive := rooted_holder_alive rooted holdMem (slots_nonempty present)
  obtain ⟨holdTail, holdEq⟩ := (rooted hold holdMem).1 holdLive
  obtain ⟨srcTail, srcEq⟩ := (rooted src srcMem).1 srcLive
  have image : {hold with slots := hold.slots ++ src.slots} ∈ doc.map (absorb hold.id src) :=
    List.mem_map.mpr ⟨hold, holdMem, by simp [absorb]⟩
  have inside : (root src.inst).address ∈ (holdTail ++ src.slots).map Slot.address := by
    simp [srcEq]
  have blockUnique : ((root hold.inst :: (holdTail ++ src.slots)).map Slot.address).Nodup := by
    have all := (List.nodup_flatMap.mp unique).1 _ image
    simpa [holdEq] using all
  refine ⟨⟨root hold.inst, holdTail ++ src.slots, by simp [holdEq], ?_, inside⟩, ?_⟩
  · intro same
    rw [List.map_cons] at blockUnique
    exact (List.nodup_cons.mp blockUnique).1 (same ▸ inside)
  · exact owner_of_mem unique image (by simp [srcEq])

/-- A create after a tombstone places the fresh block immediately after the
tombstone, and the fresh block appears in the view between the alive blocks
before and after it. -/
theorem create_after_tombstone (pre post : Document) (tomb : Block) (bid inst : Nat)
    (blocks : ((pre ++ tomb :: post).map Block.id).Nodup)
    (fresh : bid ∉ (pre ++ tomb :: post).map Block.id) (dead : tomb.alive = false) :
    step (pre ++ tomb :: post) (.create bid inst (some tomb.id)) =
        some (pre ++ tomb :: ⟨bid, inst, [root inst], true⟩ :: post) ∧
      (step (pre ++ tomb :: post) (.create bid inst (some tomb.id))).map view =
        some (view pre ++ (bid, []) :: view post) := by
  have created := step_create_focus pre post tomb bid inst blocks fresh
  refine ⟨created, ?_⟩
  rw [created]
  simp [view, dead, root]

/-! Hand-derived PASS+FAIL scenarios. Character values: a=0, b=1, c=2, d=3. -/
private def twoBlocks : Document :=
  [⟨10, 0, [root 0, character 0 (0, 1) 0, character 0 (0, 2) 1], true⟩,
   ⟨11, 1, [root 1, character 1 (1, 1) 2, character 1 (1, 2) 3], true⟩]

/-- Merging the second block into the first gives ab followed by cd in block
10, and block 11 is no longer visible. The source text is neither dropped nor
duplicated. -/
theorem merge_two_control :
    (step twoBlocks (.merge 11 10)).map view = some [(10, [0, 1, 2, 3])] ∧
    (step twoBlocks (.merge 11 10)).map view ≠ some [(10, [0, 1])] ∧
    (step twoBlocks (.merge 11 10)).map view ≠ some [(10, [0, 1, 2, 3]), (11, [2, 3])] ∧
    (step twoBlocks (.merge 11 10)).map view ≠ some [(10, [0, 1, 2, 3]), (11, [])] ∧
    (step twoBlocks (.merge 11 10)).map view ≠ some [(10, [0, 1, 2, 3, 2, 3])] := by decide

/-- The merged source stays in place as an empty tombstone that keeps its
instance, rather than being dropped from the document. -/
theorem merge_tombstone_control :
    step twoBlocks (.merge 11 10) = some
      [⟨10, 0, [root 0, character 0 (0, 1) 0, character 0 (0, 2) 1,
          root 1, character 1 (1, 1) 2, character 1 (1, 2) 3], true⟩,
       ⟨11, 1, [], false⟩] ∧
    step twoBlocks (.merge 11 10) ≠ some
      [⟨10, 0, [root 0, character 0 (0, 1) 0, character 0 (0, 2) 1,
          root 1, character 1 (1, 1) 2, character 1 (1, 2) 3], true⟩] := by decide

/-- Merging the first block into the second appends ab after cd in block 11:
the target's text comes first regardless of document order. -/
theorem merge_backward_control :
    (step twoBlocks (.merge 10 11)).map view = some [(11, [2, 3, 0, 1])] ∧
    (step twoBlocks (.merge 10 11)).map view ≠ some [(11, [0, 1, 2, 3])] := by decide

private def threeBlocks : Document :=
  [⟨10, 0, [root 0, character 0 (0, 1) 0], true⟩,
   ⟨11, 1, [root 1, character 1 (1, 1) 1], true⟩,
   ⟨12, 2, [root 2, character 2 (2, 1) 2, character 2 (2, 2) 3], true⟩]

/-- Merging the last block into the first moves cd past the untouched middle
block; the middle block stays where it was. -/
theorem merge_three_control :
    (step threeBlocks (.merge 12 10)).map view = some [(10, [0, 2, 3]), (11, [1])] ∧
    (step threeBlocks (.merge 12 10)).map view ≠ some [(10, [0]), (11, [1])] ∧
    (step threeBlocks (.merge 12 10)).map view ≠ some [(10, [0, 2, 3]), (11, [1, 2, 3])] ∧
    (step threeBlocks (.merge 12 10)).map view ≠ some [(10, [0, 1, 2, 3])] := by decide

/-- Self-merge and merges naming an absent block change nothing, and an
effective merge is not a no-op. -/
theorem merge_noop_control :
    step threeBlocks (.merge 11 11) = some threeBlocks ∧
    step threeBlocks (.merge 13 10) = some threeBlocks ∧
    step threeBlocks (.merge 10 13) = some threeBlocks ∧
    step threeBlocks (.merge 11 10) ≠ some threeBlocks := by decide

/-- After block 11 is merged into 10, a second merge of 11 into 10 changes
nothing (the source is a tombstone), and so does a merge of 10 into the
tombstone 11 (its holder is 10 itself). A merge into a tombstone does not hide
the target's text, and a repeated merge does not duplicate it. -/
theorem merge_dead_control :
    (execute twoBlocks [.merge 11 10, .merge 11 10]) = step twoBlocks (.merge 11 10) ∧
    (execute twoBlocks [.merge 11 10, .merge 11 10]).map view = some [(10, [0, 1, 2, 3])] ∧
    (execute twoBlocks [.merge 11 10, .merge 11 10]).map view ≠
      some [(10, [0, 1, 2, 3, 2, 3])] ∧
    (execute twoBlocks [.merge 11 10, .merge 10 11]).map view = some [(10, [0, 1, 2, 3])] ∧
    (execute twoBlocks [.merge 11 10, .merge 10 11]).map view ≠ some [] := by decide

/-- A create after the tombstone 11 lands at the tombstone's position, between
blocks 10 and 12, not at the front of the document and not at its end. -/
theorem create_after_tombstone_control :
    (execute threeBlocks [.merge 11 10, .create 13 13 (some 11)]).map view =
      some [(10, [0, 1]), (13, []), (12, [2, 3])] ∧
    (execute threeBlocks [.merge 11 10, .create 13 13 (some 11)]).map view ≠
      some [(13, []), (10, [0, 1]), (12, [2, 3])] ∧
    (execute threeBlocks [.merge 11 10, .create 13 13 (some 11)]).map view ≠
      some [(10, [0, 1]), (12, [2, 3]), (13, [])] := by decide

/-- The source's hidden root is retained inside the target, so addresses stay
unique and the source's anchors remain resolvable. -/
theorem merge_root_retained_control :
    ((step twoBlocks (.merge 11 10)).map fun d => flatAddresses d) =
      some [(0, .start), (0, .event (0, 1)), (0, .event (0, 2)),
        (1, .start), (1, .event (1, 1)), (1, .event (1, 2))] ∧
    ((step twoBlocks (.merge 11 10)).map fun d => flatAddresses d) ≠
      some [(0, .start), (0, .event (0, 1)), (0, .event (0, 2)),
        (1, .event (1, 1)), (1, .event (1, 2))] := by decide

/-- Three one-character blocks a, b, c, with ids 10, 11, 12. -/
private def abc : Document :=
  [⟨10, 0, [root 0, character 0 (0, 1) 0], true⟩,
   ⟨11, 1, [root 1, character 1 (1, 1) 1], true⟩,
   ⟨12, 2, [root 2, character 2 (2, 1) 2], true⟩]

/-- Merge b into a, then c into the tombstone b: c lands in a, the block that
absorbed b. The skip reading would leave ab and c apart, and nothing is
duplicated. -/
theorem merge_absorb_control :
    (execute abc [.merge 11 10, .merge 12 11]).map view = some [(10, [0, 1, 2])] ∧
    (execute abc [.merge 11 10, .merge 12 11]).map view ≠
      some [(10, [0, 1]), (12, [2])] ∧
    (execute abc [.merge 11 10, .merge 12 11]).map view ≠
      some [(10, [0, 1, 2, 2])] ∧
    (execute abc [.merge 11 10, .merge 12 11]).map view ≠
      some [(10, [0, 1])] := by decide

/-- Merge c into b, then b into a: b carries c with it, giving abc in a. -/
theorem merge_chain_control :
    (execute abc [.merge 12 11, .merge 11 10]).map view = some [(10, [0, 1, 2])] ∧
    (execute abc [.merge 12 11, .merge 11 10]).map view ≠ some [(10, [0, 1])] ∧
    (execute abc [.merge 12 11, .merge 11 10]).map view ≠
      some [(10, [0, 1]), (12, [2])] := by decide

/-- Litmus (b): the merges of b into a and c into b give the same view abc in
either order, and neither order leaves ab and c apart. -/
theorem merge_order_litmus_control :
    (execute abc [.merge 11 10, .merge 12 11]).map view =
      (execute abc [.merge 12 11, .merge 11 10]).map view ∧
    (execute abc [.merge 12 11, .merge 11 10]).map view = some [(10, [0, 1, 2])] ∧
    (execute abc [.merge 11 10, .merge 12 11]).map view ≠
      some [(10, [0, 1]), (12, [2])] ∧
    (execute abc [.merge 12 11, .merge 11 10]).map view ≠
      some [(10, [0, 1]), (12, [2])] := by decide

/-- After b is merged into a, a forged merge of a into the tombstone b finds
a itself as b's holder and is a no-op; it does not tombstone a and empty the
document. -/
theorem merge_cycle_control :
    execute abc [.merge 11 10, .merge 10 11] = execute abc [.merge 11 10] ∧
    (execute abc [.merge 11 10, .merge 10 11]).map view = some [(10, [0, 1]), (12, [2])] ∧
    (execute abc [.merge 11 10, .merge 10 11]).map view ≠ some [(12, [2])] ∧
    (execute abc [.merge 11 10, .merge 10 11]).map view ≠ some [] := by decide

#print axioms merge_alive_target
#print axioms merge_absorbed_target
#print axioms merge_cycle_noop
#print axioms merge_self_noop
#print axioms merge_source_dead_noop
#print axioms merge_view_count
#print axioms merge_text_conserved
#print axioms merge_preserves
#print axioms merge_preserves_rooted
#print axioms merge_root_absorbed
#print axioms create_after_tombstone

end Sal.MRDTs.Instances.NotionCoreSpecMerge
