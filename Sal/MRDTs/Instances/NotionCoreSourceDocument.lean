import Sal.MRDTs.Instances.NotionCoreSource

/-! Document transitions for the materialized physical-source normal form.
Projection theorems use structural guards, not assumed observation equations.
Deriving these guards and this normal form from source issuance remains separate.
-/
namespace Sal.MRDTs.Instances.NotionCoreSourceDocument
open NotionCoreSpec (Address Slot)
open NotionCoreSource (Atom Slice Block)

abbrev Document := List Block

def project (doc : Document) : NotionCoreSpec.Document := doc.map Block.project

/-- A block owns every address held by one of its slices. -/
def owns (block : Block) (origin : Address) : Bool :=
  decide (origin ∈ block.traversal)

def owner (doc : Document) (origin : Address) : Option Block :=
  doc.find? (fun block => owns block origin)

def findBlock (doc : Document) (bid : Nat) : Option Block :=
  doc.find? (fun block => decide (block.id = bid))

def freshBlock (id inst : Nat) : Block :=
  ⟨id, inst, [⟨(inst, .start), []⟩]⟩

def insertBlock (block : Block) (origin : Address) (fresh : List Atom) : Block :=
  {block with slices := NotionCoreSource.insertSlices origin fresh block.slices}

def eraseBlock (targets : List Address) (block : Block) : Block :=
  {block with slices := block.slices.map (NotionCoreSource.eraseSlice targets)}

/-- A split destination is a newly created block holding only the empty root
interval of its own instance. -/
def EmptyRoot (block : Block) : Prop :=
  block.slices = [⟨(block.inst, .start), []⟩]

instance (block : Block) : Decidable (EmptyRoot block) :=
  inferInstanceAs (Decidable (block.slices = [⟨(block.inst, .start), []⟩]))

inductive Command where
  | create (id inst : Nat) (after : Option Nat)
  | insert (origin : Address) (fresh : List Atom)
  | delete (targets : List Address)
  | split (origin marker : Address) (target : Nat)
  | merge (source target : Nat)
  deriving DecidableEq, Repr

def Command.semantic : Command → NotionCoreSpec.Command
  | .create id inst after => .create id inst after
  | .insert origin fresh => .insert origin (fresh.map Atom.slot)
  | .delete targets => .delete targets
  | .split origin marker target => .split origin ⟨marker, 0, false⟩ target
  | .merge source target => .merge source target

/-- Physical source transitions. A split cuts the owner's chain after the
origin: the kept slices stay, and the marker slice with every later slice is
appended to the empty destination. A merge looks up the holder of the
target's root interval; if the source is alive and is not that holder, the
source's chain is appended below the holder's last slice and the source
becomes a tombstone that keeps its place. Any other merge changes nothing. -/
def step (doc : Document) : Command → Option Document
  | .create id inst after =>
      if id ∈ doc.map Block.id then none
      else match after with
      | none => some (freshBlock id inst :: doc)
      | some previous =>
          if previous ∈ doc.map Block.id then
            some (doc.flatMap fun block =>
              if block.id = previous then [block, freshBlock id inst] else [block])
          else none
  | .insert origin fresh =>
      match owner doc origin with
      | none => none
      | some _ => some (doc.map fun block =>
          if owns block origin then insertBlock block origin fresh else block)
  | .delete targets => some (doc.map (eraseBlock targets))
  | .split origin marker target =>
      match owner doc origin, doc.find? (fun block => block.id == target) with
      | some source, some destination =>
          if source.id = target ∨ ¬ EmptyRoot destination then none
          else
            let cut := NotionCoreSource.splitSlices origin marker source.slices
            some (doc.map fun block =>
              if block.id = source.id then {block with slices := cut.1}
              else if block.id = target then {block with slices := block.slices ++ cut.2}
              else block)
      | _, _ => none
  | .merge source target =>
      match findBlock doc source, findBlock doc target with
      | some src, some tgt =>
          match owner doc (tgt.inst, .start) with
          | some holder =>
              if src.alive = true ∧ holder.id ≠ source then
                some (doc.map fun block =>
                  if block.id = holder.id then {block with slices := block.slices ++ src.slices}
                  else if block.id = source then {block with slices := []}
                  else block)
              else some doc
          | none => some doc
      | _, _ => some doc

@[simp] theorem slot_address (atom : Atom) : atom.slot.address = atom.address :=
  NotionCoreSource.Atom.slot_address atom

@[simp] theorem active_addresses (slice : Slice) :
    slice.slots.map Slot.address = slice.traversal :=
  NotionCoreSource.Slice.slots_addresses slice

@[simp] theorem project_id (block : Block) : block.project.id = block.id := rfl

@[simp] theorem project_alive (block : Block) : block.project.alive = block.alive := rfl

@[simp] theorem project_slots (block : Block) : block.project.slots = block.slots := rfl

@[simp] theorem project_inst (block : Block) : block.project.inst = block.inst := rfl

@[simp] theorem project_ids (doc : Document) : (project doc).map NotionCoreSpec.Block.id =
    doc.map Block.id := by simp [project, Function.comp_def]

@[simp] theorem fresh_project (id inst : Nat) :
    (freshBlock id inst).project = ⟨id, inst, [NotionCoreSpec.root inst], true⟩ := rfl

theorem owns_project (block : Block) (origin : Address) :
    NotionCoreSpec.owns block.project origin = owns block origin := by
  simp [NotionCoreSpec.owns, Block.project, owns]

theorem owner_project (doc : Document) (origin : Address) :
    NotionCoreSpec.owner (project doc) origin = (owner doc origin).map Block.project := by
  induction doc with
  | nil => rfl
  | cons block rest ih =>
    simp only [project, List.map_cons, NotionCoreSpec.owner, List.find?_cons, owner]
    rw [owns_project block origin]
    split <;> simp_all [project, NotionCoreSpec.owner, owner]

theorem findBlock_project (doc : Document) (bid : Nat) :
    NotionCoreSpec.findBlock (project doc) bid = (findBlock doc bid).map Block.project := by
  induction doc with
  | nil => rfl
  | cons block rest ih =>
    simp only [project, List.map_cons, NotionCoreSpec.findBlock, List.find?_cons, findBlock,
      project_id]
    split <;> simp_all [project, NotionCoreSpec.findBlock, findBlock]

theorem owner_some {doc : Document} {origin : Address} {block : Block}
    (found : owner doc origin = some block) : block ∈ doc ∧ origin ∈ block.traversal :=
  ⟨List.mem_of_find?_eq_some found, by simpa [owns] using List.find?_some found⟩

/-- A block that owns an address holds a slice, so it is alive. -/
theorem owns_alive {block : Block} {origin : Address} (held : origin ∈ block.traversal) :
    block.alive = true := by
  cases slices : block.slices with
  | nil => simp [Block.traversal, slices] at held
  | cons _ _ => simp [Block.alive, slices]

theorem spec_block_ext {a b : NotionCoreSpec.Block} (ids : a.id = b.id)
    (slots : a.slots = b.slots) (alive : a.alive = b.alive) (inst : a.inst = b.inst) :
    a = b := by
  cases a; cases b; simp_all

theorem insert_block_project (block : Block) (origin : Address) (fresh : List Atom)
    (unique : block.traversal.Nodup) (present : origin ∈ block.traversal) :
    (insertBlock block origin fresh).project =
      {block.project with slots := NotionCoreSpec.insertSlots origin (fresh.map Atom.slot) block.project.slots} := by
  refine spec_block_ext rfl ?_ ?_ rfl
  · exact NotionCoreSource.insertSlices_projection origin fresh block.slices unique present
  · simp [insertBlock, Block.project, Block.alive, NotionCoreSource.insertSlices]

theorem erase_block_project (targets : List Address) (block : Block) :
    (eraseBlock targets block).project =
      {block.project with slots := block.project.slots.map (NotionCoreSpec.eraseSlot targets)} := by
  refine spec_block_ext rfl ?_ ?_ rfl
  · exact NotionCoreSource.eraseSlices_projection targets block.slices
  · simp [eraseBlock, Block.project, Block.alive]

/-- Two successive erasures of a block are one erasure of both target lists. -/
theorem eraseBlock_eraseBlock (a b : List Address) (block : Block) :
    eraseBlock b (eraseBlock a block) = eraseBlock (a ++ b) block := by
  simp only [eraseBlock, List.map_map]
  congr 1
  apply List.map_congr_left
  intro slice _
  simp only [Function.comp_apply, NotionCoreSource.eraseSlice, List.map_map]
  congr 1
  apply List.map_congr_left
  intro atom _
  cases atom with
  | mk address kind =>
    cases kind <;> simp [NotionCoreSource.eraseAtom, Bool.or_assoc]

theorem project_create (doc : Document) (id inst : Nat) (after : Option Nat) :
    (step doc (.create id inst after)).map project =
      NotionCoreSpec.step (project doc) (.create id inst after) := by
  by_cases duplicate : id ∈ doc.map Block.id
  · simp [step, NotionCoreSpec.step, duplicate]
  · cases after with
    | none =>
      simp [step, NotionCoreSpec.step, duplicate, project]
      intro block member eq
      exact duplicate (List.mem_map.mpr ⟨block, member, eq⟩)
    | some previous =>
      by_cases present : previous ∈ doc.map Block.id
      · simp [step, NotionCoreSpec.step, duplicate, present, project,
          List.map_flatMap, List.flatMap_map, Function.comp_def]
        congr 1
        funext block
        split <;> simp_all
      · simp [step, NotionCoreSpec.step, duplicate, present]

theorem project_insert (doc : Document) (origin : Address) (fresh : List Atom)
    (unique : ∀ block ∈ doc, block.traversal.Nodup) :
    (step doc (.insert origin fresh)).map project =
      NotionCoreSpec.step (project doc) (.insert origin (fresh.map Atom.slot)) := by
  simp only [step, NotionCoreSpec.step, owner_project doc origin]
  cases found : owner doc origin with
  | none => rfl
  | some source =>
    simp only [Option.map_some]
    change some ((doc.map _).map Block.project) = some ((doc.map Block.project).map _)
    congr 1
    simp only [List.map_map]
    apply List.map_congr_left
    intro block member
    simp only [Function.comp_apply]
    rw [owns_project block origin]
    split
    · rename_i held
      exact insert_block_project block origin fresh (unique block member)
        (by simpa [owns] using held)
    · rfl

theorem project_delete (doc : Document) (targets : List Address) :
    (step doc (.delete targets)).map project =
      NotionCoreSpec.step (project doc) (.delete targets) := by
  simp only [step, NotionCoreSpec.step, Option.map_some, project, List.map_map]
  congr 1
  exact List.map_congr_left fun block _ => erase_block_project targets block

theorem same_id_eq {doc : Document} (unique : (doc.map Block.id).Nodup)
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

theorem empty_root_project (block : Block) (empty : EmptyRoot block) :
    block.project.slots = [NotionCoreSpec.root block.inst] := by
  have slices : block.slices = [⟨(block.inst, .start), []⟩] := empty
  simp [Block.project, Block.slots, slices, NotionCoreSource.Slice.slots,
    NotionCoreSource.Slice.anchor, NotionCoreSpec.root]

theorem project_split {doc next : Document} (origin marker : Address) (target : Nat)
    (unique : (doc.map Block.id).Nodup)
    (accepted : step doc (.split origin marker target) = some next) :
    NotionCoreSpec.step (project doc) (.split origin ⟨marker, 0, false⟩ target) =
      some (project next) := by
  cases sourceFound : owner doc origin with
  | none => simp [step, sourceFound] at accepted
  | some source =>
    cases destinationFound : doc.find? (fun block => block.id == target) with
    | none => simp [step, sourceFound, destinationFound] at accepted
    | some destination =>
      simp only [step, sourceFound, destinationFound] at accepted
      split at accepted
      · simp at accepted
      · rename_i guard
        have distinct : source.id ≠ target := (not_or.mp guard).1
        have empty : EmptyRoot destination := Classical.not_not.mp (not_or.mp guard).2
        obtain ⟨sourceMem, held⟩ := owner_some sourceFound
        have destinationMem : destination ∈ doc := List.mem_of_find?_eq_some destinationFound
        have destinationId : destination.id = target := by
          simpa using List.find?_some destinationFound
        have targetMem : target ∈ doc.map Block.id :=
          List.mem_map.mpr ⟨destination, destinationMem, destinationId⟩
        have cut := NotionCoreSource.splitSlices_projection origin marker source.slices held
        have kept := NotionCoreSource.splitSlices_left_ne_nil origin marker source.slices held
        have specOwner := owner_project doc origin
        rw [sourceFound] at specOwner
        simp only [Option.map_some] at specOwner
        simp only [NotionCoreSpec.step, specOwner, project_id, project_ids]
        rw [if_neg (by simp [distinct, targetMem])]
        injection accepted with nextEq
        subst next
        simp only [project, List.map_map, Option.some.injEq]
        apply List.map_congr_left
        intro block member
        simp only [Function.comp_apply, project_id]
        by_cases isSource : block.id = source.id
        · have same := same_id_eq unique member sourceMem isSource
          subst block
          simp only [↓reduceIte]
          refine spec_block_ext rfl ?_ ?_ rfl
          · exact cut.1.symm
          · have live := owns_alive held
            simp only [Block.alive] at live
            simp only [Block.project, Block.alive, live]
            cases h : (NotionCoreSource.splitSlices origin marker source.slices).1 with
            | nil => exact absurd h kept
            | cons _ _ => rfl
        · simp only [if_neg isSource]
          by_cases isTarget : block.id = target
          · have same := same_id_eq unique member destinationMem (isTarget.trans destinationId.symm)
            subst block
            simp only [if_pos isTarget]
            refine spec_block_ext rfl ?_ ?_ rfl
            · simp only [Block.project, Block.slots, List.flatMap_append]
              rw [cut.2]
            · have slices : destination.slices = [⟨(destination.inst, .start), []⟩] := empty
              simp [Block.project, Block.alive, slices]
          · simp only [if_neg isTarget]

theorem project_merge {doc next : Document} (source target : Nat)
    (unique : (doc.map Block.id).Nodup)
    (accepted : step doc (.merge source target) = some next) :
    NotionCoreSpec.step (project doc) (.merge source target) = some (project next) := by
  simp only [NotionCoreSpec.step, findBlock_project]
  cases foundSource : findBlock doc source with
  | none => simp [step, foundSource] at accepted; subst next; rfl
  | some src =>
    cases foundTarget : findBlock doc target with
    | none => simp [step, foundSource, foundTarget] at accepted; subst next; rfl
    | some tgt =>
      simp only [Option.map_some]
      have specOwner := owner_project doc (tgt.inst, .start)
      change NotionCoreSpec.owner (project doc) (NotionCoreSpec.root tgt.project.inst).address = _ at specOwner
      rw [specOwner]
      cases foundHolder : owner doc (tgt.inst, .start) with
      | none => simp [step, foundSource, foundTarget, foundHolder] at accepted; subst next; rfl
      | some holder =>
        simp only [Option.map_some, project_alive, project_id]
        simp only [step, foundSource, foundTarget, foundHolder] at accepted
        split at accepted
        · rename_i valid
          rw [if_pos valid]
          injection accepted with nextEq
          subst next
          obtain ⟨holderMem, held⟩ := owner_some foundHolder
          simp only [project, List.map_map, Option.some.injEq]
          apply List.map_congr_left
          intro block member
          simp only [Function.comp_apply, project_id]
          by_cases isHolder : block.id = holder.id
          · have same := same_id_eq unique member holderMem isHolder
            subst block
            simp only [↓reduceIte]
            refine spec_block_ext rfl ?_ ?_ rfl
            · simp [Block.project, Block.slots]
            · have live := owns_alive held
              simp only [Block.project, Block.alive] at live ⊢
              rw [live]
              cases h : holder.slices with
              | nil => simp [h] at live
              | cons _ _ => rfl
          · simp only [if_neg isHolder]
            split <;> rfl
        · rename_i invalid
          rw [if_neg invalid]
          injection accepted with nextEq
          subst next
          rfl

/-- Every accepted materialized-source transition has exactly the independently
computed semantic transition. The guards describe block identity uniqueness
and, for insertion, address uniqueness within each block; they are not
equalities of observations. -/
theorem step_sound {doc next : Document} (command : Command)
    (unique : (doc.map Block.id).Nodup)
    (addresses : match command with
      | .insert _ _ => ∀ block ∈ doc, block.traversal.Nodup
      | _ => True)
    (accepted : step doc command = some next) :
    NotionCoreSpec.step (project doc) command.semantic = some (project next) := by
  cases command with
  | create id inst after =>
    simp only [Command.semantic]
    rw [← project_create, accepted]
    rfl
  | insert origin fresh =>
    simp only [Command.semantic]
    rw [← project_insert doc origin fresh addresses, accepted]
    rfl
  | delete targets =>
    simp only [Command.semantic]
    rw [← project_delete, accepted]
    rfl
  | split origin marker target => exact project_split origin marker target unique accepted
  | merge source target => exact project_merge source target unique accepted

/-- Structural guards for projecting a source trace. Acceptance itself checks
origin existence and an empty distinct split destination. Fresh character and
marker allocation and semantic legality are stronger issuance obligations. -/
def Guard (doc : Document) (command : Command) : Prop :=
  (doc.map Block.id).Nodup ∧ match command with
    | .insert _ _ => ∀ block ∈ doc, block.traversal.Nodup
    | _ => True

inductive Execution : Document → List Command → Document → Prop where
  | nil (doc) : Execution doc [] doc
  | cons {doc next final command rest} :
      Guard doc command → step doc command = some next →
      Execution next rest final → Execution doc (command :: rest) final

/-- Universal simulation of accepted guarded physical-source traces by the
independent command machine, without assuming a final observation equation.
This is not the RA execution/history bridge or a JavaScript extraction theorem. -/
theorem execution_sound {doc final : Document} {commands : List Command}
    (run : Execution doc commands final) :
    NotionCoreSpec.execute (project doc) (commands.map Command.semantic) =
      some (project final) := by
  induction run with
  | nil doc => rfl
  | @cons doc next final command rest guard accepted tail ih =>
    simp only [List.map_cons, NotionCoreSpec.execute]
    rw [step_sound command guard.1 guard.2 accepted]
    exact ih

/-- Hand-derived local source trace: creating and splitting ab at its first
character moves b into the destination. -/
theorem source_trace_control :
    let a : Atom := ⟨(1, .event (1, 1)), .text 97 false⟩
    let b : Atom := ⟨(1, .event (1, 2)), .text 98 false⟩
    let original : Block := ⟨1, 1, [⟨(1, .start), [a, b]⟩]⟩
    let destination := freshBlock 2 2
    let before := [original, destination]
    let after := step before (.split a.address (1, .event (1, 3)) 2)
    (after.map (fun doc => NotionCoreSpec.view (project doc))) =
      some [(1, [97]), (2, [98])] ∧
    (after.map (fun doc => NotionCoreSpec.view (project doc))) ≠
      some [(1, [97, 98]), (2, [])] := by
  decide

/-- Hand-derived merge trace: after the split above, merging block 2 back
into block 1 shows ab in block 1 and hides block 2, and merging the tombstone
again changes nothing. -/
theorem source_merge_control :
    let a : Atom := ⟨(1, .event (1, 1)), .text 97 false⟩
    let b : Atom := ⟨(1, .event (1, 2)), .text 98 false⟩
    let before : Document := [⟨1, 1, [⟨(1, .start), [a, b]⟩]⟩, freshBlock 2 2]
    let after := (step before (.split a.address (1, .event (1, 3)) 2)).bind
      (fun doc => step doc (.merge 2 1))
    (after.map (fun doc => NotionCoreSpec.view (project doc))) = some [(1, [97, 98])] ∧
    (after.bind (fun doc => step doc (.merge 2 1))) = after ∧
    (after.map (fun doc => NotionCoreSpec.view (project doc))) ≠
      some [(1, [97]), (2, [98])] := by
  decide

/-- The cycle no-op loses nothing. After block 2 is merged into block 1, a
split of 1 just before the absorbed part moves 2's root into the fresh block
3; a merge of 3 into the tombstone 2 then finds 3 itself holding 2's root and
changes nothing, so b stays visible in block 3. -/
theorem source_cycle_control :
    let a : Atom := ⟨(1, .event (1, 1)), .text 97 false⟩
    let b : Atom := ⟨(2, .event (1, 2)), .text 98 false⟩
    let before : Document := [⟨1, 1, [⟨(1, .start), [a]⟩]⟩, ⟨2, 2, [⟨(2, .start), [b]⟩]⟩]
    let split := (step before (.merge 2 1)).bind (fun doc => step doc (.create 3 3 (some 1)))
      |>.bind (fun doc => step doc (.split a.address (1, .event (1, 3)) 3))
    let after := split.bind (fun doc => step doc (.merge 3 2))
    after = split ∧
    (after.map (fun doc => NotionCoreSpec.view (project doc))) = some [(1, [97]), (3, [98])] ∧
    (after.map (fun doc => NotionCoreSpec.view (project doc))) ≠ some [(1, [97])] := by
  decide

theorem fresh_normal (id inst : Nat) : (freshBlock id inst).Normal := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [freshBlock, NotionCoreSource.deadSlices]

#print axioms step_sound
#print axioms execution_sound
#print axioms source_cycle_control

end Sal.MRDTs.Instances.NotionCoreSourceDocument
