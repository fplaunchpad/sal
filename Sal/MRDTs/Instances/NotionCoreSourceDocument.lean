import Sal.MRDTs.Instances.NotionCoreSource

/-! Document transitions for the materialized physical-source normal form.
Projection theorems use structural guards, not assumed observation equations.
Deriving these guards and this normal form from source issuance remains separate.
-/
namespace Sal.MRDTs.Instances.NotionCoreSourceDocument
open NotionCoreSpec (Address Slot)
open NotionCoreSource (Atom Slice Block RootShape)

abbrev Document := List Block

def project (doc : Document) : NotionCoreSpec.Document := doc.map Block.project

def owns (block : Block) (origin : Address) : Bool :=
  decide (origin ∈ block.active.traversal)

def owner (doc : Document) (origin : Address) : Option Block :=
  doc.find? (fun block => owns block origin)

/-- The otherwise unused empty title-root address is not a prepared origin.
This is an address/shape condition, with no observation or transition premise. -/
def OriginSafe (doc : Document) (origin : Address) : Prop :=
  ∀ block ∈ doc, ∀ inst, block.shape = .attached inst →
    (NotionCoreSpec.root inst).address ≠ origin

def freshBlock (id inst : Nat) : Block :=
  ⟨id, .own, ⟨(inst, .start), []⟩⟩

def insertBlock (block : Block) (origin : Address) (fresh : List Atom) : Block :=
  {block with active := NotionCoreSource.insertSlice block.active (block.active.traversal.idxOf origin) fresh}

def eraseBlock (targets : List Address) (block : Block) : Block :=
  {block with active := NotionCoreSource.eraseSlice targets block.active}

/-- A split destination is a newly created empty root-only title. -/
def EmptyRoot (block : Block) : Prop :=
  block.shape = .own ∧ block.active.start.2 = .start ∧ block.active.atoms = []

instance (block : Block) : Decidable (EmptyRoot block) := inferInstanceAs
  (Decidable (block.shape = .own ∧ block.active.start.2 = .start ∧ block.active.atoms = []))

inductive Command where
  | create (id inst : Nat) (after : Option Nat)
  | insert (origin : Address) (fresh : List Atom)
  | delete (targets : List Address)
  | split (origin marker : Address) (target : Nat)
  deriving DecidableEq, Repr

def Command.semantic : Command → NotionCoreSpec.Command
  | .create id inst after => .create id inst after
  | .insert origin fresh => .insert origin (fresh.map Atom.slot)
  | .delete targets => .delete targets
  | .split origin marker target => .split origin ⟨marker, 0, false⟩ target

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
          else let result := NotionCoreSource.splitBlock source (source.active.traversal.idxOf origin) marker target destination.active.start.1
            some (doc.map fun block =>
              if block.id = source.id then result.1
              else if block.id = target then result.2
              else block)
      | _, _ => none

@[simp] theorem slot_address (atom : Atom) : atom.slot.address = atom.address := by
  cases atom with | mk address kind => cases kind <;> rfl

@[simp] theorem active_addresses (slice : Slice) :
    slice.slots.map Slot.address = slice.traversal := by
  simp [NotionCoreSource.Slice.slots, NotionCoreSource.Slice.anchor,
    NotionCoreSource.Slice.traversal]

@[simp] theorem project_id (block : Block) : block.project.id = block.id := rfl

@[simp] theorem project_ids (doc : Document) : (project doc).map NotionCoreSpec.Block.id =
    doc.map Block.id := by simp [project, Function.comp_def]

@[simp] theorem fresh_project (id inst : Nat) :
    (freshBlock id inst).project = ⟨id, [NotionCoreSpec.root inst]⟩ := rfl

theorem owns_project (block : Block) (origin : Address)
    (safe : ∀ inst, block.shape = .attached inst →
      (NotionCoreSpec.root inst).address ≠ origin) :
    NotionCoreSpec.owns block.project origin = owns block origin := by
  cases shape : block.shape with
  | own => simp [NotionCoreSpec.owns, Block.project, shape, owns]
  | attached inst =>
    have distinct := safe inst shape
    simp [NotionCoreSpec.owns, Block.project, shape, owns, Ne.symm distinct]

theorem owner_project (doc : Document) (origin : Address) (safe : OriginSafe doc origin) :
    NotionCoreSpec.owner (project doc) origin = (owner doc origin).map Block.project := by
  induction doc with
  | nil => rfl
  | cons block rest ih =>
    have headSafe := safe block (by simp)
    have tailSafe : OriginSafe rest origin := fun block member => safe block (by simp [member])
    simp only [project, List.map_cons, NotionCoreSpec.owner, List.find?_cons, owner]
    rw [owns_project block origin headSafe]
    split <;> simp_all [project, NotionCoreSpec.owner, owner]

theorem spec_block_ext {a b : NotionCoreSpec.Block} (ids : a.id = b.id)
    (slots : a.slots = b.slots) : a = b := by
  cases a; cases b; simp_all

theorem insert_block_project (block : Block) (origin : Address) (fresh : List Atom)
    (safe : ∀ inst, block.shape = .attached inst →
      (NotionCoreSpec.root inst).address ≠ origin) :
    (insertBlock block origin fresh).project =
      {block.project with slots := NotionCoreSpec.insertSlots origin (fresh.map Atom.slot) block.project.slots} := by
  have interval := NotionCoreSource.insert_slice_identity_projection block.active origin
    (block.active.traversal.idxOf origin) fresh (by rw [active_addresses])
  apply spec_block_ext
  · rfl
  · cases shape : block.shape with
    | own => simpa [insertBlock, Block.project, shape] using interval
    | attached inst =>
      have cut := NotionCoreSource.cutAfter_invisible_prefix (NotionCoreSpec.root inst)
        block.active.slots origin (safe inst shape)
      simp only [insertBlock, Block.project, shape]
      rw [interval]
      simp [NotionCoreSpec.insertSlots, cut]

theorem erase_block_project (targets : List Address) (block : Block) :
    (eraseBlock targets block).project =
      {block.project with slots := block.project.slots.map (NotionCoreSpec.eraseSlot targets)} := by
  apply spec_block_ext
  · rfl
  · cases shape : block.shape <;>
      simp [eraseBlock, Block.project, shape, NotionCoreSource.erase_slice_projection,
        NotionCoreSpec.root, NotionCoreSpec.eraseSlot]

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
    (safe : OriginSafe doc origin) :
    (step doc (.insert origin fresh)).map project =
      NotionCoreSpec.step (project doc) (.insert origin (fresh.map Atom.slot)) := by
  simp only [step, NotionCoreSpec.step, owner_project doc origin safe]
  cases found : owner doc origin with
  | none => rfl
  | some source =>
    simp only [Option.map_some]
    change some ((doc.map _).map Block.project) = some ((doc.map Block.project).map _)
    congr 1
    simp only [List.map_map]
    apply List.map_congr_left
    intro block member
    have blockSafe := safe block member
    simp only [Function.comp_apply]
    rw [owns_project block origin blockSafe]
    split
    · exact insert_block_project block origin fresh blockSafe
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
    block.project.slots = [NotionCoreSpec.root block.active.start.1] := by
  rcases empty with ⟨shape, start, atoms⟩
  simp [Block.project, shape, NotionCoreSource.Slice.slots,
    NotionCoreSource.Slice.anchor, atoms, NotionCoreSpec.root]
  have address : block.active.start = (block.active.start.1, .start) := by
    exact Prod.ext rfl start
  rw [address]

theorem project_split {doc next : Document} (origin marker : Address) (target : Nat)
    (unique : (doc.map Block.id).Nodup) (safe : OriginSafe doc origin)
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
        have sourceMem : source ∈ doc := List.mem_of_find?_eq_some sourceFound
        have destinationMem : destination ∈ doc := List.mem_of_find?_eq_some destinationFound
        have destinationId : destination.id = target := by
          simpa using List.find?_some destinationFound
        have targetMem : target ∈ doc.map Block.id :=
          List.mem_map.mpr ⟨destination, destinationMem, destinationId⟩
        have sourceSafe := safe source sourceMem
        have sourceCut := NotionCoreSource.split_block_identity_projection source origin
          (source.active.traversal.idxOf origin) marker target destination.active.start.1
          (by rw [active_addresses]) sourceSafe
        have specOwner := owner_project doc origin safe
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
          simp only []
          apply spec_block_ext
          · rfl
          · exact sourceCut.1.symm
        · simp only [if_neg isSource]
          by_cases isTarget : block.id = target
          · have same := same_id_eq unique member destinationMem (isTarget.trans destinationId.symm)
            subst block
            simp only [if_pos isTarget]
            apply spec_block_ext
            · exact destinationId
            · rw [empty_root_project destination empty]
              simpa using sourceCut.2.symm
          · simp only [if_neg isTarget]

/-- Every accepted materialized-source transition has exactly the independently
computed semantic transition. The guards describe source addresses and block
identity uniqueness, not equality of observations. -/
theorem step_sound {doc next : Document} (command : Command)
    (unique : (doc.map Block.id).Nodup)
    (safe : match command with
      | .insert origin _ | .split origin _ _ => OriginSafe doc origin
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
    rw [← project_insert doc origin fresh safe, accepted]
    rfl
  | delete targets =>
    simp only [Command.semantic]
    rw [← project_delete, accepted]
    rfl
  | split origin marker target => exact project_split origin marker target unique safe accepted

/-- Structural guards for projecting a source trace. Acceptance itself checks
origin existence and an empty distinct split destination. Fresh character and
marker allocation and semantic legality are stronger issuance obligations. -/
def Guard (doc : Document) (command : Command) : Prop :=
  (doc.map Block.id).Nodup ∧ match command with
    | .insert origin _ | .split origin _ _ => OriginSafe doc origin
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
    let original : Block := ⟨1, .own, ⟨(1, .start), [a, b]⟩⟩
    let destination := freshBlock 2 2
    let before := [original, destination]
    let after := step before (.split a.address (1, .event (1, 3)) 2)
    (after.map (fun doc => NotionCoreSpec.view (project doc))) =
      some [(1, [97]), (2, [98])] ∧
    (after.map (fun doc => NotionCoreSpec.view (project doc))) ≠
      some [(1, [97, 98]), (2, [])] := by
  decide

#print axioms step_sound
#print axioms execution_sound

end Sal.MRDTs.Instances.NotionCoreSourceDocument
