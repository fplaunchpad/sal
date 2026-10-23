import Sal.MRDTs.Instances.NotionCoreSpec

/-!
An independent sequential specification for Boolean bold formatting.

Research question: does an interval operation affect exactly the visible
identities selected by the issuer? The candidate claim is equality with
`assign` at the rich view. One extra covered character refutes it. The source
interval renderer is a separate reality oracle; the bridge needs an explicit
coverage premise and does not certify JavaScript preparation or replication.

Marks are retained by semantic address, so moving a slot between blocks does
not rename its mark. Formatting commands preserve the underlying document.
Insertion inheritance and concurrent mark arbitration are deliberately staged.
-/
namespace Sal.MRDTs.Instances.NotionCoreFormattingSpec

open NotionCoreSpec

abbrev Marks := Address → Bool

structure State where
  document : Document
  bold : Marks

def plain (document : Document) : State := ⟨document, fun _ => false⟩

structure RichChar where
  address : Address
  value : Nat
  bold : Bool
  deriving DecidableEq, Repr

def richText (marks : Marks) (slots : List Slot) : List RichChar :=
  (slots.filter Slot.visible).map fun slot => ⟨slot.address, slot.value, marks slot.address⟩

def richView (s : State) : List (Nat × List RichChar) :=
  (s.document.filter Block.alive).map fun block => (block.id, richText s.bold block.slots)

theorem richText_congr (left right : Marks) (slots : List Slot)
    (same : ∀ slot ∈ slots, slot.visible = true → left slot.address = right slot.address) :
    richText left slots = richText right slots := by
  apply List.map_congr_left
  intro slot member
  obtain ⟨member, visible⟩ := List.mem_filter.mp member
  simp [same slot member visible]

/-- Equality is needed only on displayed characters, not hidden anchors or
addresses absent from the current document. -/
theorem richView_congr (doc : Document) (left right : Marks)
    (same : ∀ block ∈ doc, block.alive = true →
      ∀ slot ∈ block.slots, slot.visible = true → left slot.address = right slot.address) :
    richView ⟨doc, left⟩ = richView ⟨doc, right⟩ := by
  apply List.map_congr_left
  intro block member
  obtain ⟨member, alive⟩ := List.mem_filter.mp member
  exact congrArg (block.id, ·) (richText_congr left right block.slots (same block member alive))

def forget (display : List (Nat × List RichChar)) : List (Nat × List Nat) :=
  display.map fun block => (block.1, block.2.map RichChar.value)

@[simp] theorem richText_values (marks : Marks) (slots : List Slot) :
    (richText marks slots).map RichChar.value = text slots := by
  simp [richText, text, List.map_map, Function.comp_def]

/-- Forgetting formatting recovers exactly the existing core view. -/
@[simp] theorem forget_richView (s : State) : forget (richView s) = view s.document := by
  simp [forget, richView, view, List.map_map, Function.comp_def]

/-- Explicit identity assignment is the independent local intent. -/
def assign (s : State) (targets : List Address) (value : Bool) : State :=
  {s with bold := fun address => if targets.contains address then value else s.bold address}

/-- The issuer removes bold precisely when every selected identity is bold.
An empty selection changes no mark. -/
def toggleValue (s : State) (targets : List Address) : Bool := !(targets.all s.bold)

def toggle (s : State) (targets : List Address) : State :=
  assign s targets (toggleValue s targets)

@[simp] theorem assign_document (s : State) (targets : List Address) (value : Bool) :
    (assign s targets value).document = s.document := rfl

@[simp] theorem toggle_document (s : State) (targets : List Address) :
    (toggle s targets).document = s.document := rfl

/-- Both the block order and unformatted text survive every format command. -/
theorem assign_preserves_view (s : State) (targets : List Address) (value : Bool) :
    forget (richView (assign s targets value)) = view s.document := by simp

@[simp] theorem assign_selected (s : State) (targets : List Address) (value : Bool)
    (address : Address) (selected : address ∈ targets) :
    (assign s targets value).bold address = value := by simp [assign, selected]

@[simp] theorem assign_untouched (s : State) (targets : List Address) (value : Bool)
    (address : Address) (outside : address ∉ targets) :
    (assign s targets value).bold address = s.bold address := by simp [assign, outside]

/-- This biconditional rules out both spill and a formatting no-op. -/
theorem assign_changes_exactly (s : State) (targets : List Address) (value : Bool)
    (address : Address) :
    (assign s targets value).bold address ≠ s.bold address ↔
      address ∈ targets ∧ value ≠ s.bold address := by
  by_cases selected : address ∈ targets <;> simp [assign, selected]

theorem toggle_off (s : State) (targets : List Address)
    (allBold : ∀ address ∈ targets, s.bold address = true)
    (address : Address) (selected : address ∈ targets) :
    (toggle s targets).bold address = false := by
  have all : targets.all s.bold = true := List.all_eq_true.mpr allBold
  simp [toggle, toggleValue, all, selected]

theorem toggle_on (s : State) (targets : List Address)
    (notAllBold : targets.all s.bold = false)
    (address : Address) (selected : address ∈ targets) :
    (toggle s targets).bold address = true := by
  simp [toggle, toggleValue, notAllBold, selected]

theorem toggle_empty (s : State) : toggle s [] = s := by
  cases s
  simp [toggle, assign]

/-- Identity selection can span blocks. A block whose addresses are outside
the selection has exactly the same rich text. -/
theorem richText_assign_untouched (s : State) (targets : List Address) (value : Bool)
    (slots : List Slot) (outside : ∀ slot ∈ slots, slot.address ∉ targets) :
    richText (assign s targets value).bold slots = richText s.bold slots := by
  apply List.map_congr_left
  intro slot member
  have memSlots := (List.mem_filter.mp member).1
  simp [assign, outside slot memSlots]

/-- Positional formatting selects only the current block's visible identities
in [start, stop), using the core's independent retained-slot scanner. -/
def prepareSelection (doc : Document) (bid start stop : Nat) : Option (List Address) := do
  let block ← findBlock doc bid
  if block.alive = true ∧ start ≤ stop ∧ stop ≤ (text block.slots).length then
    pure (prepareDelete block.slots start (stop - start))
  else none

theorem visible_take_gapIndex (slots : List Slot) (index : Nat) :
    (slots.take (gapIndex slots index)).filter Slot.visible =
      (slots.filter Slot.visible).take index := by
  induction slots generalizing index with
  | nil => cases index <;> simp [gapIndex]
  | cons slot rest ih =>
    cases index with
    | zero => simp [gapIndex]
    | succ index => cases h : slot.visible <;> simp [gapIndex, h, ih]

theorem visible_drop_gapIndex (slots : List Slot) (index : Nat) :
    (slots.drop (gapIndex slots index)).filter Slot.visible =
      (slots.filter Slot.visible).drop index := by
  induction slots generalizing index with
  | nil => cases index <;> simp [gapIndex]
  | cons slot rest ih =>
    cases index with
    | zero => simp [gapIndex]
    | succ index => cases h : slot.visible <;> simp [gapIndex, h, ih]

/-- The target list is literally the requested visible slice; invisible
anchors cannot become targets and no successor outside the slice is added. -/
theorem prepared_targets_exact (slots : List Slot) (start count : Nat) :
    prepareDelete slots start count =
      (((slots.filter Slot.visible).drop start).take count).map Slot.address := by
  simp [prepareDelete, targetsIn, visible_take_gapIndex, visible_drop_gapIndex]

theorem prepareSelection_success (pre post : Document) (block : Block) (start stop : Nat)
    (unique : ((pre ++ block :: post).map Block.id).Nodup)
    (alive : block.alive = true)
    (bound : start ≤ stop ∧ stop ≤ (text block.slots).length) :
    prepareSelection (pre ++ block :: post) block.id start stop =
      some ((((block.slots.filter Slot.visible).drop start).take (stop - start)).map Slot.address) := by
  simp [prepareSelection, findBlock_focus pre post block unique, alive, bound,
    prepared_targets_exact]

/-- A staged wrapper for the conservative plain-document projection. Its core
branch keeps the address mark function unchanged; in particular it does not
implement source interval inheritance for newly inserted characters. -/
inductive Command where
  | core (command : NotionCoreSpec.Command)
  | setBold (targets : List Address) (value : Bool)
  | toggleBold (targets : List Address)

def step (s : State) : Command → Option State
  | .core command => (NotionCoreSpec.step s.document command).map fun doc => {s with document := doc}
  | .setBold targets value => some (assign s targets value)
  | .toggleBold targets => some (toggle s targets)

/-- The wrapper commutes with core execution after forgetting its marks. -/
theorem core_step_projection (s : State) (command : NotionCoreSpec.Command) :
    (step s (.core command)).map State.document = NotionCoreSpec.step s.document command := by
  simp [step, Option.map_map, Function.comp_def]

/-- The staged core branch keeps the entire mark function. A fresh identity
therefore reads its pre-existing function value (false in `plain`), rather
than inheriting the source interval at its insertion point. -/
theorem core_step_retains_marks (s next : State) (command : NotionCoreSpec.Command)
    (executed : step s (.core command) = some next) : next.bold = s.bold := by
  cases h : NotionCoreSpec.step s.document command with
  | none => simp [step, h] at executed
  | some doc => simpa [step, h] using (congrArg (fun t => t.map State.bold) executed).symm

/-! Hand-derived controls: block 10 is a,b and block 11 is c,d. -/
private def twoBlocks : State := plain
  [⟨10, 0, [root 0, character 0 (0, 1) 97, character 0 (0, 2) 98], true⟩,
   ⟨11, 1, [root 1, character 1 (0, 3) 99, character 1 (0, 4) 100], true⟩]

private def bc : List Address := [(0, .event (0, 2)), (1, .event (0, 3))]

private def displayFlags (s : State) : List (Nat × List (Nat × Bool)) :=
  (richView s).map fun block => (block.1, block.2.map fun c => (c.value, c.bold))

/-- A crossing selection marks b,c and cannot spill to either neighbour. -/
theorem crossing_bold_control :
    displayFlags (toggle twoBlocks bc) =
      [(10, [(97, false), (98, true)]), (11, [(99, true), (100, false)])] ∧
    displayFlags (toggle twoBlocks bc) ≠
      [(10, [(97, false), (98, true)]), (11, [(99, true), (100, true)])] ∧
    displayFlags (toggle twoBlocks bc) ≠ displayFlags twoBlocks := by decide

/-- Repeating a uniform toggle switches bold off, including across blocks. -/
theorem toggle_twice_control :
    displayFlags (toggle (toggle twoBlocks bc) bc) = displayFlags twoBlocks ∧
    displayFlags (toggle (toggle twoBlocks bc) bc) ≠ displayFlags (toggle twoBlocks bc) := by decide

/-- A mixed selection switches all selected identities on, rather than
inverting each old mark independently. -/
theorem mixed_toggle_control :
    displayFlags (toggle (assign twoBlocks [(0, .event (0, 2))] true) bc) =
      [(10, [(97, false), (98, true)]), (11, [(99, true), (100, false)])] ∧
    displayFlags (toggle (assign twoBlocks [(0, .event (0, 2))] true) bc) ≠
      [(10, [(97, false), (98, false)]), (11, [(99, true), (100, false)])] := by decide

/-- Local selection does not silently extend into a neighbouring block, and
oversized bounds are rejected. -/
theorem selection_control :
    prepareSelection twoBlocks.document 10 1 2 = some [(0, .event (0, 2))] ∧
    prepareSelection twoBlocks.document 10 1 2 ≠ some bc ∧
    prepareSelection twoBlocks.document 10 1 3 = none ∧
    prepareSelection twoBlocks.document 10 1 2 ≠ none := by decide

#print axioms forget_richView
#print axioms assign_changes_exactly
#print axioms prepareSelection_success
#print axioms core_step_projection

end Sal.MRDTs.Instances.NotionCoreFormattingSpec
