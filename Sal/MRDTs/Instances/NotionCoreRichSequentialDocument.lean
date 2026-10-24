import Sal.MRDTs.Instances.NotionCoreRichSequential
import Sal.MRDTs.Instances.NotionCoreFormattingSpec
import Sal.MRDTs.Paper1.HistorySpec

/-! Independent rich document transitions. Physical instance sequences remain
separate from displayed block order. Painting mutates current cell/gap marks;
no annotation list, transaction priority, source interpreter or sort is stored.
-/
namespace Sal.MRDTs.Instances.NotionCoreRichSequential
open NotionCoreSpec

/-- Before a stable physical item, or the instance END. START/after affinity is
not part of the repaired maximal-run request compiler's supported alphabet. -/
inductive Endpoint where
  | before (id : Nat × Nat)
  | finish
  deriving DecidableEq, Repr

structure Region where
  instanceId : Nat
  lower : Endpoint
  upper : Endpoint
  deriving DecidableEq, Repr

structure State where
  document : Document := []
  texts : Nat → Option Text := fun _ => none

def endpointPosition (inst : Nat) (text : Text) : Endpoint → Option Nat
  | .finish => some text.items.length
  | .before id => (text.items.map Slot.address).findIdx? (fun a => a == (inst,.event id))

def resolveRegion (text : Text) (region : Region) : Option Range := do
  pure ⟨← endpointPosition region.instanceId text region.lower,
    ← endpointPosition region.instanceId text region.upper⟩

def readAt (state : State) (address : Address) : Option Bool := do
  let text ← state.texts address.1
  let index ← (text.items.map Slot.address).findIdx? (fun a => a == address)
  pure (text.bold index)

abbrev RichChar := NotionCoreFormattingSpec.RichChar

def render (state : State) : Option (List (Nat × List RichChar)) :=
  (state.document.filter Block.alive).mapM fun block => do
    let characters ← (block.slots.filter Slot.visible).mapM fun slot => do
      pure (⟨slot.address,slot.value,← readAt state slot.address⟩ : RichChar)
    pure (block.id,characters)

def forget := NotionCoreFormattingSpec.forget

def putText (texts : Nat → Option Text) (inst : Nat) (text : Text) : Nat → Option Text :=
  fun i => if i = inst then some text else texts i

def insertionGap (inst : Nat) (text : Text) (origin : LocalId) : Option Nat :=
  match origin with
  | .start => some 0
  | .event id => ((text.items.map Slot.address).findIdx? (fun a => a == (inst,.event id))).map (·+1)
  | .close _ | .finish => none

def insertPhysical (texts : Nat → Option Text) (origin : Address) (fresh : List Slot) :
    Option (Nat → Option Text) := do
  let text ← texts origin.1
  let gap ← insertionGap origin.1 text origin.2
  pure (putText texts origin.1 (insertAt text gap fresh))

/-- Split has a physical marker birth. Merge only changes displayed ownership. -/
def coreTexts (texts : Nat → Option Text) : NotionCoreSpec.Command → Option (Nat → Option Text)
  | .create _ inst _ => if (texts inst).isSome then none else some (putText texts inst (Text.plain []))
  | .insert origin fresh => insertPhysical texts origin fresh
  | .delete targets => some (fun i => (texts i).map (fun text => erase text targets))
  | .split origin marker _ => insertPhysical texts origin [boundary origin.1 marker]
  | .merge _ _ => some texts

def coreStep (state : State) (command : NotionCoreSpec.Command) : Option State := do
  let doc ← NotionCoreSpec.step state.document command
  let texts ← coreTexts state.texts command
  pure ⟨doc,texts⟩

def coreBatch : State → List NotionCoreSpec.Command → Option State
  | state,[] => some state
  | state,command :: rest => do coreBatch (← coreStep state command) rest

def resolveRegions (state : State) (regions : List Region) : Option (List (Nat × Range)) :=
  regions.mapM fun region => do
    let text ← state.texts region.instanceId
    let range ← resolveRegion text region
    pure (region.instanceId,range)

/-- Resolve all stable boundaries before changing any mark. Each participating
instance receives one union assignment with the same already-issued Boolean. -/
def format (state : State) (regions : List Region) (value : Bool) : Option State :=
  (resolveRegions state regions).map fun resolved =>
    {state with texts := (fun inst => (state.texts inst).map (fun text => paint text (resolved.filterMap (fun (i,r) => if i = inst then some r else none)) value))}

inductive Command where
  | core (commands : List NotionCoreSpec.Command)
  | format (regions : List Region) (value : Bool)
  deriving DecidableEq, Repr

def step (state : State) : Command → Option State
  | .core commands => coreBatch state commands
  | .format regions value => format state regions value

def execute : State → List Command → Option State
  | state,[] => some state
  | state,command :: rest => do execute (← step state command) rest

/-- Toggle is an issuance operation: inspect the complete selection once and
retain one Boolean in the command. Delivery never recomputes a toggle. -/
def issueFormat (state : State) (targets : List Address) (regions : List Region) : Option Command := do
  let marks ← targets.mapM (readAt state)
  pure (.format regions (!(marks.all id)))

/-- The history language invokes direct state transitions, with one update per
whole command/batch. Queries expose current marks and may report malformed
physical/display state via none. -/
def machine : Sal.MRDTs.Paper1.HistoryMachine Command Unit (Option (List (Nat × List RichChar))) where
  State := State
  initial := {}
  transition state label next := match label with
    | .update command => step state command = some next
    | .query _ answer => next = state ∧ answer = render state

def spec := machine.toSpec

@[simp] theorem format_document {state next : State} {regions : List Region} {value : Bool}
    (h : format state regions value = some next) : next.document = state.document := by
  cases hresolved : resolveRegions state regions with
  | none => simp [format,hresolved] at h
  | some resolved =>
    simp only [format,hresolved,Option.map_some,Option.some.injEq] at h
    have hh := congrArg State.document h
    exact hh.symm

@[simp] theorem coreStep_document {state next : State} {command : NotionCoreSpec.Command}
    (h : coreStep state command = some next) :
    NotionCoreSpec.step state.document command = some next.document := by
  unfold coreStep at h
  cases hd : NotionCoreSpec.step state.document command with
  | none => simp [hd] at h
  | some doc =>
    cases ht : coreTexts state.texts command with
    | none => simp [hd,ht] at h
    | some texts =>
      simp [hd,ht] at h
      exact congrArg (fun s : State => some s.document) h

end Sal.MRDTs.Instances.NotionCoreRichSequential
