import Sal.MRDTs.Instances.NotionCoreFormattingSpec
import Sal.MRDTs.Instances.NotionCorePhysicalReplay

/-!
Independent atomic-toggle oracle for the multi-segment priority question.

The candidate rich protocol must make each displayed selection one atomic
toggle, even when its physical maximal-run planner emits several intervals.
The falsifier uses two concurrent toggles with intersecting selections and
opposite verdicts. If different intervals of one toggle win on different
parts of that intersection, neither atomic ordering can explain the result.

This module proves the independent side of that obstruction. It does not
assume that arbitrary selected identity lists are valid source requests.
A separate source witness must establish actual displayed positional
selections, honest IDs and clocks, emitted batches, and the fractured read.

All five character identities come from the real bootstrap address encoding.
Document shape is arbitrary here: deletion and insertion do not occur in the
two-toggle oracle, while split and merge only move the retained identities.
The source witness must show that all five identities remain displayed.
-/
namespace Sal.MRDTs.Instances.NotionCoreFormattingAtomicSpec

open NotionCoreSpec (Address Document)
open NotionCoreFormattingSpec (State plain assign toggle)

def address (counter : Nat) : Address :=
  NotionCorePhysicalReplay.address 0 ⟨counter, [65]⟩

def addresses : List Address := [address 1, address 2, address 3, address 4, address 5]
def targetsA : List Address := [address 1, address 2, address 4, address 5]
def targetsB : List Address := [address 2, address 3, address 4]

/-- Initially only b,c,d are bold. -/
def initial (document : Document) : State := assign (plain document) targetsB true

def flags (state : State) : List Bool := addresses.map state.bold

inductive Event where
  | a
  | b
  deriving DecidableEq, Repr

def step (state : State) : Event → State
  | .a => toggle state targetsA
  | .b => toggle state targetsB

def execute : State → List Event → State
  | state, [] => state
  | state, event :: rest => execute (step state event) rest

/-- Shared source initial observation, with both selected verdicts forced by
the global all-bold rule rather than supplied as independent Boolean inputs. -/
theorem initial_and_verdict_control (document : Document) :
    flags (initial document) = [false, true, true, true, false] ∧
    NotionCoreFormattingSpec.toggleValue (initial document) targetsA = true ∧
    NotionCoreFormattingSpec.toggleValue (initial document) targetsB = false ∧
    NotionCoreFormattingSpec.toggleValue (initial document) targetsA ≠
      NotionCoreFormattingSpec.toggleValue (initial document) targetsB := by
  change flags (initial []) = _ ∧
    NotionCoreFormattingSpec.toggleValue (initial []) targetsA = _ ∧
    NotionCoreFormattingSpec.toggleValue (initial []) targetsB = _ ∧
    NotionCoreFormattingSpec.toggleValue (initial []) targetsA ≠
      NotionCoreFormattingSpec.toggleValue (initial []) targetsB
  decide +kernel

/-- A then B removes bold from their whole intersection, including d. -/
theorem a_then_b_control (document : Document) :
    flags (execute (initial document) [.a, .b]) = [true, false, false, false, true] ∧
    flags (execute (initial document) [.a, .b]) ≠ [true, false, false, true, true] := by
  change flags (execute (initial []) [.a, .b]) = _ ∧ flags (execute (initial []) [.a, .b]) ≠ _
  decide +kernel

/-- B then A adds bold to their whole intersection, including b. -/
theorem b_then_a_control (document : Document) :
    flags (execute (initial document) [.b, .a]) = [true, true, false, true, true] ∧
    flags (execute (initial document) [.b, .a]) ≠ [true, false, false, true, true] := by
  change flags (execute (initial []) [.b, .a]) = _ ∧ flags (execute (initial []) [.b, .a]) ≠ _
  decide +kernel

theorem two_event_orders (events : List Event) (permutation : events.Perm [.a, .b]) :
    events = [.a, .b] ∨ events = [.b, .a] := by
  obtain ⟨first, second, rfl⟩ := List.length_eq_two.mp (by simpa using permutation.length_eq)
  cases first <;> cases second
  · have member := permutation.mem_iff.mpr (show Event.b ∈ [.a, .b] from by simp)
    simp at member
  · exact Or.inl rfl
  · exact Or.inr rfl
  · have member := permutation.mem_iff.mpr (show Event.a ∈ [.a, .b] from by simp)
    simp at member

/-- Every atomic toggle assigns one verdict to its entire selection. -/
theorem toggle_uniform_on_selection (state : State) (targets : List Address)
    (left right : Address) (leftIn : left ∈ targets) (rightIn : right ∈ targets) :
    (toggle state targets).bold left = (toggle state targets).bold right := by
  simp [toggle, leftIn, rightIn]

/-- Both toggles select b and d, so whichever commits last must assign them
the same verdict. This argument is independent of the initial marks and of
how either toggle decides that verdict. -/
theorem serial_intersection_uniform (state : State) (events : List Event)
    (permutation : events.Perm [.a, .b]) :
    (execute state events).bold (address 2) = (execute state events).bold (address 4) := by
  rcases two_event_orders events permutation with rfl | rfl
  · exact toggle_uniform_on_selection (toggle state targetsA) targetsB _ _ (by decide) (by decide)
  · exact toggle_uniform_on_selection (toggle state targetsB) targetsA _ _ (by decide) (by decide)

/-- A fractured b/d read cannot arise from either atomic ordering, for any
starting document or mark map. -/
theorem no_atomic_serialization_from_any (state : State) (events : List Event)
    (permutation : events.Perm [.a, .b]) :
    flags (execute state events) ≠ [true, false, false, true, true] := by
  intro agrees
  have second := congrArg (fun xs : List Bool => xs[1]?) agrees
  have fourth := congrArg (fun xs : List Bool => xs[3]?) agrees
  simp only [flags, addresses, List.map_cons, List.map_nil, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.some.injEq] at second fourth
  have equal := serial_intersection_uniform state events permutation
  rw [second, fourth] at equal
  cases equal

/-- No permutation containing each complete toggle once produces a fractured
intersection. This is stronger than merely checking two named schedules:
the theorem quantifies over every serial witness for these two events. -/
theorem no_atomic_serialization (document : Document) (events : List Event)
    (permutation : events.Perm [.a, .b]) :
    flags (execute (initial document) events) ≠ [true, false, false, true, true] := by
  rcases two_event_orders events permutation with rfl | rfl
  · exact (a_then_b_control document).2
  · exact (b_then_a_control document).2

/-- Equivalent existential form for a source refinement counterexample. -/
theorem no_atomic_witness (document : Document) :
    ¬ ∃ events : List Event, events.Perm [.a, .b] ∧
      flags (execute (initial document) events) = [true, false, false, true, true] := by
  rintro ⟨events, permutation, agrees⟩
  exact no_atomic_serialization document events permutation agrees

/-! Whole-history necessary semantics, including the initial b,c,d toggle.
`reshape` overapproximates every interleaving of empty-block creation, splitting
and corrected merging: it permits an arbitrary new document shape in one
step. These operations introduce no new visible character and preserve the
marks of the existing b,d identities. No insertion-inheritance rule is assumed.
-/

inductive FormatEvent where
  | initialMark
  | a
  | b
  deriving DecidableEq, Repr

def formatTargets : FormatEvent → List Address
  | .initialMark | .b => targetsB
  | .a => targetsA

inductive HistoryEvent where
  | format (event : FormatEvent)
  | prepared (event : FormatEvent) (value : Bool)
  | reshape (document : Document)

def historyStep (state : State) : HistoryEvent → State
  | .format event => toggle state (formatTargets event)
  | .prepared event value => assign state (formatTargets event) value
  | .reshape document => {state with document := document}

def history : State → List HistoryEvent → State
  | state, [] => state
  | state, event :: rest => history (historyStep state event) rest

def formatEvents : List HistoryEvent → List FormatEvent
  | [] => []
  | .format event :: rest => event :: formatEvents rest
  | .prepared event _ :: rest => event :: formatEvents rest
  | .reshape _ :: rest => formatEvents rest

def IntersectionUniform (state : State) : Prop :=
  state.bold (address 2) = state.bold (address 4)

/-- The shared b,d verdict is a semantic invariant of each atomic format.
This remains true when a mixed selection changes the toggle's verdict. -/
theorem format_uniform (state : State) (event : FormatEvent) :
    IntersectionUniform (toggle state (formatTargets event)) := by
  apply toggle_uniform_on_selection
  · cases event <;> decide
  · cases event <;> decide

theorem historyStep_uniform (state : State) (event : HistoryEvent)
    (before : IntersectionUniform state) : IntersectionUniform (historyStep state event) := by
  cases event with
  | format event => exact format_uniform state event
  | prepared event value =>
    have leftIn : address 2 ∈ formatTargets event := by cases event <;> decide
    have rightIn : address 4 ∈ formatTargets event := by cases event <;> decide
    simp [historyStep, IntersectionUniform, leftIn, rightIn]
  | reshape document => exact before

/-- Arbitrary core shape changes may occur before, between or after formats.
Every ordering of all three format events preserves b,d equality. -/
theorem history_uniform (state : State) (events : List HistoryEvent)
    (before : IntersectionUniform state) : IntersectionUniform (history state events) := by
  induction events generalizing state with
  | nil => exact before
  | cons event rest ih => exact ih _ (historyStep_uniform state event before)

theorem uniform_excludes_fracture (state : State) (uniform : IntersectionUniform state) :
    flags state ≠ [true, false, false, true, true] := by
  intro agrees
  have second := congrArg (fun xs : List Bool => xs[1]?) agrees
  have fourth := congrArg (fun xs : List Bool => xs[3]?) agrees
  simp only [flags, addresses, List.map_cons, List.map_nil, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.some.injEq] at second fourth
  unfold IntersectionUniform at uniform
  rw [second, fourth] at uniform
  cases uniform

/-- This is stronger than refuting two suffix orderings from an assumed
formatted base. It starts all-plain, includes the initial marking event, and
permits arbitrary interleaved shape changes. Even extra repetitions of these
three format kinds cannot produce the fractured source observation. `prepared`
also permits any issuer-chosen verdict, rather than recomputing a toggle from
the serial prefix; the invariant covers both interpretations. -/
theorem no_plain_history (document : Document) (events : List HistoryEvent) :
    flags (history (plain document) events) ≠ [true, false, false, true, true] :=
  uniform_excludes_fracture _ (history_uniform _ events rfl)

/-- The exact whole-update permutation shape needed by a serial witness.
All six orders of initialMark,A,B and every shape interleaving are excluded. -/
theorem no_three_event_serialization (document : Document) (events : List HistoryEvent)
    (_permutation : (formatEvents events).Perm [.initialMark, .a, .b]) :
    flags (history (plain document) events) ≠ [true, false, false, true, true] :=
  no_plain_history document events

/-- A valid serial history exists and differs from the fractured read, so the
negative result is not caused by rejecting every history or by stuckness. -/
private def fiveVisible : Document :=
  [⟨0, 0, [NotionCoreSpec.root 0, ⟨address 1, 97, true⟩, ⟨address 2, 98, true⟩,
    ⟨address 3, 99, true⟩, ⟨address 4, 100, true⟩, ⟨address 5, 101, true⟩], true⟩]

private def movedVisible : Document :=
  [⟨0, 0, [NotionCoreSpec.root 0, ⟨address 1, 97, true⟩, ⟨address 2, 98, true⟩,
    ⟨address 4, 100, true⟩, ⟨address 5, 101, true⟩], true⟩,
   ⟨1, 1, [NotionCoreSpec.root 1, ⟨address 3, 99, true⟩], true⟩]

theorem whole_history_control :
    flags (history (plain fiveVisible) [.format .initialMark, .reshape movedVisible, .format .a, .format .b]) =
      [true, false, false, false, true] ∧
    flags (history (plain fiveVisible) [.format .a, .format .initialMark, .reshape movedVisible, .format .b]) =
      [true, false, false, false, true] ∧
    flags (history (plain fiveVisible) [.format .initialMark, .reshape movedVisible, .format .a, .format .b]) ≠
      [true, false, false, true, true] := by decide +kernel

/-- Fixed issuer verdicts retain the same atomic intersection invariant on
five visible characters, through the actual final abde|c display shape. -/
theorem prepared_history_control :
    flags (history (plain fiveVisible)
      [.prepared .initialMark true, .reshape movedVisible, .prepared .a true, .prepared .b false]) =
      [true, false, false, false, true] ∧
    flags (history (plain fiveVisible)
      [.prepared .initialMark true, .reshape movedVisible, .prepared .a true, .prepared .b false]) ≠
      [true, false, false, true, true] ∧
    NotionCoreSpec.view movedVisible = [(0, [97, 98, 100, 101]), (1, [99])] ∧
    NotionCoreSpec.view movedVisible ≠ [(0, [97, 98]), (1, [99, 100, 101])] := by decide +kernel

#print axioms initial_and_verdict_control
#print axioms no_atomic_serialization
#print axioms no_atomic_serialization_from_any
#print axioms no_atomic_witness
#print axioms history_uniform
#print axioms no_three_event_serialization
#print axioms whole_history_control
#print axioms prepared_history_control

end Sal.MRDTs.Instances.NotionCoreFormattingAtomicSpec
