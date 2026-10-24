import Sal.MRDTs.Instances.NotionCoreRichSequentialDocument
import Sal.MRDTs.Instances.NotionCoreRichPayload
import Sal.MRDTs.Instances.NotionCoreMachineCommands

/-!
Static input translation into the independent rich-document specification.

Source IDs name cells and boundaries. They do not impose an order inside the
sequential specification, whose state contains no transaction log or priority.
Every source transaction remains one update. Unsupported endpoint forms are
rejected; the repaired positional compiler produces before-item/END only.
Failed implementation queries are not accepted as document observations.
-/
namespace Sal.MRDTs.Instances.NotionCoreRichSequentialInputs
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1
open NotionCoreRichPayload (Transaction Part)
open NotionCoreRichSequential (State Command Region RichChar)

abbrev View := List (Nat × List RichChar)

def endpoint (anchor : NotionCoreFormattingSource.Anchor) : Option NotionCoreRichSequential.Endpoint :=
  match anchor.endpoint,anchor.side with
  | .item id,.before => some (.before (NotionCorePhysicalReplay.markerKey id))
  | .finish,.before => some .finish
  | _,_ => none

def region (part : Part) : Option Region := do
  pure ⟨part.instanceId,← endpoint part.lower,← endpoint part.upper⟩

def command (transaction : Transaction) : Option Command :=
  match transaction.payload with
  | .edit payload => some (.core ((NotionCoreMachineCommands.commands ⟨transaction.id,payload⟩).map
      NotionCoreSourceDocument.Command.semantic))
  | .format parts value => (parts.mapM region).map (fun regions => .format regions value)

def segmentRegion (inst : Nat) (segment : NotionCoreFormattingPlanner.Segment) : Region :=
  ⟨inst,.before (NotionCorePhysicalReplay.markerKey segment.first.item.id),
    match segment.next with
    | none => .finish
    | some next => .before (NotionCorePhysicalReplay.markerKey next.item.id)⟩

private def segmentPart (inst : Nat) (segment : NotionCoreFormattingPlanner.Segment) : Part :=
  let operation := segment.operation ⟨0,[]⟩ false
  ⟨inst,operation.start,operation.finish⟩

/-- The actual maximal-run compiler always produces supported stable
boundaries. This conclusion is structural, not a guard supplied by a client. -/
theorem planned_regions (segments : List (Nat × NotionCoreFormattingPlanner.Segment)) :
    ((NotionCoreRichPayload.partsOf segments).mapM region) =
      some (segments.map fun (inst,segment) => segmentRegion inst segment) := by
  induction segments with
  | nil => rfl
  | cons located rest ih =>
    rcases located with ⟨inst,segment⟩
    change (segmentPart inst segment :: NotionCoreRichPayload.partsOf rest).mapM region =
        some (segmentRegion inst segment :: rest.map (fun (i,s) => segmentRegion i s))
    simp only [List.mapM_cons,ih]
    cases ending : segment.next <;>
      simp [segmentPart,NotionCoreFormattingPlanner.Segment.operation,
        region,endpoint,segmentRegion,ending]

theorem planned_command (id : NotionRunAllocation.Id) (value : Bool)
    (segments : List (Nat × NotionCoreFormattingPlanner.Segment)) :
    command ⟨id,.format (NotionCoreRichPayload.partsOf segments) value⟩ =
      some (.format (segments.map fun (inst,segment) => segmentRegion inst segment) value) := by
  simp only [command,planned_regions,Option.map_some]

def applyEvent (state : State) (event : Op Transaction) : Option State := do
  let selected ← command event.op
  NotionCoreRichSequential.step state selected

def execute (state : State) : List (Op Transaction) → Option State
  | [] => some state
  | event :: rest => do execute (← applyEvent state event) rest

def applyTransaction (state : State) (transaction : Transaction) : Option State := do
  NotionCoreRichSequential.step state (← command transaction)

def executeTransactions (state : State) : List Transaction → Option State
  | [] => some state
  | transaction :: rest => do executeTransactions (← applyTransaction state transaction) rest

theorem execute_payloads (state : State) (events : List (Op Transaction)) :
    execute state events = executeTransactions state (events.map Op.op) := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
    change (applyEvent state event >>= fun next => execute next rest) =
      (applyEvent state event >>= fun next => executeTransactions next (rest.map Op.op))
    congr 1
    funext next
    exact ih next

theorem executeTransactions_append (state : State) (left right : List Transaction) :
    executeTransactions state (left ++ right) =
      (executeTransactions state left >>= fun next => executeTransactions next right) := by
  induction left generalizing state with
  | nil => rfl
  | cons transaction rest ih =>
    simp only [List.cons_append,executeTransactions]
    cases one : applyTransaction state transaction <;> simp [ih]

theorem applyEvent_compiled (state : State) (event : Op Transaction) (selected : Command)
    (compiled : command event.op = some selected) :
    applyEvent state event = NotionCoreRichSequential.step state selected := by
  simp [applyEvent,compiled]

/-- Static label translation preserves the complete direct-state run. It
neither sorts the supplied events nor consults implementation replay. -/
theorem execute_compiled (state : State) (events : List (Op Transaction)) (commands : List Command)
    (compiled : (events.mapM fun event => command event.op) = some commands) :
    execute state events = NotionCoreRichSequential.execute state commands := by
  induction events generalizing state commands with
  | nil =>
    have empty : ([] : List Command) = commands := Option.some.inj compiled
    cases empty
    rfl
  | cons event rest ih =>
    cases selected : command event.op with
    | none => simp [List.mapM_cons,selected] at compiled
    | some selectedCommand =>
      cases remaining : rest.mapM (fun event => command event.op) with
      | none => simp [List.mapM_cons,selected,remaining] at compiled
      | some remainingCommands =>
        have same : selectedCommand :: remainingCommands = commands := by
          simpa [List.mapM_cons,selected,remaining] using compiled
        subst commands
        simp only [execute,applyEvent_compiled state event selectedCommand selected,
          NotionCoreRichSequential.execute]
        cases one : NotionCoreRichSequential.step state selectedCommand with
        | none => rfl
        | some next => simpa using ih next remainingCommands remaining

def machine : HistoryMachine (Op Transaction) Unit (Option View) where
  State := State
  initial := {}
  transition before label after := match label with
    | .update event => applyEvent before event = some after
    | .query _ (some answer) => after = before ∧ NotionCoreRichSequential.render before = some answer
    | .query _ none => False

def spec : HistorySpec (Op Transaction) Unit (Option View) := machine.toSpec

def labels (events : List (Op Transaction)) : List (SeqLabel (Op Transaction) Unit (Option View)) :=
  events.map SeqLabel.update

theorem update_runs_iff (before after : State) (events : List (Op Transaction)) :
    Runs machine.transition before (labels events) after ↔ execute before events = some after := by
  induction events generalizing before with
  | nil =>
    constructor
    · intro run; cases run; rfl
    · intro run
      simp only [execute,Option.some.injEq] at run
      subst after
      exact .nil _
  | cons event events ih =>
    constructor
    · intro run
      cases run with
      | cons one rest =>
        change applyEvent before event = some _ at one
        simp only [execute,one,Option.bind_some]
        exact (ih _).mp rest
    · intro run
      simp only [execute] at run
      cases one : applyEvent before event with
      | none => simp [one] at run
      | some next =>
        simp only [one,Option.bind_some] at run
        exact .cons one ((ih next).mpr run)

/-- Query agreement is with the state reached by those same whole events.
The existential cannot choose a separately replayed implementation state. -/
theorem updates_query_iff (events : List (Op Transaction)) (answer : View) :
    spec.admits (labels events ++ [.query () (some answer)]) ↔
      ∃ final, execute {} events = some final ∧ NotionCoreRichSequential.render final = some answer := by
  constructor
  · rintro ⟨final,history⟩
    obtain ⟨middle,priorRun,query⟩ := history.split (labels events) [.query () (some answer)]
    cases query with
    | cons observed finish => exact ⟨middle,(update_runs_iff {} middle events).mp priorRun,observed.2⟩
  · rintro ⟨final,executed,observed⟩
    exact ⟨final,((update_runs_iff {} final events).mpr executed).append
      (.cons ⟨rfl,observed⟩ (.nil _))⟩

theorem rejects_none (events : List (Op Transaction)) :
    ¬ spec.admits (labels events ++ [.query () none]) := by
  rintro ⟨final,history⟩
  obtain ⟨middle,priorRun,query⟩ := history.split (labels events) [.query () none]
  cases query with
  | cons observed finish => exact observed

/-- The outer framework timestamp/replica is not a hidden spec counter.
Only the explicit application transaction supplies cell and boundary names. -/
theorem same_payload_step (state : State) (left right : Op Transaction)
    (same : left.op = right.op) : applyEvent state left = applyEvent state right := by
  simp only [applyEvent,same]

theorem query_unique (events : List (Op Transaction)) (left right : View)
    (acceptedLeft : spec.admits (labels events ++ [.query () (some left)]))
    (acceptedRight : spec.admits (labels events ++ [.query () (some right)])) : left = right := by
  obtain ⟨before,executed,observed⟩ := (updates_query_iff events left).mp acceptedLeft
  obtain ⟨after,executedAfter,observedAfter⟩ := (updates_query_iff events right).mp acceptedRight
  rw [executed] at executedAfter
  cases Option.some.inj executedAfter
  exact Option.some.inj (observed.symm.trans observedAfter)

namespace SPOT
private def id (counter : Nat) : NotionRunAllocation.Id := ⟨counter,[65]⟩
private def events : List (Op Transaction) :=
  [(1,0,⟨id 1,.edit (.bootstrap [97,98])⟩),
    (2,0,⟨id 3,.format [⟨0,⟨.item (id 1),.before⟩,⟨.finish,.before⟩⟩] true⟩)]
private def expected : View := [(0,[⟨NotionCorePhysicalReplay.address 0 (id 1),97,true⟩,
  ⟨NotionCorePhysicalReplay.address 0 (id 2),98,true⟩])]
private def rival : View := [(0,[⟨NotionCorePhysicalReplay.address 0 (id 1),97,false⟩,
  ⟨NotionCorePhysicalReplay.address 0 (id 2),98,false⟩])]

/-- PASS+FAIL: the source-label specification accepts a nonempty bold read
and rejects both the tempting plain answer and an implementation failure. -/
theorem nonempty_history :
    spec.admits (labels events ++ [.query () (some expected)]) ∧
    ¬ spec.admits (labels events ++ [.query () (some rival)]) ∧
    ¬ spec.admits (labels events ++ [.query () none]) := by
  have positive : spec.admits (labels events ++ [.query () (some expected)]) := by
    apply (updates_query_iff events expected).mpr
    exact ⟨(execute {} events).getD {},rfl,rfl⟩
  refine ⟨positive,?_,rejects_none events⟩
  intro negative
  have same := query_unique events expected rival positive negative
  have different : expected ≠ rival := by decide
  exact different same
end SPOT

#print axioms updates_query_iff
#print axioms SPOT.nonempty_history

end Sal.MRDTs.Instances.NotionCoreRichSequentialInputs
