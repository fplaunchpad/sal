import Sal.MRDTs.Framework.GuardedStateProjection
import Sal.MRDTs.Framework.GuardedProjectionAutomation
import Sal.MRDTs.Paper1.GuardedProjectionHistory
import Sal.MRDTs.Paper1.ORSetEventSpec

/-! Independent nonempty toy trace; false invariant and constant projection
must both fail an interface obligation. Expected values are hand-derived. -/
namespace Sal.MRDTs.Paper1.Automation.GuardedStateProjectionControls
open Foundation

open Lean Elab Tactic in
elab "reject_guarded_projection " body:tacticSeq : tactic => do
  let saved ← saveState
  let rejected ← try
    withoutRecover <| Lean.Elab.Term.withoutErrToSorry <| evalTactic body
    pure (none : Option String)
  catch error =>
    let mut diagnostic ← error.toMessageData.toString
    for message in (← Lean.Core.getMessageLog).toList do
      if message.severity == .error then
        diagnostic := diagnostic ++ "\n" ++ (← message.data.toString)
    if (diagnostic.splitOn "heartbeats").length > 1 ∨
        (diagnostic.splitOn "timeout").length > 1 ∨
        (diagnostic.splitOn "maximum recursion depth").length > 1 then
      throwError "negative guarded projection control exhausted resources: {diagnostic}"
    if (diagnostic.splitOn "unsupportedSyntax").length > 1 ∨
        (diagnostic.splitOn "unsupported syntax").length > 1 then
      throwError "negative control hit unsupported syntax: {diagnostic}"
    if (diagnostic.splitOn "unsolved goals").length == 1 ∧
        (diagnostic.splitOn "simp_all made no progress").length == 1 then
      throwError "negative control failed for a reason other than unsolved false goal: {diagnostic}"
    pure (some diagnostic)
  saved.restore
  match rejected with
  | none => throwError "negative guarded projection control unexpectedly accepted the derivation"
  | some diagnostic => logInfo m!"GUARDED_PROJECTION_REJECT {diagnostic}"


abbrev counter : MRDTSig where
  State := Int
  dec_state := inferInstance
  init := 0
  AppOp := Unit
  dec_op := inferInstance
  Query := Unit
  Value := Int
  update n _ := if n < 0 then 0 else n + 1
  merge _ a b := max a b
  query n _ := n

abbrev specification : SequentialSpec counter where
  State := Int
  init := 0
  step n _ := n + 1
  Legal _ := True
  query n _ := n

def projection : GuardedStateProjection counter specification where
  Inv _ n := 0 ≤ n
  project := id
  prefix_closed _ _ _ := True.intro
  inv_initial := by change (0 : Int) ≤ 0; omega
  inv_update _ n _ inv _ := by
    change 0 ≤ n at inv
    change 0 ≤ if n < 0 then 0 else n + 1
    rw [if_neg (not_lt.mpr inv)]
    have hn : (0 : Int) ≤ n := inv
    change (0 : Int) ≤ n + 1
    omega
  initial := rfl
  update _ n _ inv _ := by simp [counter, specification, not_lt.mpr inv]
  observes _ _ _ _ := rfl

def events : List (Op Unit) := [(1, 0, ()), (2, 0, ())]

example : counter.query (applySeq counter.toUpdateSig counter.init events) () = (2 : Int) := by
  exact projection.query_agrees events True.intro ()
example : counter.query (applySeq counter.toUpdateSig counter.init events) () ≠ (0 : Int) := by decide

example : ¬ (∃ H : GuardedStateProjection counter specification,
    ∀ pre s, H.Inv pre s ↔ False) := by
  rintro ⟨H, bad⟩
  exact (bad [] counter.init).mp H.inv_initial

example : ¬ (∀ (e : Op Unit), (0 : Int) = specification.step 0 e) := by
  intro h
  have bad := h (1, 0, ())
  contradiction

example : projection.Inv events (applySeq counter.toUpdateSig counter.init events) :=
  projection.run_invariant events True.intro

example : counter.update (-2) (1, 0, ()) = 0 := by decide
example : counter.update (-2) (1, 0, ()) ≠ specification.step (-2) (1, 0, ()) := by decide
example : ¬ (∀ n e, counter.update n e = specification.step n e) := by
  intro h
  have bad := h (-2) (1, 0, ())
  contradiction

example (n : Int) (nonnegative : 0 ≤ n) :
    (if n < 0 then (0 : Int) else n + 1) = n + 1 := by
  guarded_projection_step [] using [if_neg, not_lt.mpr]

example : (0 : Int) ≠ 1 := by decide
example : True := by
  reject_guarded_projection
    have : (0 : Int) = 1 := by
      guarded_projection_step [] using []
  trivial

noncomputable def ordinarySetProjection :=
  (ORSet.EventSpec.projectionDescription (α := Nat)).toGuarded

def setEvents : List (Op (ORSet.Update Nat)) :=
  [(1, 0, .add 7)]

example : (ORSet.D Nat).query
    (applySeq (ORSet.D Nat).toUpdateSig (ORSet.D Nat).init setEvents) (7 : Nat) = true := by
  exact ordinarySetProjection.query_agrees setEvents True.intro (7 : Nat)

example : (ORSet.D Nat).query
    (applySeq (ORSet.D Nat).toUpdateSig (ORSet.D Nat).init setEvents) (7 : Nat) ≠ false := by
  rw [ordinarySetProjection.query_agrees setEvents True.intro (7 : Nat)]
  change (true : Bool) ≠ false
  decide

example (s : (ORSet.D Nat).State) : ordinarySetProjection.Rel s (ORSet.view s) := rfl

theorem successorNonnegative (n : Int) (h : 0 ≤ n) : 0 ≤ n + 1 := by omega
example (n : Int) (h : 0 ≤ n) : 0 ≤ (n + 1) + 1 := by
  guarded_projection_step [] using [successorNonnegative]

example (a : Finset Nat) (e : Nat) : a ∪ ({e} : Finset Nat) = insert e a := by
  guarded_projection_step [] using []

#print axioms projection
end Sal.MRDTs.Paper1.Automation.GuardedStateProjectionControls
