import Sal.MRDTs.Paper1.Automation.RepresentationAutomation

/-! Independent representation controls, with no concrete datatype imports.
The negative witnesses are hand-derived and accompanied by strict rejection
checks; exhausting a resource budget is never accepted as rejection evidence. -/
namespace Sal.MRDTs.Paper1.Automation.RepresentationAutomationControls
set_option linter.unusedTactic false

open Lean Elab Tactic in
elab "reject_representation " body:tacticSeq : tactic => do
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
      throwError "negative representation control exhausted resources: {diagnostic}"
    pure (some diagnostic)
  saved.restore
  match rejected with
  | none => throwError "negative representation control unexpectedly accepted the derivation"
  | some diagnostic => logInfo m!"REPRESENTATION_REJECT {diagnostic}"

variable {α : Type}

theorem set_survivors (base a b : Set α) :
    (a ∩ b) ∪ (a \ base) ∪ (b \ base) =
      (b ∩ a) ∪ (b \ base) ∪ (a \ base) := by
  mrdt_representation []

theorem finite_filter [DecidableEq α] (a b : Finset α) (keep : α → Prop) [DecidablePred keep] :
    (a ∪ b).filter keep = a.filter keep ∪ b.filter keep := by
  mrdt_representation []

theorem boolean_functions (a b : α → Bool) :
    (fun x => a x || (a x || b x)) = (fun x => b x || a x) := by
  mrdt_representation []

inductive Change (α : Type) where
  | credit (key : α) (amount : Int)
  | debit (key : α) (amount : Int)

def mapZero : (α → Int) × (α → Int) := (fun _ => 0, fun _ => 0)
def mapMerge (base a b : (α → Int) × (α → Int)) :=
  (fun x => a.1 x + b.1 x - base.1 x,
   fun x => a.2 x + b.2 x - base.2 x)
def bump [DecidableEq α] (f : α → Int) (key : α) (amount : Int) :=
  fun x => if x = key then f x + amount else f x
def mapUpdate [DecidableEq α] (s : (α → Int) × (α → Int)) : Change α → (α → Int) × (α → Int)
  | .credit key amount => (bump s.1 key amount, s.2)
  | .debit key amount => (s.1, bump s.2 key amount)

theorem map_causal [DecidableEq α] (s : (α → Int) × (α → Int)) (e : Change α) :
    mapMerge mapZero s (mapUpdate mapZero e) = mapUpdate s e := by
  mrdt_representation [mapMerge, mapZero, mapUpdate, bump]

theorem map_local [DecidableEq α] (l B t b : (α → Int) × (α → Int)) (e : Change α) :
    mapMerge l (mapMerge B t (mapUpdate B e)) b =
      mapMerge B (mapMerge l t b) (mapUpdate B e) := by
  mrdt_representation [mapMerge, mapUpdate, bump]

/- A left projection drops the independently chosen right-hand member. -/
example : ({0} : Finset Nat) ≠ ({0} ∪ {1}) := by decide
example : True := by
  reject_representation
    have falseProjection : ({0} : Finset Nat) = ({0} ∪ {1}) := by
      mrdt_representation []
  trivial

/- The affine merge subtracts its base once; adding it gives 9 instead of 5. -/
example : (3 : Int) + 4 - 2 ≠ 3 + 4 + 2 := by decide
example : True := by
  reject_representation
    have wrongArithmetic : (3 : Int) + 4 - 2 = 3 + 4 + 2 := by
      mrdt_representation []
  trivial

#print axioms set_survivors
#print axioms finite_filter
#print axioms boolean_functions
#print axioms map_causal
#print axioms map_local
end Sal.MRDTs.Paper1.Automation.RepresentationAutomationControls
