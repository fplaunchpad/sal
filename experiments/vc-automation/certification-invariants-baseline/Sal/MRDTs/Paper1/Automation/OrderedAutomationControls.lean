import Sal.MRDTs.Paper1.Automation.AutomatedRGA
import Sal.MRDTs.Paper1.Automation.OrderedInputDerivation
import Sal.MRDTs.Paper1.Automation.GenericLexOrder
import Sal.MRDTs.Paper1.Automation.GenericPrefixCodes

/-! Independent controls for ordered derivation and preservation. The eight
Type-valued kit maps are pinned by kernel definitional equality to their
ffec6e9 meanings; changing proof fields cannot discharge these equalities. -/
namespace Sal.MRDTs.Paper1.Automation.OrderedAutomationControls
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.EmbedRGA
open Instances.EmbedRGA
open OrderedRecords
set_option linter.unusedTactic false
variable (Γ : OrderedPrefixCode)

/- Negative controls must reject a false obligation, not exhaust resources. -/
open Lean Elab Tactic in
elab "reject_ordered_derivation " body:tacticSeq : tactic => do
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
      throwError "negative ordered control exhausted resources: {diagnostic}"
    pure (some diagnostic)
  saved.restore
  match rejected with
  | none => throwError "negative ordered control unexpectedly accepted the derivation"
  | some diagnostic => logInfo m!"ORDERED_REJECT {diagnostic}"

example : (AutomatedRGA.Embedded.kit (α := Nat) Γ).carrier = List.toFinset := by rfl
example : (AutomatedRGA.Embedded.kit (α := Nat) Γ).id = Prod.fst := by rfl
example : (AutomatedRGA.Embedded.kit (α := Nat) Γ).Key = List Nat := by rfl
example : (AutomatedRGA.Embedded.kit (α := Nat) Γ).key =
    (fun p => key p.2.2) := by rfl
example : (AutomatedRGA.Embedded.kit (α := Nat) Γ).insertion = eIsIns := by rfl
example : (AutomatedRGA.Embedded.kit (α := Nat) Γ).written = eRecOf Γ := by rfl
example : (AutomatedRGA.Embedded.kit (α := Nat) Γ).target =
    (fun e n => e.2.2 = .del n) := by rfl
example : (AutomatedRGA.Embedded.kit (α := Nat) Γ).ordered = ESorted := by rfl

/- Construct a fresh kit from the data description, never the cached kit. -/
set_option maxHeartbeats 2000000 in
def freshKit : Kit (E Γ Nat) (ERec Nat) := by
  derive_ordered_kit (AutomatedRGA.Embedded.description Γ) unfolding
    [AutomatedRGA.Embedded.description, E, eUpdate, eIds, eIsIns, eRecOf, eCoord, ESorted, eMerge]

#print axioms freshKit

/- A description with a constant identifier contradicts written_id at time 1.
The negative does not depend on a cached correctness theorem or replay premise. -/
def falseDescription : Description (E Γ Nat) (ERec Nat) :=
  { AutomatedRGA.Embedded.description Γ with id := fun _ => 0 }

def witnessEvent : Op (EOp Nat) := (1, 0, .del 0)

example : (falseDescription Γ).id ((falseDescription Γ).written witnessEvent) ≠
    witnessEvent.1 := by change (0 : Nat) ≠ 1; decide

set_option maxHeartbeats 2000000 in
example : True := by
  reject_ordered_derivation
    have falseKit : Kit (E Γ Nat) (ERec Nat) := by
      derive_ordered_kit (falseDescription Γ) unfolding
        [falseDescription, AutomatedRGA.Embedded.description, E, eUpdate, eIds, eIsIns, eRecOf, eCoord, ESorted, eMerge]
  trivial

/- A nonexistent description cannot be replaced by a registered datatype kit. -/
set_option maxHeartbeats 2000000 in
example : True := by
  reject_ordered_derivation
    have missingKit : Kit (E Γ Nat) (ERec Nat) := by
      derive_ordered_kit missingOrderedDescription unfolding []
  trivial

/- Raw no-op merge and empty update are rejected by concrete finite cells.
The records and verdicts are hand chosen, independent of implementation eval. -/
def brokenUpdate : MRDTSig := { E Γ Nat with update := fun _ _ => [] }
def brokenMerge : MRDTSig := { E Γ Nat with merge := fun _ a _ => a }
def sample : ERec Nat := (7, 0, default)
def deletion : Op (EOp Nat) := (8, 0, .del 9)
def brokenUpdateDescription : Description (brokenUpdate Γ) (ERec Nat) where
  carrier := List.toFinset
  id := Prod.fst
  Key := List Nat
  key := fun p => key p.2.2
  insertion := eIsIns
  written := eRecOf Γ
  target := fun e n => e.2.2 = .del n
  ordered := ESorted
def brokenMergeDescription : Description (brokenMerge Γ) (ERec Nat) where
  carrier := List.toFinset
  id := Prod.fst
  Key := List Nat
  key := fun p => key p.2.2
  insertion := eIsIns
  written := eRecOf Γ
  target := fun e n => e.2.2 = .del n
  ordered := ESorted

example : ¬ List.Mem sample ((brokenUpdate Γ).update [sample] deletion) := by change ¬ List.Mem sample []; intro h; cases h
example : sample ∈ ([sample] : List (ERec Nat)) ∧ ¬deletion.2.2 = .del sample.1 := by
  simp [sample, deletion]
example : ¬ List.Mem sample ((brokenMerge Γ).merge [] [] [sample]) := by change ¬ List.Mem sample []; intro h; cases h
example : Certified.cell (sample ∈ ([] : List (ERec Nat)))
    (sample ∈ ([] : List (ERec Nat))) (sample ∈ [sample]) := by simp [Certified.cell]

set_option maxHeartbeats 2000000 in
example : True := by
  reject_ordered_derivation
    have wrong : Kit (brokenUpdate Γ) (ERec Nat) := by
      derive_ordered_kit (brokenUpdateDescription Γ) unfolding
        [brokenUpdateDescription, brokenUpdate, AutomatedRGA.Embedded.description, E, eUpdate, eIds, eIsIns, eRecOf, eCoord, ESorted, eMerge]
  trivial
set_option maxHeartbeats 2000000 in
example : True := by
  reject_ordered_derivation
    have wrong : Kit (brokenMerge Γ) (ERec Nat) := by
      derive_ordered_kit (brokenMergeDescription Γ) unfolding
        [brokenMergeDescription, brokenMerge, AutomatedRGA.Embedded.description, E, eUpdate, eIds, eIsIns, eRecOf, eCoord, ESorted, eMerge]
  trivial

/- A fresh Boolean comparator exercises the generic theorem independently of
RGA's comparator and coordinate representation. -/
def boolLex : List Bool → List Bool → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else boolLex as bs

def boolOrder : OrderedLists.Order (id : List Bool → List Bool) boolLex :=
  OrderedLists.orderOfComparator boolLex rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ _ => rfl) id

example : boolLex [false] [true] = true := by decide
example : boolLex [true] [false] ≠ true := by decide
example : OrderedLists.Sorted boolLex
    (OrderedLists.insert boolLex [true] [[false]]) := by
  exact OrderedLists.insert_sorted boolOrder _ _ (by simp [OrderedLists.Sorted])
    (by intro x hx; simp only [List.mem_singleton] at hx; subst x; decide)

def brokenBoolLex : List Bool → List Bool → Bool
  | [], [] => true
  | xs, ys => boolLex xs ys

example : brokenBoolLex [] [] ≠ false := by decide
example : True := by
  fail_if_success
    have wrong : OrderedLists.Order (id : List Bool → List Bool) brokenBoolLex := by
      exact OrderedLists.orderOfComparator brokenBoolLex (by rfl)
        (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl) id
  trivial

/- Prefix freedom on a one-token domain does not exclude an empty codeword.
The nonempty field is load bearing for the generic injection theorem. -/
example : ∀ a b : Unit, a ≠ b → ¬([] : List Bool) <+: [] := by
  intro a b ne; exact (ne (Subsingleton.elim a b)).elim
example : PrefixCodes.encode (fun _ : Unit => ([] : List Bool)) [] =
    PrefixCodes.encode (fun _ : Unit => ([] : List Bool)) [()] := by rfl
example : ([] : List Unit) ≠ [()] := by decide
example : ¬ PrefixCodes.Code (fun _ : Unit => True) (fun _ => ([] : List Bool)) := by
  intro code; exact code.nonempty () trivial rfl

example : ¬ PrefixCodes.delimiter true false 0 <+: PrefixCodes.delimiter true false 1 := by decide
example : PrefixCodes.delimiter true true 0 <+: PrefixCodes.delimiter true true 1 := by decide

end Sal.MRDTs.Paper1.Automation.OrderedAutomationControls
