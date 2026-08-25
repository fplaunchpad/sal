import Sal.MRDTs.Metatheory.Correctness

/-!
# Sequential-legality proof-oriented tests

These examples test the distinction between origin authorization and a legal
sequential witness.  They are intentionally smaller than any production
datatype.

Two consumers can each be authorized at an origin state where a resource is
enabled.  A merged event set contains both consumers, but no permutation of
the enable and two consume events is prefix-legal.  Therefore mint honesty
and internal replay cannot imply client-facing RA correctness by themselves.
-/

namespace Sal.MRDTs.Metatheory.ConditioningSPOT

open Sal.MRDTs.Foundation

inductive GateOp where
  | enable
  | consume
deriving DecidableEq

def gateUpdate (_ : Bool) (e : Op GateOp) : Bool :=
  match e.2.2 with
  | .enable => true
  | .consume => false

def Gate : MRDTSig where
  State := Bool
  dec_state := inferInstance
  init := false
  AppOp := GateOp
  dec_op := inferInstance
  Query := Unit
  Value := Bool
  update := gateUpdate
  query := fun s _ => s
  merge := fun _ a b => a || b

def gateLegalFrom : Bool → List (Op GateOp) → Prop
  | _, [] => True
  | _, (_, _, .enable) :: rest => gateLegalFrom true rest
  | available, (_, _, .consume) :: rest =>
      available = true ∧ gateLegalFrom false rest

def gateSpec : SequentialSpec Gate where
  State := Bool
  init := false
  step := gateUpdate
  Legal := gateLegalFrom false
  query := fun s _ => s

def enable : Op GateOp := (1, 0, .enable)
def consumeA : Op GateOp := (2, 1, .consume)
def consumeB : Op GateOp := (3, 2, .consume)

/-- PASS control: one authorized consumer has a legal sequential history. -/
example : gateSpec.Legal [enable, consumeA] := by
  simp [gateSpec, gateLegalFrom, enable, consumeA]

/-- Both consumers pass the same origin check on independent replicas. -/
example : gateLegalFrom true [consumeA] := by
  simp [gateLegalFrom, consumeA]

example : gateLegalFrom true [consumeB] := by
  simp [gateLegalFrom, consumeB]

/-- The six serializations of the three distinct events, listed independently
of the legality checker. -/
def mergedOrders : List (List (Op GateOp)) :=
  [[enable, consumeA, consumeB], [enable, consumeB, consumeA],
   [consumeA, enable, consumeB], [consumeA, consumeB, enable],
   [consumeB, enable, consumeA], [consumeB, consumeA, enable]]

/-- FAIL control: placing the two consumers together makes each of the six
serializations illegal.  This is the missing implication in the replay-only
theorem, checked independently of a production MRDT. -/
theorem no_legal_merged_order :
    ∀ π ∈ mergedOrders,
      ¬ gateSpec.Legal π := by
  simp [mergedOrders, gateSpec, gateLegalFrom, enable, consumeA, consumeB]

/-- The raw total transition system still replays the merged list. -/
example : applySeq Gate.toCRDTSig Gate.init [enable, consumeA, consumeB] = false := by
  decide

/-- Rejecting every nonempty history is not an acceptable positive control:
the valid one-consumer scenario above distinguishes the intended semantics
from this degenerate condition. -/
def rejectAll : SequentialSpec Gate where
  State := Bool
  init := false
  step := gateUpdate
  Legal := fun ops => ops = []
  query := fun s _ => s

example : ¬ rejectAll.Legal [enable] := by
  simp [rejectAll]

end Sal.MRDTs.Metatheory.ConditioningSPOT
