import Sal.MRDTs.Instances.NotionCoreAtomicFormattingMachine
import Sal.MRDTs.Instances.NotionCoreAtomicFormattingPlanner
import Sal.MRDTs.Instances.NotionCoreRichAtomicCounterexample

/-! Hand-derived paired controls for the shared-priority repair. The original
per-segment obstruction is imported and retained as a negative control.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 4096
namespace Sal.MRDTs.Instances.NotionCoreAtomicFormattingSPOT
open NotionCoreAtomicFormatting
open NotionCoreRichPayload (Part Transaction)
open NotionCoreFormattingSource (Anchor)
open NotionRunAllocation (Id)

def id (counter : Nat) (session : Nat := 65) : Id := ⟨counter,[session]⟩
def before (counter : Nat) : Anchor := ⟨.item (id counter),.before⟩
def finish : Anchor := ⟨.finish,.before⟩
def part (lower upper : Anchor) (inst : Nat := 0) : Part := ⟨inst,lower,upper⟩
def abcde : NotionCoreOriginTree.Forest := .cons
  (NotionCoreOriginTree.runTree (NotionCoreOriginTree.literal 1 97)
    [NotionCoreOriginTree.literal 2 98,NotionCoreOriginTree.literal 3 99,
      NotionCoreOriginTree.literal 4 100,NotionCoreOriginTree.literal 5 101]) .nil
def initialMark : Batch := Batch.ofFormat (id 6) [part (before 2) (before 5)] true
def add : Batch := Batch.ofFormat (id 10) [part (before 1) (before 3),part (before 4) finish] true
def remove : Batch := Batch.ofFormat (id 10 66) [part (before 2) (before 5)] false
def flags (batches : List Batch) : List Bool :=
  (List.range 5).map (fun index => resolveAt (fun _ => abcde) batches 0 index)

/-- PASS+FAIL: one whole priority wins across the intersection b,d. The
per-segment fracture 10011 is rejected, independently of input list order. -/
theorem shared_priority_control :
    flags [initialMark,add,remove] = [true,false,false,false,true] ∧
    flags [remove,initialMark,add] = [true,false,false,false,true] ∧
    flags [initialMark,add,remove] ≠ [true,false,false,true,true] ∧
    flags [initialMark,add,remove] ≠ [true,true,false,true,true] := by decide +kernel

/-- PASS+FAIL: distinct segment IDs remain allocated; they no longer provide
independent priorities that could split the winner of one atomic operation. -/
theorem distinct_segment_ids_control :
    add.segments.map Segment.id = [id 10,id 11] ∧
    add.priority = id 10 ∧
    (add.segments.map Segment.id).Nodup ∧
    add.segments.map Segment.id ≠ [id 10,id 10] := by decide +kernel

/-- PASS+FAIL: changing the transaction order changes the entire intersection
uniformly, including both b and d. It does not preserve the old fracture. -/
theorem opposite_winner_control :
    let laterAdd := Batch.ofFormat (id 11) [part (before 1) (before 3),part (before 4) finish] true
    flags [initialMark,remove,laterAdd] = [true,true,false,true,true] ∧
    flags [initialMark,remove,laterAdd] ≠ [true,false,false,false,true] ∧
    flags [initialMark,remove,laterAdd] ≠ [true,false,false,true,true] := by decide +kernel

/-- PASS+FAIL: left insertion affinity excludes the start gap; right affinity
includes the end gap. Character membership and gap membership are different. -/
theorem sticky_gap_control :
    let mark := Batch.ofFormat (id 6) [part (before 2) (before 3)] true
    (List.range 5).map (resolveAt (fun _ => abcde) [mark] 0) = [false,true,false,false,false] ∧
    (List.range 6).map (resolveGapAt (fun _ => abcde) [mark] 0) = [false,false,true,false,false,false] ∧
    (List.range 6).map (resolveGapAt (fun _ => abcde) [mark] 0) ≠ [false,true,true,false,false,false] ∧
    resolveGapAt (fun _ => abcde) [Batch.ofFormat (id 6) [part (before 5) finish] true] 0 5 = true := by decide +kernel

/-- PASS+FAIL: a shared verdict can cover multiple instances without allowing
the same numeric coordinate in an unrelated instance to inherit that mark. -/
theorem instance_guard_control :
    let mark := Batch.ofFormat (id 6) [part (before 1) (before 2) 0,part (before 4) finish 1] true
    (List.range 5).map (resolveAt (fun _ => abcde) [mark] 0) = [true,false,false,false,false] ∧
    (List.range 5).map (resolveAt (fun _ => abcde) [mark] 1) = [false,false,false,true,true] ∧
    (List.range 5).map (resolveAt (fun _ => abcde) [mark] 0) ≠ [true,false,false,true,true] := by decide +kernel

def formerTransactions : List Transaction := NotionCoreRichPayload.sort
  (NotionCoreRichNetwork.receivedTransactions NotionCoreRichAtomicCounterexample.final
    NotionCoreRichAtomicCounterexample.A)

def repairedFlags : Option (List Bool) :=
  (NotionCoreAtomicFormattingMachine.replay {} formerTransactions).map fun state =>
    NotionCoreFormattingAtomicSpec.addresses.map (NotionCoreAtomicFormattingMachine.boldAt state)

/-- PASS+FAIL: replaying the exact previously source-issued whole transactions
through the repaired interpreter fixes the complete split/merge/clock fixture.
The old evaluator still computes its preserved 10011 counterexample. -/
theorem full_fracture_repaired_control :
    NotionCoreRichAtomicCounterexample.flags NotionCoreRichAtomicCounterexample.final
      NotionCoreRichAtomicCounterexample.A = some [true,false,false,true,true] ∧
    repairedFlags = some [true,false,false,false,true] ∧
    repairedFlags ≠ some [true,false,false,true,true] ∧
    repairedFlags ≠ some [true,true,false,true,true] := by decide +kernel

def view (transactions : List Transaction) : Option (List (Nat × List (Nat × Bool))) :=
  (NotionCoreAtomicFormattingMachine.replay {} transactions >>= NotionCoreAtomicFormattingMachine.render).map
    (fun document => document.map fun (bid,atoms) =>
      (bid,atoms.map fun (atom : NotionCoreAtomicFormattingMachine.RichAtom) => (atom.value,atom.bold)))

def seed : Transaction := ⟨id 1,.edit (.bootstrap [97,98])⟩
def boldA : Transaction := ⟨id 3,.format [part (before 1) (before 2)] true⟩
def insertX : Transaction := ⟨id 5 66,.edit (.insert .initial .initial (.item (id 1)) [120])⟩
def splitId : Id := id 4 66
def splitBlock : Nat := NotionCoreMachine.blockName (.issued splitId)
def divide : Transaction := ⟨splitId,.edit (.split .initial .initial (.item (id 1)))⟩
def mergeBack : Transaction := ⟨id 6 66,.edit (.merge (.issued splitId) .initial (some splitId))⟩

/-- PASS+FAIL: actual editing-core insertion and tombstone semantics still
resolve dynamic boundaries, rather than caching the originally selected IDs. -/
theorem actual_inheritance_control :
    view [seed,boldA,insertX] = some [(0,[(97,true),(120,true),(98,false)])] ∧
    view [seed,boldA,insertX] ≠ some [(0,[(97,true),(120,false),(98,false)])] ∧
    view [seed,boldA,⟨id 4,.edit (.erase .initial [(.initial,[id 1])])⟩,insertX] =
      some [(0,[(120,true),(98,false)])] ∧
    view [seed,boldA,⟨id 4,.edit (.erase .initial [(.initial,[id 1])])⟩,insertX] ≠
      some [(0,[(120,false),(98,false)])] := by decide +kernel

/-- PASS+FAIL: actual split and corrected stop-marker merge preserve marks
while changing the displayed block structure. -/
theorem actual_structure_control :
    view [seed,boldA,divide] = some [(0,[(97,true)]),(splitBlock,[(98,false)])] ∧
    view [seed,boldA,divide] ≠ some [(0,[(97,true),(98,false)])] ∧
    view [seed,boldA,divide,mergeBack] = some [(0,[(97,true),(98,false)])] ∧
    view [seed,boldA,divide,mergeBack] ≠ some [(0,[(97,false),(98,false)])] := by decide +kernel

#print axioms full_fracture_repaired_control
#print axioms actual_inheritance_control
#print axioms actual_structure_control
end Sal.MRDTs.Instances.NotionCoreAtomicFormattingSPOT
