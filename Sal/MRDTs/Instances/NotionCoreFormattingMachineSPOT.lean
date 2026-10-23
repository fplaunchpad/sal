import Sal.MRDTs.Instances.NotionCoreFormattingMachine
import Sal.MRDTs.Instances.NotionCoreFormattingPlanner

/-! Concrete integration controls use actual core bootstrap/insert/erase/
split/corrected-merge transactions. Expected text and flags are hand-derived.
The controls establish execution behavior, not reachable rich protocol traces.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 2048
namespace Sal.MRDTs.Instances.NotionCoreFormattingMachineSPOT
open NotionCoreFormattingMachine
open NotionCoreFormattingSource (Anchor MarkOp)
open NotionCorePayload (Transaction)
open NotionRunAllocation (Id)

def a : Id := ⟨1,[65]⟩
def b : Id := ⟨2,[65]⟩
def x : Id := ⟨5,[66]⟩
def splitId : Id := ⟨4,[66]⟩
def created : Id := ⟨4,[67]⟩
def second : Nat := NotionCoreMachine.blockName (.issued created)
def splitBlock : Nat := NotionCoreMachine.blockName (.issued splitId)

def before (id : Id) : Anchor := ⟨.item id, .before⟩
def finish : Anchor := ⟨.finish,.before⟩
def mark (counter : Nat) (lo hi : Anchor) (value : Bool) : MarkOp :=
  ⟨⟨counter,[65]⟩,lo,hi,value⟩
def seed : Request := .edit (NotionCorePayload.bootstrap [97,98])
def boldA : Request := .format [(0,mark 3 (before a) (before b) true)]
def boldB : Request := .format [(0,mark 3 (before b) finish true)]
def insertX : Request := .edit ⟨x,.insert .initial .initial (.item a) [120]⟩
def divide : Request := .edit ⟨splitId,.split .initial .initial (.item a)⟩
def mergeBack : Request := .edit ⟨⟨6,[66]⟩,.merge (.issued splitId) .initial (some splitId)⟩

def view (state : State) : Option (List (Nat × List (Nat × Bool))) :=
  (render state).map fun document => document.map fun (bid, atoms) =>
    (bid, atoms.map fun atom => (atom.value,atom.bold))

def run (requests : List Request) : Option (List (Nat × List (Nat × Bool))) :=
  replay {} requests >>= view

/-- PASS+FAIL: actual factory payload creates a live ab block with unmarked
characters; formatting does not invent a hidden empty result or default bold. -/
theorem bootstrap_control :
    run [seed] = some [(0,[(97,false),(98,false)])] ∧
    run [seed] ≠ some [] ∧
    run [seed] ≠ some [(0,[(97,true),(98,true)])] := by decide +kernel

/-- PASS+FAIL: source anchors are resolved after the real insert transaction.
The new child immediately before the old end successor b inherits a's mark. -/
theorem boundary_insert_inheritance_control :
    run [seed,boldA,insertX] = some [(0,[(97,true),(120,true),(98,false)])] ∧
    run [seed,boldA,insertX] ≠ some [(0,[(97,true),(120,false),(98,false)])] ∧
    run [seed,boldB,insertX] = some [(0,[(97,false),(120,false),(98,true)])] ∧
    run [seed,boldB,insertX] ≠ some [(0,[(97,false),(120,true),(98,true)])] := by decide +kernel

/-- PASS+FAIL: deleting the marked start hides it but retains its anchor and
origin. Later insertion through that tombstone still inherits the interval. -/
theorem tombstone_anchor_control :
    run [seed,boldA,.edit ⟨⟨4,[65]⟩,.erase .initial [(.initial,[a])]⟩,insertX] =
      some [(0,[(120,true),(98,false)])] ∧
    run [seed,boldA,.edit ⟨⟨4,[65]⟩,.erase .initial [(.initial,[a])]⟩,insertX] ≠
      some [(0,[(97,true),(120,true),(98,false)])] ∧
    run [seed,boldA,.edit ⟨⟨4,[65]⟩,.erase .initial [(.initial,[a])]⟩,insertX] ≠
      some [(0,[(120,false),(98,false)])] := by decide +kernel

/-- PASS+FAIL: actual split routes b to the generated block. The rich lookup
uses the text instance identity, so b keeps its mark after display movement. -/
theorem split_preserves_control :
    run [seed,boldB,divide] = some [(0,[(97,false)]),(splitBlock,[(98,true)])] ∧
    run [seed,boldB,divide] ≠ some [(0,[(97,false)]),(splitBlock,[(98,false)])] ∧
    run [seed,boldB,divide] ≠ some [(0,[(97,false),(98,true)])] := by decide +kernel

/-- PASS+FAIL: actual corrected merge resolves the stop-marker anchor and
absorbs the split block. The source annotation remains on its instance; the
merged display reads both characters with the same flags. END is a different
merge anchor and leaves the two split blocks in place. -/
theorem corrected_merge_control :
    run [seed,boldB,divide,mergeBack] = some [(0,[(97,false),(98,true)])] ∧
    run [seed,boldB,divide,mergeBack] ≠ some [(0,[(97,false),(98,false)])] ∧
    run [seed,boldB,divide,mergeBack] ≠ some [(0,[(97,false)]),(splitBlock,[(98,true)])] ∧
    run [seed,boldB,divide,.edit ⟨⟨6,[66]⟩,.merge (.issued splitId) .initial none⟩] =
      some [(0,[(97,false)]),(splitBlock,[(98,true)])] := by decide +kernel

def otherText : Id := ⟨5,[67]⟩
def twoInstances : List Request :=
  [.edit (NotionCorePayload.bootstrap [97]),
   .edit ⟨created,.create (some .initial)⟩,
   .edit ⟨otherText,.insert (.issued created) (.issued created) .start [98]⟩]
def atomicBatch : List (Nat × MarkOp) :=
  [(0,mark 6 (before a) finish true), (second,mark 7 (before otherText) finish true)]

/-- PASS+FAIL: a complete multi-instance format batch becomes observable in
one applyRequest, while actual create/insert establish both editing instances.
The negative excludes installing only the first segment. -/
theorem atomic_multisegment_control :
    run (twoInstances ++ [.format atomicBatch]) =
      some [(0,[(97,true)]),(second,[(98,true)])] ∧
    run (twoInstances ++ [.format atomicBatch]) ≠
      some [(0,[(97,true)]),(second,[(98,false)])] ∧
    (replay {} (twoInstances ++ [.format atomicBatch])).map State.annotations = some atomicBatch ∧
    (replay {} (twoInstances ++ [.format atomicBatch])).map State.annotations ≠
      some [(0,mark 6 (before a) finish true)] := by decide +kernel

/-- PASS+FAIL: a later atomic removal may overlap an earlier source interval;
resolution remains per-item Lamport last-writer, rather than add-wins. -/
theorem atomic_remove_overlap_control :
    run [seed,.format [(0,mark 3 (before a) finish true)],
      .format [(0,mark 4 (before b) finish false)]] =
        some [(0,[(97,true),(98,false)])] ∧
    run [seed,.format [(0,mark 3 (before a) finish true)],
      .format [(0,mark 4 (before b) finish false)]] ≠
        some [(0,[(97,true),(98,true)])] := by decide +kernel

def selectedB : NotionCoreFormattingSource.Character := ⟨0,⟨b,.text 98 false⟩,false⟩

def planB (state : State) : List (Nat × MarkOp) :=
  NotionCoreFormattingPlanner.planToggle (instanceForest state) [0] [65] 3 [selectedB]

/-- PASS+FAIL: an actual candidate planner batch can be applied by this
interpreter. No independent selected-ID renderer stands in for source marks. -/
theorem planner_batch_control :
    (replay {} [seed] >>= fun state => applyRequest state (.format (planB state)) >>= view) =
      some [(0,[(97,false),(98,true)])] ∧
    (replay {} [seed] >>= fun state => applyRequest state (.format (planB state)) >>= view) ≠
      some [(0,[(97,true),(98,true)])] := by decide +kernel

def invalid : Request := .edit ⟨a,.insert .initial .initial .start [120]⟩

/-- PASS+FAIL: a conflicting real insert fails the entire request replay;
format batches do not hide the old interpreter's failure. -/
theorem failed_edit_control :
    replay {} [seed,boldB,invalid] = none ∧
    run [seed,boldB,invalid] = none ∧
    run [seed,boldB,invalid] ≠ some [(0,[(97,false),(98,true)])] := by decide +kernel

def malformed : State := ⟨{forest := [⟨0,NotionCoreSliceForest.freshTitle 0⟩],display := [0]},[]⟩

/-- PASS+FAIL: a missing instance makes the actual slice query fail. The rich
query propagates that failure instead of returning an empty successful block. -/
theorem malformed_query_control :
    render malformed = none ∧ NotionCoreMachine.render malformed.core = none ∧
    render malformed ≠ some [(0,[])] := by decide +kernel

#print axioms boundary_insert_inheritance_control
#print axioms tombstone_anchor_control
#print axioms split_preserves_control
#print axioms corrected_merge_control
#print axioms atomic_multisegment_control
#print axioms planner_batch_control
end Sal.MRDTs.Instances.NotionCoreFormattingMachineSPOT
