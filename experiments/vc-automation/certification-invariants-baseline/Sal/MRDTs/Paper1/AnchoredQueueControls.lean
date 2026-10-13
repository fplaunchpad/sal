import Sal.MRDTs.Paper1.AnchoredQueue

/-! Hand-derived PASS+FAIL controls. These computations specify the intended
queue values, never derive expected values by evaluating the implementation. -/
namespace Sal.MRDTs.Paper1.AnchoredQueue.Controls
open Foundation Instances.EmbedRGA

abbrev a : Event := (1,0,enq 10 0 [])
abbrev b : Event := (2,0,enq 20 1 [true,false])
abbrev c : Event := (3,1,enq 30 1 [true,false])
abbrev removeA : Event := (4,0,deq 1)
def singleton : State := Q.update Q.init a
def sameTail : State := Q.merge singleton (Q.update singleton b) (Q.update singleton c)

/-- Greater Lamport delta siblings precede smaller siblings, consistently
with the coordinate code. Both actual issuers observed the same tail. -/
theorem concurrent_same_tail :
    CanIssue b singleton ∧ CanIssue c singleton ∧
    Q.query sameTail () = [10,30,20] ∧
    Q.query sameTail () ≠ [10,20,30] ∧
    Q.merge singleton (Q.update singleton c) (Q.update singleton b) = sameTail := by
  try simp only [E]
  decide +kernel

/-- A removed singleton anchor survives in the enqueuer's carried coordinate;
the merged materialized state contains only the fresh live element. -/
theorem singleton_dequeue_enqueue :
    CanIssue removeA singleton ∧ CanIssue b singleton ∧
    Q.query (Q.merge singleton (Q.update singleton removeA) (Q.update singleton b)) () = [20] ∧
    Q.query (Q.merge singleton (Q.update singleton removeA) (Q.update singleton b)) () ≠ [] ∧
    (Q.merge singleton (Q.update singleton removeA) (Q.update singleton b)).length = 1 := by
  try simp only [E]
  decide +kernel

abbrev removeAgain : Event := (5,1,deq 1)
/-- Two original issuers may dequeue the same head. The second replay is
idempotent on an absent identity, but cannot be reissued from an empty head. -/
theorem duplicate_dequeues :
    CanIssue removeA singleton ∧ CanIssue removeAgain singleton ∧
    Q.query (Q.merge singleton (Q.update singleton removeA) (Q.update singleton removeAgain)) () = [] ∧
    Q.query (Q.update (Q.update singleton removeA) removeAgain) () = [] ∧
    Q.query (Q.update (Q.update singleton removeA) removeAgain) () ≠ [10] ∧
    ¬ CanIssue removeAgain (Q.update singleton removeA) ∧
    fifoApplicable (fifoFold [a,removeA]) removeAgain := by
  try simp only [E]
  decide +kernel

abbrev d : Event := (6,0,enq 40 2 [true,false,true,false])
def continued : State := Q.update (Q.update sameTail removeA) d
/-- Following a merge, new enqueue still observes the final live tail and
new dequeue still names the displayed head, rather than the candidate list. -/
theorem postmerge_continuation :
    CanIssue removeA sameTail ∧ CanIssue d (Q.update sameTail removeA) ∧
    Q.query continued () = [30,20,40] ∧
    Q.query continued () ≠ [20,30,40] ∧
    CanIssue (7,0,deq 3) continued ∧ ¬ CanIssue (7,0,deq 2) continued ∧
    Q.query (Q.update continued (7,0,deq 3)) () = [20,40] := by
  try simp only [E]
  decide +kernel

/-- The public language's list semantics append independently of the anchor;
absent dequeue succeeds, while deleting a live non-head is illegal. -/
theorem independent_fifo_controls :
    fifoFold [a,b,c] = [(1,10),(2,20),(3,30)] ∧
    fifoFold [a,b,c] ≠ [(1,10),(3,30),(2,20)] ∧
    fifoApplicable [(1,10),(2,20)] removeA ∧
    ¬ fifoApplicable [(1,10),(2,20)] (7,0,deq 2) ∧
    fifoApplicable [(2,20)] removeAgain ∧
    fifoStep [(2,20)] removeAgain = [(2,20)] := by
  try simp only [E]
  decide +kernel

/-- The exported queue signature returns the tagged head, matching the
original Queue interface; the list controls above additionally pin the tail. -/
theorem public_head_controls :
    publicQueue.query sameTail () = some (1,10) ∧
    publicQueue.query continued () = some (3,30) ∧
    publicQueue.query continued () ≠ some (2,20) ∧
    publicQueue.query (Q.update continued (7,0,deq 3)) () = some (2,20) := by
  change headQuery sameTail () = some (1,10) ∧
    headQuery continued () = some (3,30) ∧
    headQuery continued () ≠ some (2,20) ∧
    headQuery (Q.update continued (7,0,deq 3)) () = some (2,20)
  decide +kernel

#print axioms concurrent_same_tail
#print axioms postmerge_continuation
end Sal.MRDTs.Paper1.AnchoredQueue.Controls
