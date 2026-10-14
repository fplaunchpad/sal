import Sal.MRDTs.Paper1.AddWinsPriorityQueueCertificate
import Sal.MRDTs.Instances.AddWinsPriorityQueueReadSide

/-! Hand-derived PASS+FAIL priority traces. Distinct replica identifiers are
used for concurrent branches. Negative values pin the historical-increment,
latest-timestamp and ancestor-sensitive semantics rather than mere presence. -/
namespace Sal.MRDTs.Instances.AddWinsPriorityQueue.SPOT
open Foundation

def empty : State Nat := (∅,∅)
def add : Op (Update Nat) := (1,0,.add 7 10)
def inc : Op (Update Nat) := (2,0,.inc 7 5)
def rem : Op (Update Nat) := (3,0,.remove 7)

theorem innate_priority : query (step empty add) 7 = some 10 ∧
    query (step empty add) 7 ≠ none := by decide

theorem signed_priority : query (step (step empty add) (2,0,.inc 7 (-13))) 7 = some (-3) ∧
    query (step (step empty add) (2,0,.inc 7 (-13))) 7 ≠ some 10 := by decide

theorem observed_remove : query (step (step empty add) rem) 7 = none ∧
    query (step (step empty add) rem) 7 ≠ some 10 := by decide

def inherited : State Nat := step (step empty add) inc

theorem remove_readd_preserves_increments :
    query (step (step inherited rem) (4,0,.add 7 20)) 7 = some 25 ∧
    query (step (step inherited rem) (4,0,.add 7 20)) 7 ≠ some 20 := by decide

theorem increment_while_absent_is_retained :
    query (step (step empty inc) (3,0,.add 7 10)) 7 = some 15 ∧
    query (step (step empty inc) (3,0,.add 7 10)) 7 ≠ some 10 := by decide

theorem latest_timestamp_not_maximum_innate :
    query (step (step empty (1,0,.add 7 100)) (2,1,.add 7 3)) 7 = some 3 ∧
    query (step (step empty (1,0,.add 7 100)) (2,1,.add 7 3)) 7 ≠ some 100 := by decide

def concurrent : State Nat :=
  merge inherited (step inherited (3,0,.remove 7)) (step inherited (4,1,.add 7 20))

theorem concurrent_add_wins : query concurrent 7 = some 25 ∧
    query concurrent 7 ≠ none ∧ query concurrent 7 ≠ some 20 := by decide

theorem merge_neither_branch_projection :
    concurrent = (({(7,4,20)},{(7,2,5)}) : State Nat) ∧
    concurrent ≠ step inherited (3,0,.remove 7) ∧
    concurrent ≠ step inherited (4,1,.add 7 20) := by
  refine ⟨?_,?_,?_⟩ <;> decide

theorem ancestor_observed_remove :
    query (merge inherited (step inherited (3,0,.remove 7)) inherited) 7 = none ∧
    query (merge inherited (step inherited (3,0,.remove 7)) inherited) 7 ≠ some 15 := by decide

def increments : State Nat :=
  merge (step empty add) (step (step empty add) (2,0,.inc 7 5))
    (step (step empty add) (3,1,.inc 7 (-8)))

theorem concurrent_signed_increments : query increments 7 = some 7 ∧
    query increments 7 ≠ some 15 ∧ query increments 7 ≠ some 2 := by decide

theorem repeated_delivery_is_idempotent :
    query (step (step (step empty add) inc) inc) 7 = some 15 ∧
    query (step (step (step empty add) inc) inc) 7 ≠ some 20 := by decide

/-- The sequential cell model accepts the signed, remove/re-add answer and
rejects the tempting reset-on-remove answer independently of concrete merge. -/
theorem independent_history :
    (Paper1.AddWinsPriorityQueue.spec Nat).admits
      [.update add,.update inc,.update rem,.update (4,0,.add 7 20),.query 7 (some 25)] ∧
    ¬ (Paper1.AddWinsPriorityQueue.spec Nat).admits
      [.update add,.update inc,.update rem,.update (4,0,.add 7 20),.query 7 (some 20)] := by
  change (Paper1.AddWinsPriorityQueue.model Nat).toSpec.admits
      (Paper1.DeterministicSpec.updateLabels [add,inc,rem,(4,0,.add 7 20)] ++ [.query 7 (some 25)]) ∧
    ¬ (Paper1.AddWinsPriorityQueue.model Nat).toSpec.admits
      (Paper1.DeterministicSpec.updateLabels [add,inc,rem,(4,0,.add 7 20)] ++ [.query 7 (some 20)])
  rw [Paper1.DeterministicSpec.updates_query_iff,Paper1.DeterministicSpec.updates_query_iff]
  constructor <;> decide

end Sal.MRDTs.Instances.AddWinsPriorityQueue.SPOT
