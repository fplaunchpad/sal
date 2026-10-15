import Sal.MRDTs.Paper1.PublishedPriorityQueueObstruction

/-! Hand-derived Algorithm 2 PASS+FAIL controls. These are source-conformance
controls, not certificates of ordinary priority-queue RA linearizability. -/
namespace Sal.MRDTs.Instances.PublishedAddWinsPriorityQueue.SPOT
open Foundation

abbrev empty : State := {}
def a10 : Event := (1,0,.add 7 10)
def i5 : Event := (2,0,.inc 7 5 {1})
def rem : Event := (3,0,.remove 7 {1})
def a2 : Event := (4,0,.add 7 2)
def removed : State := step (step (step empty a10) i5) rem
def readded : State := step removed a2

theorem source_reset_after_remove_readd :
    priorities readded 7 = {2} ∧ priorities readded 7 ≠ {7} ∧
    record readded (7,1) = ⟨(7,1),{10},5,5⟩ ∧
    record readded (7,4) = ⟨(7,4),{2},0,0⟩ := by decide

theorem complete_local_guards :
    prepare empty 1 0 (.add 7 10) = some a10 ∧
    prepare (step empty a10) 2 0 (.inc 7 5) = some i5 ∧
    prepare (step (step empty a10) i5) 3 0 (.remove 7) = some rem ∧
    prepare removed 4 0 (.add 7 2) = some a2 ∧
    prepare empty 2 0 (.inc 7 5) = none ∧
    prepare empty 3 0 (.remove 7) = none ∧
    prepare (step empty a10) 4 0 (.add 7 2) ≠ some a2 := by decide

theorem observed_remove_disables_record_value :
    lookup removed 7 = false ∧ priorities removed 7 = ∅ ∧
    priorities removed 7 ≠ {15} := by decide

/-- Inc can be delivered before the Add that it honestly observed elsewhere.
The placeholder is visible to lookup; null arithmetic remains unresolved. -/
def early : State := step empty i5

theorem early_increment_placeholder :
    record early (7,1) = ⟨(7,1),∅,5,5⟩ ∧
    lookup early 7 = true ∧ unresolvedInnate early 7 = true ∧
    priorities early 7 = ∅ ∧ priorities early 7 ≠ {5} := by decide

theorem arriving_add_fills_null_without_reset :
    record (step early a10) (7,1) = ⟨(7,1),{10},5,5⟩ ∧
    priorities (step early a10) 7 = {15} ∧
    priorities (step early a10) 7 ≠ {10} := by decide

/-- A later insertion does not inherit increments that observed only an older
insertion. While the older insertion stays live, MCW may still select it. -/
def unobserved : State := merge empty (step (step empty a10) i5)
    (step empty (3,1,.add 7 2))

theorem increments_are_per_observed_record :
    record unobserved (7,1) = ⟨(7,1),{10},5,5⟩ ∧
    record unobserved (7,3) = ⟨(7,3),{2},0,0⟩ ∧
    priorities unobserved 7 = {7} ∧ priorities unobserved 7 ≠ {2} ∧
    priorities (step unobserved (4,0,.remove 7 {1})) 7 = {2} ∧
    priorities (step unobserved (4,0,.remove 7 {1})) 7 ≠ {7} := by decide

def tieA : State := step (step empty (1,0,.add 7 0)) (3,0,.inc 7 1 {1})
def tieB : State := step (step empty (2,1,.add 7 10)) (4,1,.inc 7 (-1) {2})
def tied : State := merge empty tieA tieB

theorem published_mcw_tie_is_not_resolved :
    priorities tied 7 = {9,11} ∧ priorities tied 7 ≠ {9} ∧
    priorities tied 7 ≠ {11} ∧ priorities tied 7 ≠ {10} := by decide

/-- When an issuer sees both births, its Inc targets both, without double
counting the same effect at a merge. -/
def sharedIncrement : Event := (5,2,.inc 7 3 {1,2})
def twoObserved : State := step (merge empty tieA tieB) sharedIncrement

theorem increment_updates_every_observed_birth :
    record twoObserved (7,1) = ⟨(7,1),{0},4,4⟩ ∧
    record twoObserved (7,2) = ⟨(7,2),{10},2,4⟩ ∧
    priorities twoObserved 7 = {12,14} ∧ priorities twoObserved 7 ≠ {13} := by decide

/-- Maximum selection and derived removal follow the exact allowed source
query answer, including its original priority, rather than candidate echoes. -/
def queue : State := step (step (step empty a10) i5) (3,0,.add 8 17)
def boosted : State := step queue (4,0,.inc 7 5 {1})
def removedMaximum : State := step boosted (5,0,.remove 7 {1})

theorem maximum_and_derived_remove :
    maximumPairs queue = {(8,17)} ∧ maximumPairs queue ≠ {(7,15)} ∧
    maximumPairs boosted = {(7,20)} ∧ maximumPairs boosted ≠ {(8,17)} ∧
    prepareRmvMax boosted 5 0 = {((5,0,Payload.remove 7 {1}),(7,20))} ∧
    maximumPairs removedMaximum = {(8,17)} ∧
    priorities (step removedMaximum (6,0,.add 7 2)) 7 = {2} ∧
    priorities (step removedMaximum (6,0,.add 7 2)) 7 ≠ {12} := by decide

theorem empty_maximum :
    maximumPairs empty = ∅ ∧ prepareRmvMax empty 1 0 = ∅ ∧
    maximumPairs empty ≠ {(0,0)} := by decide

end Sal.MRDTs.Instances.PublishedAddWinsPriorityQueue.SPOT
