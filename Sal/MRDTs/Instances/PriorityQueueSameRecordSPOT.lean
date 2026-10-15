import Sal.MRDTs.Paper1.PriorityQueueSameRecordCertificate
import Sal.MRDTs.Paper1.PriorityQueueSameRecordSpec
import Sal.MRDTs.Paper1.PublishedPriorityQueueObstruction

/-! Hand-derived PASS+FAIL controls for the intentional same-record repair.
The ordinary model, not the implementation, determines expected replay answers.
No general issuance/history adequacy certificate is asserted by these tests. -/
namespace Sal.MRDTs.Instances.PriorityQueueSameRecord.SPOT
open Foundation
open Paper1.PriorityQueueSameRecord (model seqStep seqRead)

private def a : Event := (1,0,.add 7 10)
private def i : Event := (2,0,.inc 7 5 {1})
private def r : Event := (3,0,.remove 7 {1})
private def fresh : Event := (4,0,.add 7 2)
private def beforeRemove := step (step {} a) i
private def reset := step (step beforeRemove r) fresh

theorem reset_discards_old_acquired :
    priority beforeRemove 7 = some 15 ∧ priority reset 7 = some 2 ∧
    priority reset 7 ≠ some 7 ∧
    PublishedAddWinsPriorityQueue.acquired reset (7,1) = 5 ∧
    PublishedAddWinsPriorityQueue.acquired reset (7,4) = 0 := by decide

theorem actual_prepare_guards :
    prepare {} 1 0 (.add 7 10) = some a ∧
    prepare (step {} a) 2 0 (.inc 7 5) = some i ∧
    prepare beforeRemove 3 0 (.remove 7) = some r ∧
    prepare (step beforeRemove r) 4 0 (.add 7 2) = some fresh ∧
    prepare {} 1 0 (.inc 7 5) = none ∧
    prepare {} 1 0 (.remove 7) = none ∧
    prepare (step {} a) 2 0 (.add 7 2) = none ∧
    prepare {} 1 0 (.inc 7 5) ≠ some (1,0,.inc 7 5 ∅) := by decide

private def sourceWitness := Paper1.PublishedPriorityQueueObstruction.joined

theorem unique_mcw_anomaly_repaired :
    PublishedAddWinsPriorityQueue.priorities sourceWitness 7 = {12} ∧
    priority sourceWitness 7 = some 11 ∧
    priority sourceWitness 7 ≠ some 12 ∧
    seqRead ([Paper1.PublishedPriorityQueueObstruction.addA,
      Paper1.PublishedPriorityQueueObstruction.incA,
      Paper1.PublishedPriorityQueueObstruction.addB,
      Paper1.PublishedPriorityQueueObstruction.incB].foldl seqStep model.initial) (.getPri 7) =
        .priority (some 11) := by decide

private def oldIncNewBirth := merge {} beforeRemove (step {} (3,1,.add 7 2))

theorem unrelated_record_increment_does_not_leak :
    priority oldIncNewBirth 7 = some 2 ∧
    priority oldIncNewBirth 7 ≠ some 7 ∧
    PublishedAddWinsPriorityQueue.priorities oldIncNewBirth 7 = {7} ∧
    priority (step oldIncNewBirth (4,0,.inc 7 3 {1,3})) 7 = some 5 ∧
    priority (step oldIncNewBirth (4,0,.inc 7 3 {1,3})) 7 ≠ some 10 := by decide

private def tieBranches := merge {}
  (step (step {} (1,0,.add 7 0)) (3,0,.inc 7 1 {1}))
  (step (step {} (2,1,.add 7 10)) (4,1,.inc 7 (-1) {2}))

theorem no_independent_mcw_tie :
    priority tieBranches 7 = some 9 ∧ priority tieBranches 7 ≠ some 11 ∧
    PublishedAddWinsPriorityQueue.priorities tieBranches 7 = {9,11} ∧
    priority (step tieBranches (5,0,.inc 7 3 {1,2})) 7 = some 12 ∧
    priority (step tieBranches (5,0,.inc 7 3 {1,2})) 7 ≠ some 14 := by decide

private def maxTie := step (step {} (1,0,.add 7 10)) (2,0,.add 8 10)
private def boosted := step maxTie (3,0,.inc 7 5 {1})

theorem maximum_is_computed :
    getMax {} = none ∧ getMax {} ≠ some (0,0) ∧
    getMax maxTie = some (8,10) ∧ getMax maxTie ≠ some (7,10) ∧
    getMax boosted = some (7,15) ∧ getMax boosted ≠ some (8,10) ∧
    read boosted (.lookup 7) = .boolean true ∧
    read boosted .empty ≠ .boolean true := by decide

theorem extraction_observes_then_removes :
    prepareRmvMax boosted 4 0 = some ((4,0,.remove 7 {1}),(7,15)) ∧
    rmvMax boosted 4 0 = some ((7,15),step boosted (4,0,.remove 7 {1})) ∧
    getMax (step boosted (4,0,.remove 7 {1})) = some (8,10) ∧
    priority (step (step boosted (4,0,.remove 7 {1})) (5,0,.add 7 2)) 7 = some 2 ∧
    priority (step (step boosted (4,0,.remove 7 {1})) (5,0,.add 7 2)) 7 ≠ some 7 := by decide

end Sal.MRDTs.Instances.PriorityQueueSameRecord.SPOT
