import Sal.MRDTs.Instances.TransferableBoundedCounterCorrected

/-! Hand-derived PASS+FAIL controls for corrected candidate API. -/
namespace Sal.MRDTs.Instances.TransferableBoundedCounter.CorrectedSPOT
open Foundation TransferableBoundedCounter.Corrected

def funded : State := update (initial 10 0) (1,0,.transfer 5 1)
def left : State := update funded (2,0,.transfer 3 2)
def right : State := update funded (3,1,.transfer 3 2)
def joined : State := merge funded left right

/-- Two donors credit six; common funding is subtracted once. -/
theorem concurrent_transfers :
    applicable 0 funded (2,0,.transfer 3 2) ∧
    applicable 0 funded (3,1,.transfer 3 2) ∧
    query joined (.available 0) = 2 ∧ query joined (.available 1) = 2 ∧
    query joined (.available 2) = 6 ∧ query joined (.available 2) ≠ 3 ∧
    query joined (.reserved 0) + query joined (.reserved 1) + query joined (.reserved 2) = 10 ∧
    query joined (.reserved 0) + query joined (.reserved 1) + query joined (.reserved 2) ≠ 7 := by
  norm_num [applicable, funded, left, right, joined, update, initial,
    available, reserved, query, bump, merge, Op.op]

/-- Allocation consumes four rights without destroying its reservation. -/
theorem allocation_queries :
    applicable 0 joined (4,2,.allocate 4) ∧
    query (update joined (4,2,.allocate 4)) (.available 2) = 2 ∧
    query (update joined (4,2,.allocate 4)) (.allocated 2) = 4 ∧
    query (update joined (4,2,.allocate 4)) (.reserved 2) = 6 ∧
    query (update joined (4,2,.allocate 4)) (.allocated 2) ≠ 0 := by
  norm_num [applicable, funded, left, right, joined, update, initial,
    available, reserved, query, bump, merge, Op.op]

/-- Issuance rejects overspending and negative requests; rejection is no-op. -/
theorem rejected_requests :
    prepareAllocate 0 (initial 10 0) 1 1 = none ∧
    prepareTransfer 0 (initial 10 0) 0 1 (-3) = none ∧
    applyPrepared (initial 10 0) 1 1 (prepareAllocate 0 (initial 10 0) 1 1) = initial 10 0 ∧
    prepareAllocate 0 (initial 10 0) 1 1 ≠ some (.allocate 1) := by
  norm_num [prepareAllocate, prepareTransfer, prepare, applicable,
    initial, available, applyPrepared, Op.op] <;> decide

/-- Membership union survives a merge; it does not echo either branch. -/
theorem participant_union :
    participants 0 (merge (initial 10 0)
      (update (initial 10 0) (1,0,.participants {1}))
      (update (initial 10 0) (2,2,.participants {2}))) = {0,1,2} ∧
    participants 0 (merge (initial 10 0)
      (update (initial 10 0) (1,0,.participants {1}))
      (update (initial 10 0) (2,2,.participants {2}))) ≠ {0,1} := by
  norm_num [participants, merge, update, initial, Op.op] <;> decide

/-- Prepared rebalance of a ten/zero pair transfers five; replay does not
recompute the half-gap. -/
theorem prepared_rebalance_effect :
    applicable 0 (update (initial 10 0) (1,0,.participants {1})) (2,0,.rebalance 5 1) ∧
    query (update (initial 10 0) (2,0,.rebalance 5 1)) (.available 0) = 5 ∧
    query (update (initial 10 0) (2,0,.rebalance 5 1)) (.available 1) = 5 ∧
    query (update (initial 10 0) (2,0,.rebalance 5 1)) (.available 1) ≠ 0 := by
  constructor
  · simp [applicable, update, initial, Op.op, available]
  · norm_num [query, update, initial, Op.op, available, bump]

/-- Actual high-level rebalance preparation picks the funded donor and
records the half-gap. The empty donor cannot issue this rebalance. -/
theorem rebalance_preparation :
    prepareRebalance 0 (update (initial 10 0) (1,0,.participants {1})) 0 = some (.rebalance 5 1) ∧
    prepareRebalance 0 (update (initial 10 0) (1,0,.participants {1})) 1 = none ∧
    prepareRebalance 0 (update (initial 10 0) (1,0,.participants {1})) 0 ≠ some (.rebalance 0 1) := by
  have sorted : ({0,1} : Finset Nat).sort (· ≤ ·) = [0,1] := by
    rw [Finset.sort_insert (· ≤ ·) (by simp) (by simp)]
    exact congrArg (0 :: ·) (Finset.sort_singleton (· ≤ ·) 1)
  norm_num [prepareRebalance, extrema, participants, update, initial, Op.op,
    available, sorted, prepare, applicable] <;> decide

/-- Concurrent allocation at two funded accounts consumes eight of ten,
not four from a projected merge or twelve from overspending. -/
theorem concurrent_allocation_budget :
    applicable 0 funded (2,0,.allocate 4) ∧ applicable 0 funded (3,1,.allocate 4) ∧
    let combined := merge funded (update funded (2,0,.allocate 4)) (update funded (3,1,.allocate 4))
    query combined (.allocated 0) + query combined (.allocated 1) = 8 ∧
    query combined (.allocated 0) + query combined (.allocated 1) ≤ 10 ∧
    query combined (.available 0) + query combined (.available 1) = 2 ∧
    query combined (.allocated 0) + query combined (.allocated 1) ≠ 4 ∧
    prepareAllocate 0 funded 1 6 = none ∧ prepareAllocate 0 funded 1 6 ≠ some (.allocate 6) := by
  norm_num [applicable, funded, update, initial, available, reserved, query,
    bump, merge, Op.op, prepareAllocate, prepare] <;> decide

#print axioms concurrent_transfers
#print axioms rejected_requests
end Sal.MRDTs.Instances.TransferableBoundedCounter.CorrectedSPOT
