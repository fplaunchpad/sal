import Sal.MRDTs.Instances.BalegasBoundedCounter

/-! Independent hand-derived PASS+FAIL controls for Balegas et al. §III-B.
Amounts are natural numbers. Every trace respects sequential issuance per
replica; concurrency here is between distinct replicas. Expected arithmetic
comes from cumulative increments, transfers and consumption, not evaluation.
The SRDS Fig. 2 value label is inconsistent with its cells; we use the cells
and the companion report's value 30 instead.
-/
namespace Sal.MRDTs.Instances.BalegasBoundedCounter.SPOT
open Foundation

-- Ten rights at replica 0, then five at each of replicas 0 and 1.
def funded : State := update initial (1, 0, .increment 10)
def split : State := update funded (2, 0, .transfer 5 1)
def donor0 : State := update split (3, 0, .transfer 3 2)
def donor1 : State := update split (4, 1, .transfer 3 2)
def donorsJoined : State := merge split donor0 donor1

/-- Distinct matrix cells retain both donors; a projected merge loses three. -/
theorem concurrent_donors :
    applicable 3 split (3, 0, .transfer 3 2) ∧
    applicable 3 split (4, 1, .transfer 3 2) ∧
    donorsJoined.R 0 2 = 3 ∧ donorsJoined.R 1 2 = 3 ∧
    localRights 3 donorsJoined 0 = 2 ∧ localRights 3 donorsJoined 1 = 2 ∧
    localRights 3 donorsJoined 2 = 6 ∧ localRights 3 donorsJoined 2 ≠ 3 ∧
    value 3 10 donorsJoined = 20 ∧ value 3 10 donorsJoined ≠ 26 := by
  simp only [applicable, Op.op]
  decide

/-- Five rights each permit concurrent spending of four, leaving two total. -/
theorem concurrent_spending :
    applicable 3 split (3, 0, .decrement 4) ∧
    applicable 3 split (4, 1, .decrement 4) ∧
    let s := merge split (update split (3, 0, .decrement 4))
      (update split (4, 1, .decrement 4))
    s.U 0 = 4 ∧ s.U 1 = 4 ∧ value 3 10 s = 12 ∧ value 3 10 s ≠ 16 ∧
    localRights 3 s 0 = 1 ∧ localRights 3 s 1 = 1 ∧
    ¬ applicable 3 s (5, 0, .decrement 2) := by
  simp only [applicable, Op.op]
  decide

/-- An unseen incoming transfer causes rejection, then delivery enables it.
The stale state is current for recipient 1's own row and consumption. -/
theorem stale_incoming_knowledge :
    localRights 3 funded 1 = 0 ∧ ¬ applicable 3 funded (3, 1, .decrement 4) ∧
    localRights 3 (merge initial funded split) 1 = 5 ∧
    applicable 3 (merge initial funded split) (3, 1, .decrement 4) ∧
    localRights 3 funded 1 ≠ 5 := by
  simp only [applicable, Op.op]
  decide

/-- Duplicate delivery keeps cumulative transfers and spending once. -/
theorem duplicate_delivery :
    let spent := update donorsJoined (5, 2, .decrement 4)
    let delivered := merge initial (merge split spent donor0) donor0
    delivered.R 0 2 = 3 ∧ delivered.U 2 = 4 ∧
    localRights 3 delivered 2 = 2 ∧ localRights 3 delivered 2 ≠ 5 ∧
    value 3 10 delivered = 16 ∧ value 3 10 delivered ≠ 12 := by
  decide

/-- Issuance accepts the exact balance and rejects overdrafts and bad ids.
A negative amount is unrepresentable in Action, rather than a runtime guard. -/
theorem issuance_boundaries :
    applicable 3 split (3, 1, .decrement 5) ∧
    ¬ applicable 3 split (3, 1, .decrement 6) ∧
    applicable 3 split (3, 1, .transfer 5 2) ∧
    ¬ applicable 3 split (3, 1, .transfer 6 2) ∧
    ¬ applicable 3 split (3, 1, .transfer 1 1) ∧
    ¬ applicable 3 split (3, 1, .transfer 1 3) ∧
    ¬ applicable 3 split (3, 3, .increment 1) ∧
    applicable 3 split (3, 1, .decrement 0) := by
  simp only [applicable, Op.op]
  decide

/-- Increment changes value, transfer preserves it, decrement consumes it.
The bound itself is not usable credit. Diagonal increments count once. -/
theorem operation_values :
    value 3 10 initial = 10 ∧ localRights 3 initial 0 = 0 ∧
    ¬ applicable 3 initial (0, 0, .decrement 1) ∧
    value 3 10 funded = 20 ∧ localRights 3 funded 0 = 10 ∧
    localRights 3 funded 0 ≠ 20 ∧ value 3 10 split = 20 ∧
    value 3 10 (update split (3, 1, .decrement 4)) = 16 ∧
    value 3 10 (update split (3, 1, .decrement 4)) ≠ 20 := by
  simp only [applicable, Op.op]
  decide

/-- The published figure's cells: 31 increments, 11 decrements, K=10.
Off-diagonal transfers redistribute rights but never enter the value sum. -/
def figureCells : State :=
  update (update (update (update (update (update (update initial
    (1, 0, .increment 30)) (2, 1, .increment 1))
    (3, 0, .transfer 10 1)) (4, 0, .transfer 10 2))
    (5, 0, .decrement 5)) (6, 1, .decrement 4)) (7, 2, .decrement 2)

theorem published_cells :
    value 3 10 figureCells = 30 ∧ value 3 10 figureCells ≠ 20 ∧
    localRights 3 figureCells 0 = 5 ∧ localRights 3 figureCells 1 = 7 ∧
    localRights 3 figureCells 2 = 8 ∧ localRights 3 figureCells 0 ≠ 35 := by
  decide

/-- Ternary embedding ignores its ancestor; the ancestor is not subtracted. -/
theorem ancestor_irrelevance :
    localRights 3 (merge initial donor0 donor1) 2 = 6 ∧
    localRights 3 (merge donorsJoined donor0 donor1) 2 = 6 ∧
    value 3 10 (merge donorsJoined donor0 donor1) = 20 ∧
    value 3 10 (merge donorsJoined donor0 donor1) ≠ 10 := by
  decide

/-- Each accepted effect writes its issuer's row or U cell only. -/
theorem single_writer_cells :
    donor1.R 0 0 = split.R 0 0 ∧ donor1.R 0 1 = split.R 0 1 ∧
    donor1.R 0 2 = split.R 0 2 ∧ donor1.R 1 2 = 3 ∧ donor1.R 0 2 ≠ 3 ∧
    (update split (3, 1, .decrement 4)).U 0 = 0 ∧
    (update split (3, 1, .decrement 4)).U 1 = 4 ∧
    (update split (3, 1, .decrement 4)).U 0 ≠ 4 := by
  decide

/-- Counterfactual outside the supported model: two stale requests at the
same issuer reuse ten rights. The guards alone do not provide serialization.
This pins the paper's per-replica sequential-execution assumption. -/
theorem same_issuer_stale_fork_requires_serialization :
    applicable 3 funded (2, 0, .transfer 7 1) ∧
    applicable 3 funded (3, 0, .transfer 7 2) ∧
    let fork := merge funded (update funded (2, 0, .transfer 7 1))
      (update funded (3, 0, .transfer 7 2))
    localRights 3 fork 0 = -4 ∧ localRights 3 fork 0 ≠ 3 ∧
    applicable 3 fork (4, 1, .decrement 7) ∧
    applicable 3 fork (5, 2, .decrement 7) ∧
    value 3 10 (merge fork (update fork (4, 1, .decrement 7))
      (update fork (5, 2, .decrement 7))) = 6 ∧
    ¬ 10 ≤ value 3 10 (merge fork (update fork (4, 1, .decrement 7))
      (update fork (5, 2, .decrement 7))) := by
  simp only [applicable, Op.op]
  decide

#print axioms concurrent_donors
#print axioms concurrent_spending
#print axioms issuance_boundaries
end Sal.MRDTs.Instances.BalegasBoundedCounter.SPOT
