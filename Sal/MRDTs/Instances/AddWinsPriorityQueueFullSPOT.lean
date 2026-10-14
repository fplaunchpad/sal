import Sal.MRDTs.Paper1.AddWinsPriorityQueueFullCertificate
import Sal.MRDTs.Instances.AddWinsPriorityQueueSPOT

/-! Full-interface PASS+FAIL traces with hand-derived maxima. The queue uses
finite live support; equal priorities choose the greatest natural-number ID. -/
namespace Sal.MRDTs.Instances.AddWinsPriorityQueue.FullSPOT
open Foundation

def empty : State Nat := (∅,∅)
def two : State Nat := step (step empty (1,0,.add 7 10)) (2,0,.add 8 20)
def three : State Nat := step two (3,0,.add 9 2)

theorem empty_queries :
    FullD.query empty .empty = .boolean true ∧
    FullD.query empty .getMax = .maximum none ∧
    FullD.query empty .empty ≠ .boolean false ∧
    FullD.query empty .getMax ≠ .maximum (some (0,0)) := by decide

theorem lookup_and_priority :
    FullD.query two (.lookup 7) = .boolean true ∧
    FullD.query two (.lookup 9) = .boolean false ∧
    FullD.query two (.getPri 8) = .priority (some 20) ∧
    FullD.query two (.getPri 9) = .priority none ∧
    FullD.query two (.lookup 9) ≠ .boolean true ∧
    FullD.query two (.getPri 9) ≠ .priority (some 0) := by decide

theorem actual_maximum :
    FullD.query three .getMax = .maximum (some (8,20)) ∧
    FullD.query three .getMax ≠ .maximum (some (7,10)) ∧
    FullD.query three .getMax ≠ .maximum (some (9,2)) ∧
    FullD.query three .getMax ≠ .maximum none := by decide

def tied : State Nat := step (step empty (1,0,.add 7 10)) (2,1,.add 9 10)

theorem deterministic_tie :
    FullD.query tied .getMax = .maximum (some (9,10)) ∧
    FullD.query tied .getMax ≠ .maximum (some (7,10)) := by decide

def changed : State Nat := step two (3,0,.inc 7 15)

theorem increments_change_maximum :
    FullD.query changed .getMax = .maximum (some (7,25)) ∧
    FullD.query changed .getMax ≠ .maximum (some (8,20)) ∧
    FullD.query changed (.getPri 7) ≠ .priority (some 10) := by decide

def negative : State Nat :=
  step (step (step empty (1,0,.add 7 1)) (2,0,.inc 7 (-8))) (3,0,.add 8 0)

theorem signed_maximum :
    FullD.query negative (.getPri 7) = .priority (some (-7)) ∧
    FullD.query negative .getMax = .maximum (some (8,0)) ∧
    FullD.query negative .getMax ≠ .maximum (some (7,1)) := by decide

def incremented : State Nat := step two (3,0,.inc 8 5)
def removed : State Nat := step incremented (4,0,.remove 8)

theorem remove_max_return_and_effect :
    prepareRmvMax incremented 4 0 = some ((4,0,.remove 8),(8,25)) ∧
    rmvMax incremented 4 0 = some ((8,25),removed) ∧
    FullD.query removed .getMax = .maximum (some (7,10)) ∧
    prepareRmvMax incremented 4 0 ≠ some ((4,0,.remove 7),(7,10)) ∧
    FullD.query removed (.lookup 8) ≠ .boolean true := by
  refine ⟨by decide,?_,by decide,by decide,by decide⟩
  have prepared : prepareRmvMax incremented 4 0 = some ((4,0,.remove 8),(8,25)) := by decide
  rw [rmvMax,prepared]
  rfl

theorem remove_max_retains_increments :
    FullD.query (step removed (5,0,.add 8 3)) (.getPri 8) = .priority (some 8) ∧
    FullD.query (step removed (5,0,.add 8 3)) (.getPri 8) ≠ .priority (some 3) ∧
    FullD.query (step removed (5,0,.add 8 3)) .getMax = .maximum (some (7,10)) := by decide

theorem empty_remove_max :
    prepareRmvMax empty 1 0 = none ∧ rmvMax empty 1 0 = none ∧
    prepareRmvMax empty 1 0 ≠ some ((1,0,.remove 0),(0,0)) := by decide

/-- Two replicas can prepare the same selected pair. Derived local removal
therefore does not implement atomic global extraction of distinct pairs. -/
theorem concurrent_clients_can_return_same_pair :
    prepareRmvMax two 3 0 = some ((3,0,.remove 8),(8,20)) ∧
    prepareRmvMax two 4 1 = some ((4,1,.remove 8),(8,20)) ∧
    prepareRmvMax two 4 1 ≠ some ((4,1,.remove 7),(7,10)) ∧
    FullD.query (merge two (step two (3,0,.remove 8)) (step two (4,1,.remove 8))) .getMax =
      .maximum (some (7,10)) := by
  refine ⟨?_,?_,?_,?_⟩ <;> decide

/-- The independent model accepts the changing maximum and rejects a stale
winner; this is not a candidate list computed from concrete replay. -/
theorem independent_max_history :
    Paper1.AddWinsPriorityQueue.Full.spec.admits
      [.update (1,0,.add 7 10),.update (2,0,.add 8 20),.update (3,0,.inc 7 15),
        .query .getMax (.maximum (some (7,25)))] ∧
    ¬ Paper1.AddWinsPriorityQueue.Full.spec.admits
      [.update (1,0,.add 7 10),.update (2,0,.add 8 20),.update (3,0,.inc 7 15),
        .query .getMax (.maximum (some (8,20)))] := by
  change Paper1.AddWinsPriorityQueue.Full.model.toSpec.admits
      (Paper1.DeterministicSpec.updateLabels
        [(1,0,Update.add 7 10),(2,0,.add 8 20),(3,0,.inc 7 15)] ++
        [.query .getMax (.maximum (some (7,25)))]) ∧
    ¬ Paper1.AddWinsPriorityQueue.Full.model.toSpec.admits
      (Paper1.DeterministicSpec.updateLabels
        [(1,0,Update.add 7 10),(2,0,.add 8 20),(3,0,.inc 7 15)] ++
        [.query .getMax (.maximum (some (8,20)))])
  rw [Paper1.DeterministicSpec.updates_query_iff,Paper1.DeterministicSpec.updates_query_iff]
  constructor <;> decide

end Sal.MRDTs.Instances.AddWinsPriorityQueue.FullSPOT
