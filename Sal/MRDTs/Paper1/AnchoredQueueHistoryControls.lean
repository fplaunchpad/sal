import Sal.MRDTs.Paper1.AnchoredQueueHistory
import Sal.MRDTs.Paper1.AnchoredQueueControls

/-! Independent FIFO legality controls. Expected results are literal; the
checks distinguish idempotent removal from invented identities and ID reuse. -/
namespace Sal.MRDTs.Paper1.AnchoredQueue.HistoryControls
open Controls History

theorem duplicate_removal :
    fifoLegal [a,removeA,removeAgain] ∧
    fifoFold [a,removeA,removeAgain] = [] ∧
    ¬ fifoLegal [removeA] := by
  refine ⟨legal_of_check (by decide +kernel), rfl, ?_⟩
  rw [← check_iff_legal]
  decide +kernel

theorem fresh_births :
    fifoLegal [a,removeA,b] ∧
    fifoFold [a,removeA,b] = [(2,20)] ∧
    ¬ fifoLegal [a,removeA,a] := by
  refine ⟨legal_of_check (by decide +kernel), rfl, ?_⟩
  rw [← check_iff_legal]
  decide +kernel

theorem named_head :
    fifoLegal [a,b,removeA] ∧
    fifoFold [a,b,removeA] = [(2,20)] ∧
    ¬ fifoLegal [a,b,(7,0,deq 2)] := by
  refine ⟨legal_of_check (by decide +kernel), rfl, ?_⟩
  rw [← check_iff_legal]
  decide +kernel

-- The sequential enqueue appends even when its recorded anchor was removed.
-- Legality uses birth freshness and named-head removal, not anchor liveness.
theorem removed_anchor_ignored :
    fifoLegal [a,removeA,b,c] ∧
    fifoFold [a,removeA,b,c] = [(2,20),(3,30)] ∧
    fifoFold [a,removeA,b,c] ≠ [(3,30),(2,20)] := by
  refine ⟨legal_of_check (by decide +kernel), rfl, ?_⟩
  decide +kernel

#print axioms duplicate_removal
#print axioms fresh_births
#print axioms named_head
#print axioms removed_anchor_ignored
end Sal.MRDTs.Paper1.AnchoredQueue.HistoryControls
