import Sal.MRDTs.Paper1.AnchoredQueueHistory
import Sal.MRDTs.Paper1.CertifiedHistoryCommutation
import Sal.MRDTs.Paper1.AnchoredQueueReadSide
import Sal.MRDTs.Paper1.AnchoredQueuePublic

namespace Sal.MRDTs.Paper1.AnchoredQueue.History
open Foundation Instances.EmbedRGA

/-- Independent appending enqueue and an unrelated named dequeue commute on
 every abstract state, without consulting the recorded tail. -/
theorem unrelated_steps (dts dr its ir target value anchor : Nat)
    (coordinate : List Bool) (different : its ≠ target)
    (s : List (Nat × Nat)) :
    fifoStep (fifoStep s (dts,dr,deq target)) (its,ir,enq value anchor coordinate) =
    fifoStep (fifoStep s (its,ir,enq value anchor coordinate)) (dts,dr,deq target) := by
  simp [fifoStep, deq, enq, List.filter_append, different,Op.op,Op.time]

private theorem checks_append (pre xs ys : List Event) :
    CheckFrom pre (xs ++ ys) ↔ CheckFrom pre xs ∧ CheckFrom (pre ++ xs) ys := by
  induction xs generalizing pre with
  | nil => simp [CheckFrom]
  | cons x xs ih => simp [CheckFrom,ih,List.append_assoc,and_assoc]

private theorem checks_congr (p q xs : List Event)
    (equal : ∀ tail e, NextLegal (p ++ tail) e ↔ NextLegal (q ++ tail) e) :
    CheckFrom p xs ↔ CheckFrom q xs := by
  rw [checkFrom_iff,checkFrom_iff]
  exact forall_congr' fun before => forall_congr' fun e => forall_congr' fun after =>
    imp_congr_right fun _ => equal before e

private theorem checks_swap (pre suf : List Event) (a b : Event)
    (firstA : NextLegal (pre ++ [b]) a ↔ NextLegal pre a)
    (firstB : NextLegal (pre ++ [a]) b ↔ NextLegal pre b)
    (suffix : ∀ tail e, NextLegal ((pre ++ [a,b]) ++ tail) e ↔
      NextLegal ((pre ++ [b,a]) ++ tail) e) :
    CheckFrom [] (pre ++ [a,b] ++ suf) ↔ CheckFrom [] (pre ++ [b,a] ++ suf) := by
  rw [checks_append,checks_append]
  simp only [List.nil_append]
  rw [checks_append,checks_append]
  simp only [CheckFrom,List.append_nil,true_and,and_true]
  have last := checks_congr (pre ++ [a,b]) (pre ++ [b,a]) suf suffix
  simp only [List.append_assoc] at last ⊢
  tauto

private theorem dequeue_applicable_append (s : List (Nat × Nat))
    (dts dr its ir target value anchor : Nat) (coordinate : List Bool)
    (different : its ≠ target) :
    fifoApplicable (s ++ [(its,value)]) (dts,dr,deq target) ↔
      fifoApplicable s (dts,dr,deq target) := by
  cases s <;> simp [fifoApplicable,deq,different,Ne.symm different,Op.op,Op.time]

private theorem nextLegal_enq (pre : List Event) (its ir value anchor : Nat)
    (coordinate : List Bool) :
    NextLegal pre (its,ir,enq value anchor coordinate) ↔ its ∉ eInsIds pre := by
  simp only [NextLegal,fifoApplicable,enq,eIsIns,Op.op,Op.time,reduceCtorEq,
    false_implies,implies_true,and_true,true_implies]
  exact ⟨fun h => h.2,fun h => ⟨fifo_fresh_of_birth_fresh h,h⟩⟩

private theorem nextLegal_deq (pre : List Event) (dts dr target : Nat) :
    NextLegal pre (dts,dr,deq target) ↔
    fifoApplicable (fifoFold pre) (dts,dr,deq target) ∧ target ∈ eInsIds pre := by
  simp only [NextLegal,deq,eIsIns,Op.op,reduceCtorEq,false_implies,true_and,
    EOp.del.injEq,forall_eq']

/-- The public legality contract exchanges an unrelated enqueue/dequeue pair
 in every context, including contexts containing duplicate removals. -/
theorem unrelated_legal_swap (dts dr its ir target value anchor : Nat)
    (coordinate : List Bool) (different : its ≠ target) (pre suf : List Event) :
    fifoLegal (pre ++ [(dts,dr,deq target),(its,ir,enq value anchor coordinate)] ++ suf) ↔
    fifoLegal (pre ++ [(its,ir,enq value anchor coordinate),(dts,dr,deq target)] ++ suf) := by
  rw [← check_iff_legal,← check_iff_legal]
  apply checks_swap
  · rw [nextLegal_deq,nextLegal_deq]
    have fold : fifoFold (pre ++ [(its,ir,enq value anchor coordinate)]) =
        fifoFold pre ++ [(its,value)] := by
      simp [fifoFold,List.foldl_append,fifoStep,enq,Op.op,Op.time]
    rw [fold,dequeue_applicable_append _ dts dr its ir target value anchor coordinate different]
    simp [eInsIds_append,eInsIds,enq,eIsIns,Op.time,different,Ne.symm different]
  · rw [nextLegal_enq,nextLegal_enq]
    simp [eInsIds_append,eInsIds,deq,eIsIns]
  · intro tail e
    have fold : fifoFold ((pre ++ [(dts,dr,deq target),(its,ir,enq value anchor coordinate)]) ++ tail) =
        fifoFold ((pre ++ [(its,ir,enq value anchor coordinate),(dts,dr,deq target)]) ++ tail) := by
      simp only [fifoFold,List.foldl_append,List.foldl_cons,List.foldl_nil]
      rw [unrelated_steps dts dr its ir target value anchor coordinate different]
    have ids : eInsIds ((pre ++ [(dts,dr,deq target),(its,ir,enq value anchor coordinate)]) ++ tail) =
        eInsIds ((pre ++ [(its,ir,enq value anchor coordinate),(dts,dr,deq target)]) ++ tail) := by
      simp [eInsIds_append,eInsIds,eIsIns,enq,deq]
    simp only [NextLegal,fold,ids]

/-- Specification-conflict visibility can disregard unrelated enqueue/dequeue
 edges even though both operations retain their original anchors and targets. -/
theorem unrelated_language (dts dr its ir target value anchor : Nat)
    (coordinate : List Bool) (different : its ≠ target) :
    language.Commutes (dts,dr,deq target) (its,ir,enq value anchor coordinate) := by
  apply GuardedHistory.language_commutes_of_legal_swap fifoSpec
    (fun _ _ h => fifoLegal_prefix h)
  · exact unrelated_steps dts dr its ir target value anchor coordinate different
  · exact unrelated_legal_swap dts dr its ir target value anchor coordinate different

/-- The tagged-head public query has the same contextual independence: the
 proof exchanges complete abstract tagged states, so identity is retained. -/
theorem unrelated_public_language (dts dr its ir target value anchor : Nat)
    (coordinate : List Bool) (different : its ≠ target) :
    Public.language.Commutes (dts,dr,deq target) (its,ir,enq value anchor coordinate) := by
  apply GuardedHistory.language_commutes_of_legal_swap Public.fifoSpec
    (fun _ _ h => fifoLegal_prefix h)
  · exact unrelated_steps dts dr its ir target value anchor coordinate different
  · exact unrelated_legal_swap dts dr its ir target value anchor coordinate different

/-- A sufficient syntactic conflict relation for the independent FIFO:
 same-kind operations and an enqueue paired with removal of its own identity. -/
def Conflict (a b : Event) : Prop :=
  match a.op,b.op with
  | .ins _ _ _, .ins _ _ _ => True
  | .del _, .del _ => True
  | .ins _ _ _, .del target => a.time = target
  | .del target, .ins _ _ _ => b.time = target

theorem conflict_symmetric {a b : Event} (h : Conflict a b) : Conflict b a := by
  rcases a with ⟨ats,ar,ao⟩
  rcases b with ⟨bts,br,bo⟩
  cases ao <;> cases bo <;> simpa [Conflict,Op.op,Op.time] using h

theorem nonconflicting_public_commutes {a b : Event} (independent : ¬ Conflict a b) :
    Public.language.Commutes a b := by
  rcases a with ⟨ats,ar,ao⟩
  rcases b with ⟨bts,br,bo⟩
  cases ao with
  | ins value pref anchor =>
    cases bo with
    | ins value' pref' anchor' => simp [Conflict,Op.op] at independent
    | del target =>
      have different : ats ≠ target := by simpa [Conflict,Op.op,Op.time] using independent
      exact HistorySpec.commutes_symm
        (unrelated_public_language bts br ats ar target value anchor pref different)
  | del target =>
    cases bo with
    | del target' => simp [Conflict,Op.op] at independent
    | ins value pref anchor =>
      have different : bts ≠ target := by simpa [Conflict,Op.op,Op.time] using independent
      exact unrelated_public_language ats ar bts br target value anchor pref different

theorem nonconflicting_language {a b : Event} (independent : ¬ Conflict a b) :
    language.Commutes a b := by
  rcases a with ⟨ats,ar,ao⟩
  rcases b with ⟨bts,br,bo⟩
  cases ao with
  | ins value pref anchor =>
    cases bo with
    | ins value' pref' anchor' => simp [Conflict,Op.op] at independent
    | del target =>
      have different : ats ≠ target := by simpa [Conflict,Op.op,Op.time] using independent
      exact HistorySpec.commutes_symm
        (unrelated_language bts br ats ar target value anchor pref different)
  | del target =>
    cases bo with
    | del target' => simp [Conflict,Op.op] at independent
    | ins value pref anchor =>
      have different : bts ≠ target := by simpa [Conflict,Op.op,Op.time] using independent
      exact unrelated_language ats ar bts br target value anchor pref different

theorem visibility_conflict {C : Configuration Q} {a b : Event}
    (edge : projectedSpecVisibility id language C.replayContext a b) :
    C.vis a b ∧ Conflict a b := by
  exact ⟨edge.1,Classical.byContradiction (fun independent =>
    edge.2 (nonconflicting_language independent))⟩

theorem public_visibility_conflict {C : Configuration publicQueue} {a b : Event}
    (edge : projectedSpecVisibility id Public.language C.replayContext a b) :
    C.vis a b ∧ Conflict a b := by
  exact ⟨edge.1,Classical.byContradiction (fun independent =>
    edge.2 (nonconflicting_public_commutes independent))⟩

theorem invariant_order_conflict {C : Configuration Q}
    (exec : CertifiedExecution Q issuance C) {H : Set Event} {a b : Event}
    (ha : a ∈ C.events) (hb : b ∈ C.events)
    (edge : InvariantOrder.order (Valid C) CertifiedRGAInvariantReplay.policy
      C.replayContext H a b) : C.vis a b ∧ Conflict a b := by
  rcases edge with ⟨visible,noncommuting⟩ | concurrent
  · refine ⟨visible,Classical.byContradiction ?_⟩
    intro independent
    apply noncommuting
    apply CertifiedRGAInvariant.semantic_commutes Sal.EmbedRGA.unaryCode C.replayContext
      (eHonest_core (eHonest_of_mint (execution_weaken exec).mintHonest)) a b ha hb
    rcases a with ⟨ats,ar,ao⟩
    rcases b with ⟨bts,br,bo⟩
    cases ao <;> cases bo <;>
      simp_all [Conflict,Instances.ProductionRGA.embedSemanticCommutes,Op.op,Op.time]
  · exact False.elim concurrent.2.2.1

#print axioms unrelated_language
#print axioms unrelated_public_language
#print axioms unrelated_steps
end Sal.MRDTs.Paper1.AnchoredQueue.History
