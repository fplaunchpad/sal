import Sal.MRDTs.Paper1.CertifiedQueueMVRCommutation
import Sal.MRDTs.Paper1.CertifiedHistoryBridge
import Sal.MRDTs.Paper1.GuardedHistory

/-! Independent sequential histories for certified compact MVR event sets.
Only event support, causal closure and a finite enumeration are required;
no correctness theorem about stored or merged MVR states is used. -/
namespace Sal.MRDTs.Paper1.CertifiedMVRHistory
open Foundation ConcreteMRDT Instances.MVRLive
open Classical
abbrev policy := commutingPolicy D.AppOp
abbrev language := GuardedHistory.language spec

theorem legal_prefix (pre suf : List Event) (h : spec.Legal (pre ++ suf)) :
    spec.Legal pre := by
  obtain ⟨nd,targets⟩ := h
  refine ⟨?_,?_⟩
  · exact (List.nodup_append.mp (by simpa only [List.map_append] using nd)).1
  · intro before e after split n target
    apply targets before e (after ++ suf) _ n target
    simp only [split,List.append_assoc,List.cons_append]

theorem chronological_vis (C : Configuration D) (ops : List Event) :
    respects (Instances.MVR.chronological ops) C.vis :=
  (Instances.MVR.chronological_sorted ops).imp fun {_ _} le vis =>
    (not_lt_of_ge le) (C.causal_mono vis)

theorem chronological_paperOrder (C : Configuration D) (E : Set Event)
    (ops : List Event) :
    respects (Instances.MVR.chronological ops) (paperOrder policy C.replayContext E) := by
  apply (chronological_vis C ops).imp
  intro a b backward edge
  rcases edge with causal | concurrent
  · exact backward causal.1
  · exact concurrent.2.2.1.elim

/-- This supplies the history half of the bridge independently of merge VCs. -/
theorem replay_history (C : Configuration D) (execution : CertifiedExecution D issuance C)
    (E : Set Event) (supported : E ⊆ C.events)
    (closed : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    (ops : List Event) (perm : listPermOf ops E) (q : D.Query) :
    ∃ π : List Event, listPermOf π E ∧ respects π C.vis ∧
      respects π (paperOrder policy C.replayContext E) ∧
      respects π (projectedSpecVisibility id language C.replayContext) ∧
      Represents E (applySeq D.toUpdateSig D.init π) ∧
      language.admits (projectedLabels id π ++
        [.query q (D.query (applySeq D.toUpdateSig D.init π) q)]) := by
  let π := Instances.MVR.chronological ops
  have hp : listPermOf π E :=
    ⟨(Instances.MVR.chronological_perm ops).symm.nodup perm.1,
      fun e => (Instances.MVR.chronological_perm ops).mem_iff.trans (perm.2 e)⟩
  have oldOrder : @respects Event π (@loOn D.toUpdateSig rc C.replayContext E) := by
    apply (Instances.MVR.chronological_sorted ops).imp
    intro a b le edge
    rcases edge with causal | resolved
    · exact (not_lt_of_ge le) (C.causal_mono causal.1)
    · exact (not_lt_of_ge le) ((Instances.MVR.rc_before_iff b a).mp resolved.2.2.1).1
  have legal := replay_legal execution.mintHonest supported closed hp oldOrder
  refine ⟨π,hp,chronological_vis C ops,chronological_paperOrder C E ops,?_,?_,?_⟩
  · exact (chronological_vis C ops).imp (fun {_ _} no edge => no edge.1)
  · rw [fold_live π (Instances.MVR.chronological_sorted ops)
      (fun e he n hn => issued_overwrite_lt execution.mintHonest (supported ((hp.2 e).mp he)) hn)]
    intro p
    rw [mem_live]
    simp only [Born,Dead,List.mem_toFinset,hp.2]
  · exact GuardedHistory.admits_updates_query spec legal_prefix π legal q

end Sal.MRDTs.Paper1.CertifiedMVRHistory
