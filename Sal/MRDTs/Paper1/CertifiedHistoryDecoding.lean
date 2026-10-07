import Sal.MRDTs.Paper1.GuardedHistory

/-! Decode a finite update/query history in the independent sequential machine.
This supports exhaustive counterexample checks against the history language
rather than substituting an unrelated executable predicate. -/
namespace Sal.MRDTs.Paper1.GuardedHistory
open Foundation
variable {D : MRDTSig}

private theorem decode_updates (S : SequentialSpec D) (emptyLegal : S.Legal [])
    (ops : List (Op D.AppOp)) {finish : (machine S).State}
    (run : Runs (machine S).transition ([],S.init) (projectedLabels id ops) finish) :
    finish = (ops,S.run ops) ∧ S.Legal ops := by
  induction ops using List.reverseRecOn generalizing finish with
  | nil =>
    cases run
    exact ⟨rfl,emptyLegal⟩
  | append_singleton ops e ih =>
    have split : Runs (machine S).transition ([],S.init)
        (projectedLabels id ops ++ [.update e]) finish := by
      simpa only [projectedLabels,List.map_append,List.map_cons,List.map_nil] using run
    obtain ⟨mid,before,last⟩ := split.split _ _
    obtain ⟨rfl,_⟩ := ih before
    cases last with
    | cons step rest =>
      obtain ⟨legal,rfl⟩ := step
      cases rest
      exact ⟨by simp [SequentialSpec.run,SequentialMachine.run,List.foldl_append],legal⟩

/-- Acceptance of an update-only prefix followed by one query is exactly
original sequential legality and the original sequential query result. -/
theorem admits_updates_query_iff (S : SequentialSpec D)
    (emptyLegal : S.Legal [])
    (prefixClosed : ∀ pre suf, S.Legal (pre ++ suf) → S.Legal pre)
    (ops : List (Op D.AppOp)) (q : D.Query) (answer : D.Value) :
    (language S).admits (projectedLabels id ops ++ [.query q answer]) ↔
      S.Legal ops ∧ answer = S.query (S.run ops) q := by
  constructor
  · rintro ⟨finish,run⟩
    obtain ⟨mid,updates,last⟩ := run.split (projectedLabels id ops) [.query q answer]
    obtain ⟨rfl,legal⟩ := decode_updates S emptyLegal ops updates
    cases last with
    | cons step rest => exact ⟨legal,step.1⟩
  · rintro ⟨legal,rfl⟩
    exact admits_updates_query S prefixClosed ops legal q

end Sal.MRDTs.Paper1.GuardedHistory
