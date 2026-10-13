import Sal.MRDTs.Paper1.EventBridge

/-! Turn a production independent sequential machine and prefix-closed public
legality contract into a history language. The remembered prefix is abstract
legality bookkeeping, not an implementation state or stored-version replay. -/
namespace Sal.MRDTs.Paper1
open Foundation

namespace GuardedHistory

def machine {D : MRDTSig} (S : SequentialSpec D) :
    HistoryMachine (Op D.AppOp) D.Query D.Value where
  State := List (Op D.AppOp) × S.State
  initial := ([], S.init)
  transition s label t := match label with
    | .update e => S.Legal (s.1 ++ [e]) ∧ t = (s.1 ++ [e], S.step s.2 e)
    | .query q answer => answer = S.query s.2 q ∧ t = s

def language {D : MRDTSig} (S : SequentialSpec D) := (machine S).toSpec

theorem updates_run {D : MRDTSig} (S : SequentialSpec D)
    (prefixClosed : ∀ pre suf, S.Legal (pre ++ suf) → S.Legal pre)
    (ops : List (Op D.AppOp)) (legal : S.Legal ops) :
    Runs (machine S).transition ([], S.init)
      (projectedLabels (D := D) id ops) (ops, S.run ops) := by
  induction ops using List.reverseRecOn with
  | nil => exact .nil _
  | append_singleton ops e ih =>
      have hp := prefixClosed ops [e] legal
      have step : (machine S).transition (ops,S.run ops) (.update e)
          (ops ++ [e], S.run (ops ++ [e])) := by
        exact ⟨legal, by simp [SequentialSpec.run, SequentialMachine.run, List.foldl_append]⟩
      simpa only [projectedLabels, List.map_append, List.map_cons, List.map_nil] using
        (ih hp).append (.cons step (.nil _))

theorem admits_updates_query {D : MRDTSig} (S : SequentialSpec D)
    (prefixClosed : ∀ pre suf, S.Legal (pre ++ suf) → S.Legal pre)
    (ops : List (Op D.AppOp)) (legal : S.Legal ops) (q : D.Query) :
    (language S).admits (projectedLabels id ops ++ [.query q (S.query (S.run ops) q)]) :=
  ⟨(ops,S.run ops), (updates_run S prefixClosed ops legal).append
    (.cons ⟨rfl,rfl⟩ (.nil _))⟩

/-- The final recorded abstract history is exactly the sequence of updates,
including across intervening queries. -/
theorem recorded_prefix {D : MRDTSig} (S : SequentialSpec D)
    {s t : (machine S).State} {ls : List (SeqLabel (Op D.AppOp) D.Query D.Value)}
    (run : Runs (machine S).transition s ls t) :
    t.1 = s.1 ++ ls.filterMap (fun l => match l with
      | .update e => some e | .query _ _ => none) := by
  induction run with
  | nil => simp
  | @cons s mid t label tail step rest ih =>
      cases label with
      | update e =>
          obtain ⟨_,rfl⟩ := step
          simpa [List.append_assoc] using ih
      | query q answer =>
          obtain ⟨_,rfl⟩ := step
          simpa using ih

theorem rejects_first_update {D : MRDTSig} (S : SequentialSpec D)
    (e : Op D.AppOp) (illegal : ¬ S.Legal [e])
    (tail : List (SeqLabel (Op D.AppOp) D.Query D.Value)) :
    ¬ (language S).admits (.update e :: tail) := by
  rintro ⟨t,run⟩
  cases run with
  | cons step _ => exact illegal step.1

end GuardedHistory

/-- A production independent sequential certificate supplies an admitted
full-input history. Its legality contract must preserve visibility; all
concrete updates commute, so the paper replay order is empty. -/
theorem event_versions_of_guarded_certificate {D : MRDTSig} {I : Issuance D}
    {S : SequentialSpec D} {Rel : D.State → S.State → Prop}
    (certificate : SequentialCorrectnessCertificate D I
      (ReplayPolicy.unconstrained D.toUpdateSig) S Rel)
    (prefixClosed : ∀ pre suf, S.Legal (pre ++ suf) → S.Legal pre)
    (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (join : ∀ C, MintHonest D I.CanIssue C →
      @JoinAt D (ReplayPolicy.unconstrained D.toUpdateSig) C.replayContext)
    (visible : ∀ C : Configuration D, ∀ ops, S.Legal ops → respects ops C.vis)
    {C : Configuration D} (exec : CertifiedExecution D I C) :
    EventVersionsSpecificationRA D (commutingPolicy D.AppOp) (GuardedHistory.language S) C := by
  letI : ReplayPolicy D.toUpdateSig := ReplayPolicy.unconstrained D.toUpdateSig
  have replay := hasReplayWitness_of_canonical (exec.canonicalConfig join)
  intro v s E hv q
  obtain ⟨π,hp,_,legal,_,observes⟩ := certificate.sound C exec replay v s E hv
  refine ⟨π,hp,?_,?_,?_⟩
  · unfold respects
    apply List.pairwise_of_forall
    intro a b
    exact paperOrder_false_of_all_commute commute C.replayContext E b a
  · exact (visible C π legal).imp (fun {_ _} h => fun edge => h edge.1)
  · rw [observes q]
    exact GuardedHistory.admits_updates_query S prefixClosed π legal q

end Sal.MRDTs.Paper1
