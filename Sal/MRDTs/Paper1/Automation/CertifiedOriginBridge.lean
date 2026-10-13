import Sal.MRDTs.Paper1.Automation.OriginPrefixEvidence
import Sal.MRDTs.Paper1.GuardedHistory

/-! Reconstruct legal causal origins from certified execution evidence, and
connect an independently justified query refinement to a guarded language.
Neither theorem assumes the desired history acceptance or a stored-state bridge. -/
namespace Sal.MRDTs.Paper1.Automation
open Foundation

theorem mint_origin_prefix {D : MRDTSig} [DecidableEq (Op D.AppOp)]
    {I : Issuance D} {C : Configuration D} {E : Set (Op D.AppOp)}
    (materialize : Finset (Op D.AppOp) → D.State)
    (eligible : Op D.AppOp → Finset (Op D.AppOp) → Prop)
    (replay : ∀ ops, applySeq D.toUpdateSig D.init ops = materialize ops.toFinset)
    (issued : ∀ e origin, I.CanIssue e (materialize origin) → eligible e origin)
    (mint : MintHonest D I.CanIssue C)
    (supported : ∀ e ∈ E, e ∈ C.events)
    (closed : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    {ops : List (Op D.AppOp)} (perm : listPermOf ops E)
    (visible : respects ops C.vis) :
    ∀ pre e post, ops = pre ++ e :: post →
      ∃ origin : Finset (Op D.AppOp), origin ⊆ pre.toFinset ∧ eligible e origin := by
  intro pre e post split
  have member : e ∈ E := (perm.2 e).mp (by rw [split]; simp)
  obtain ⟨past, pastPerm, _, guard⟩ := mint e (supported e member)
  refine ⟨past.toFinset, ?_, ?_⟩
  · exact OriginPrefixEvidence.origin_subset_prefix perm visible
      (fun a edge => Nat.lt_irrefl _ (C.causal_mono edge)) closed
      (fun old member => ((pastPerm.2 old).mp member).2) split
  · apply issued e past.toFinset
    rwa [replay] at guard

theorem guarded_replay_witness {D : MRDTSig} (S : SequentialSpec D)
    (prefixClosed : ∀ pre suf, S.Legal (pre ++ suf) → S.Legal pre)
    (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (C : Configuration D) (E : Set (Op D.AppOp)) (ops : List (Op D.AppOp))
    (perm : listPermOf ops E) (visible : respects ops C.vis) (legal : S.Legal ops)
    (observes : ∀ q, D.query (applySeq D.toUpdateSig D.init ops) q =
      S.query (S.run ops) q) (q : D.Query) :
    listPermOf ops E ∧ respects ops (paperOrder (commutingPolicy D.AppOp) C.replayContext E) ∧
      respects ops (projectedSpecVisibility id (GuardedHistory.language S) C.replayContext) ∧
      (GuardedHistory.language S).admits (projectedLabels id ops ++
        [.query q (D.query (applySeq D.toUpdateSig D.init ops) q)]) := by
  refine ⟨perm, ?_, visible.imp (fun {_ _} h edge => h edge.1), ?_⟩
  · apply List.pairwise_of_forall
    intro a b
    exact paperOrder_false_of_all_commute commute C.replayContext E b a
  · rw [observes]
    exact GuardedHistory.admits_updates_query S prefixClosed ops legal q

end Sal.MRDTs.Paper1.Automation
