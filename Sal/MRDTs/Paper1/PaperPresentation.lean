import Sal.MRDTs.Paper1.RALinearizability

/-! The paper-facing sequential lifting theorem uses the public semantic order
in its witness premise. No replay law is needed to reuse that witness in the
sequential specification. Replay laws belong to the separate proof that stored
states possess such witnesses. -/
namespace Sal.MRDTs.Paper1.PaperPresentation
open Foundation

/-- An exact witness in the public paper order, together with total sequential
fold soundness and an irreflexive order on each stored event set, explains
every query at every stored version using one word.
This removes the uniform replay-law premise needed by the older theorem only
to translate its framework-order witness to the public paper order.
The explicit irreflexivity premise matches the manuscript convention: the
underlying `respects` predicate itself compares only distinct list positions. -/
theorem uniform_versionsRA_of_paperOrder_witness
    {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec D.AppOp D.Query D.Value} {C : Configuration D}
    (_h_order_irrefl : ∀ v s E, C.ver v = some (s,E) →
      ∀ e ∈ E, ¬ paperOrder P C.replayContext E e e)
    (witness : ∀ v s E, C.ver v = some (s,E) →
      ∃ π : List (Op D.AppOp), listPermOf π E ∧
        respects π (paperOrder P C.replayContext E) ∧
        applySeq D.toUpdateSig D.init π = s)
    (sound : FoldHistorySound D S) : UniformVersionsRALinearizable D P S C := by
  intro v s E hv
  obtain ⟨π, hp, ho, hf⟩ := witness v s E hv
  refine ⟨π, hp, ho, ?_⟩
  intro q
  simpa only [hf] using sound π q

#print axioms uniform_versionsRA_of_paperOrder_witness
end Sal.MRDTs.Paper1.PaperPresentation
