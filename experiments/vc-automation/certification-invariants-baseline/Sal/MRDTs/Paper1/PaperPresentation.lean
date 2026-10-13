import Sal.MRDTs.Paper1.RALinearizability
import Sal.MRDTs.Paper1.InvariantOrder

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

/-- The manuscript's unrestricted lifting theorem, including specification
visibility and an explicit update-label projection. The same exact word works
for every query, with no repeated replay-law premise in the lifting step. -/
theorem projected_versions_of_exact_total
    {D : MRDTSig} {P : OperationPolicy D.AppOp} {U : Type}
    {f : Op D.AppOp → U} {S : HistorySpec U D.Query D.Value} {C : Configuration D}
    (_order_irrefl : ∀ v s E, C.ver v = some (s,E) →
      ∀ e ∈ E, ¬ paperOrder P C.replayContext E e e)
    (witness : ∀ v s E, C.ver v = some (s,E) →
      ∃ π : List (Op D.AppOp), listPermOf π E ∧
        respects π (paperOrder P C.replayContext E) ∧
        applySeq D.toUpdateSig D.init π = s)
    (sound : ∀ π q, S.admits (projectedLabels f π ++
      [.query q (D.query (applySeq D.toUpdateSig D.init π) q)]))
    (compatible : CommutationCompatibility D f S) :
    ∀ v s E, C.ver v = some (s,E) →
      ∃ π : List (Op D.AppOp), listPermOf π E ∧
        respects π (paperOrder P C.replayContext E) ∧
        respects π (projectedSpecVisibility f S C.replayContext) ∧
        ∀ q, S.admits (projectedLabels f π ++ [.query q (D.query s q)]) := by
  intro v s E stored
  obtain ⟨π,perm,order,fold⟩ := witness v s E stored
  refine ⟨π,perm,order,?_,?_⟩
  · exact order.imp (fun {_ _} h => h ∘
      projectedSpecVisibility_sub_paperOrder compatible C.replayContext E _ _)
  · intro q
    simpa only [fold] using sound π q

#print axioms projected_versions_of_exact_total

/-- A chosen exact replay can explain a guarded sequential history without
requiring all public-order linear extensions to have the same fold. Issuance,
representation and invariant closure are established by each port upstream.
The explicit diagonal condition aligns `respects` with strict linear extensions. -/
theorem invariant_versions_of_exact_histories
    {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {C : Configuration D}
    {I : D.State → Prop}
    (_order_irrefl : ∀ v s E, C.ver v = some (s,E) →
      ∀ e ∈ E, ¬ InvariantOrder.order I P C.replayContext E e e)
    (history : ∀ v s E, C.ver v = some (s,E) → ∀ q,
      ∃ π : List (Op D.AppOp), listPermOf π E ∧
        respects π (InvariantOrder.order I P C.replayContext E) ∧
        respects π (projectedSpecVisibility id S C.replayContext) ∧
        applySeq D.toUpdateSig D.init π = s ∧
        S.admits (projectedLabels id π ++
          [.query q (D.query (applySeq D.toUpdateSig D.init π) q)])) :
    InvariantOrder.VersionsRA D I P S C := by
  intro v s E stored q
  obtain ⟨π,perm,ordered,visible,fold,accepted⟩ := history v s E stored q
  exact ⟨π,perm,ordered,visible,by simpa only [fold] using accepted⟩

#print axioms invariant_versions_of_exact_histories
end Sal.MRDTs.Paper1.PaperPresentation
