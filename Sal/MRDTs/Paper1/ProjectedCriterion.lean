import Sal.MRDTs.Paper1.SpecificationVisibility

/-! The stronger candidate criterion with an explicit event-to-application-label
projection. Concrete events, issuance, and the manuscript's paper order are
unchanged; the independent history language sees only the projected labels. -/
namespace Sal.MRDTs.Paper1
open Foundation

def projectedLabels {D : MRDTSig} {U : Type} (project : Op D.AppOp → U)
    (π : List (Op D.AppOp)) : List (SeqLabel U D.Query D.Value) :=
  π.map (fun e => .update (project e))

def projectedSpecVisibility {D : MRDTSig} {U : Type}
    (project : Op D.AppOp → U) (S : HistorySpec U D.Query D.Value)
    (C : ReplayContext D.toUpdateSig) (a b : Op D.AppOp) : Prop :=
  C.vis a b ∧ ¬ S.Commutes (project a) (project b)

def ProjectedSpecificationRALinearizable (D : MRDTSig)
    (P : OperationPolicy D.AppOp) {U : Type} (project : Op D.AppOp → U)
    (S : HistorySpec U D.Query D.Value) (C : Configuration D) : Prop :=
  ∀ r v s E, C.head r = some v → C.ver v = some (s, E) →
    ∀ q, ∃ π : List (Op D.AppOp),
      listPermOf π E ∧ respects π (paperOrder P C.replayContext E) ∧
      respects π (projectedSpecVisibility project S C.replayContext) ∧
      S.admits (projectedLabels project π ++ [.query q (D.query s q)])

theorem projected_original_iff {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {S : HistorySpec D.AppOp D.Query D.Value} {C : Configuration D} :
    ProjectedSpecificationRALinearizable D P Op.op S C ↔
      SpecificationRALinearizable D P S C := by
  rfl


def ProjectedSpecificationExecution (D : MRDTSig) (P : OperationPolicy D.AppOp)
    {U : Type} (project : Op D.AppOp → U) (S : HistorySpec U D.Query D.Value)
    (initial : Configuration D) (trace : List (Label D × Configuration D)) : Prop :=
  ProjectedSpecificationRALinearizable D P project S initial ∧
    ∀ entry ∈ trace, ProjectedSpecificationRALinearizable D P project S entry.2

private theorem execution_invariant (T : LabeledTS) (Inv : T.State → Prop)
    (closed : ∀ s l t, Inv s → T.step s l t → Inv t)
    {initial : T.State} {trace : List (T.Label × T.State)}
    (run : T.Execution initial trace) (start : Inv initial) :
    Inv initial ∧ ∀ entry ∈ trace, Inv entry.2 := by
  induction run with
  | nil => exact ⟨start, by simp⟩
  | @cons s t l tail step run ih =>
      have next := closed s l t start step
      have rest := ih next
      refine ⟨start, ?_⟩
      intro entry he
      rcases List.mem_cons.mp he with rfl | he
      · exact rest.1
      · exact rest.2 entry he

/-- Transfer a guarantee for every honestly certified configuration to every
visited state of a valid honestly certified execution. -/
theorem projected_certified_executions {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {U : Type} {project : Op D.AppOp → U} {S : HistorySpec U D.Query D.Value}
    {I : Issuance D}
    (h : ∀ C, MintCertifiedReach D I C → ProjectedSpecificationRALinearizable D P project S C)
    (trace : List (Label D × Configuration D))
    (execution : (certifiedTS D I).Execution (initConfig D) trace) :
    ProjectedSpecificationExecution D P project S (initConfig D) trace := by
  have visited := execution_invariant (certifiedTS D I) (MintCertifiedReach D I)
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2)
    execution MintCertifiedReach.init
  exact ⟨h _ visited.1, fun entry he => h _ (visited.2 entry he)⟩

theorem projected_certified_executionsV {D : MRDTSig} {P : OperationPolicy D.AppOp}
    {U : Type} {project : Op D.AppOp → U} {S : HistorySpec U D.Query D.Value}
    {I : Issuance D}
    (h : ∀ C, MintCertifiedReachV D (canonicalVirtualMergeBase D) I C →
      ProjectedSpecificationRALinearizable D P project S C)
    (trace : List (Label D × Configuration D))
    (execution : (certifiedTSV D I).Execution (initConfig D) trace) :
    ProjectedSpecificationExecution D P project S (initConfig D) trace := by
  have visited := execution_invariant (certifiedTSV D I)
    (MintCertifiedReachV D (canonicalVirtualMergeBase D) I)
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2)
    execution MintCertifiedReachV.init
  exact ⟨h _ visited.1, fun entry he => h _ (visited.2 entry he)⟩

end Sal.MRDTs.Paper1
