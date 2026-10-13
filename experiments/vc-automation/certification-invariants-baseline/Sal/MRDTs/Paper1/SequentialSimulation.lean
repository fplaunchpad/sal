import Sal.MRDTs.Paper1.RALinearizability

/-! A local simulation is a sufficient, merge-free proof of the paper's
all-history sequential premise. The public specification remains a language;
the representation relation is only a proof tool. -/

namespace Sal.MRDTs.Paper1
open Foundation

structure SequentialSimulation (D : MRDTSig)
    (M : DeterministicSpec D.AppOp D.Query D.Value) where
  Rel : D.State → M.State → Prop
  initial : Rel D.init M.initial
  update : ∀ s a, Rel s a → ∀ e : Op D.AppOp,
    Rel (D.update s e) (M.update a e.op)
  observes : ∀ s a, Rel s a → ∀ q, D.query s q = M.query a q

namespace SequentialSimulation

theorem fold_rel {D : MRDTSig} {M : DeterministicSpec D.AppOp D.Query D.Value}
    (H : SequentialSimulation D M) (π : List (Op D.AppOp))
    (s : D.State) (a : M.State) (h : H.Rel s a) :
    H.Rel (applySeq D.toUpdateSig s π) ((π.map Op.op).foldl M.update a) := by
  induction π generalizing s a with
  | nil => exact h
  | cons e π ih => exact ih (D.update s e) (M.update a e.op) (H.update s a h e)

theorem sound {D : MRDTSig} {M : DeterministicSpec D.AppOp D.Query D.Value}
    (H : SequentialSimulation D M) : FoldHistorySound D M.toSpec := by
  intro π q
  have labels : projectedUpdates (D := D) π =
      DeterministicSpec.updateLabels (Q := D.Query) (V := D.Value) (π.map Op.op) := by
    simp [projectedUpdates, DeterministicSpec.updateLabels, List.map_map]
  rw [labels, M.updates_query_iff]
  exact H.observes _ _ (H.fold_rel π D.init M.initial H.initial) q

end SequentialSimulation
end Sal.MRDTs.Paper1
