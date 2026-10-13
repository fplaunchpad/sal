import Sal.MRDTs.Framework.GuardedStateProjection
import Sal.MRDTs.Paper1.ProjectedSimulation
import Sal.MRDTs.Paper1.Automation.CertifiedOriginBridge

/-! Derive language acceptance from a guarded state projection. Legal witness
selection and execution/issuance evidence remain explicit inputs; the independent
machine's transitions and observations are preserved. -/
namespace Sal.MRDTs
open Foundation

namespace GuardedStateProjection
open Paper1
variable {D : MRDTSig} {S : SequentialSpec D}

theorem admits (H : GuardedStateProjection D S) (ops : List (Op D.AppOp))
    (legal : S.Legal ops) (q : D.Query) :
    (GuardedHistory.language S).admits (projectedLabels id ops ++
      [.query q (D.query (applySeq D.toUpdateSig D.init ops) q)]) := by
  rw [H.query_agrees ops legal q]
  exact GuardedHistory.admits_updates_query S H.prefix_closed ops legal q

theorem witness (H : GuardedStateProjection D S)
    (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (C : Configuration D) (E : Set (Op D.AppOp)) (ops : List (Op D.AppOp))
    (perm : listPermOf ops E) (visible : respects ops C.vis) (legal : S.Legal ops)
    (q : D.Query) :
    listPermOf ops E ∧ respects ops (paperOrder (commutingPolicy D.AppOp) C.replayContext E) ∧
      respects ops (projectedSpecVisibility id (GuardedHistory.language S) C.replayContext) ∧
      (GuardedHistory.language S).admits (projectedLabels id ops ++
        [.query q (D.query (applySeq D.toUpdateSig D.init ops) q)]) :=
  Automation.guarded_replay_witness S H.prefix_closed commute C E ops perm visible legal
    (H.query_agrees ops legal) q

end GuardedStateProjection

namespace Paper1

/-- View an independently supplied total machine through the full event
alphabet. No implementation data enter this specification. -/
def projectionSequentialSpec {D : MRDTSig} {U : Type}
    (M : DeterministicSpec U D.Query D.Value) (label : Op D.AppOp → U) : SequentialSpec D where
  State := M.State
  init := M.initial
  step s e := M.update s (label e)
  Legal _ := True
  query := M.query

/-- Total OR-set-style projections are the unrestricted special case. -/
def MachineProjection.toGuarded {D : MRDTSig} {U : Type}
    {M : DeterministicSpec U D.Query D.Value} {label : Op D.AppOp → U}
    (H : MachineProjection D M label) :
    GuardedStateProjection D (projectionSequentialSpec M label) where
  Inv _ _ := True
  project := H.project
  prefix_closed _ _ _ := True.intro
  inv_initial := True.intro
  inv_update _ _ _ _ _ := True.intro
  initial := H.initial
  update _ s e _ _ := H.update s e
  observes _ s _ q := H.observes s q

end Paper1
end Sal.MRDTs
