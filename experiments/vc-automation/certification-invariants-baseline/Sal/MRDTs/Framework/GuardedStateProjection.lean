import Sal.MRDTs.Framework.Certificates
import Sal.MRDTs.Framework.SequentialInduction

/-! A proof-only simulation into an independently supplied sequential machine.
The invariant describes justified concrete states at a history prefix. The
transition law is required only for such states and legal extensions; neither
the implementation equality nor the sequential specification is redefined. -/
namespace Sal.MRDTs
open Foundation

structure GuardedStateProjection (D : MRDTSig) (S : SequentialSpec D) where
  Inv : List (Op D.AppOp) → D.State → Prop
  project : D.State → S.State
  prefix_closed : ∀ pre suf, S.Legal (pre ++ suf) → S.Legal pre
  inv_initial : Inv [] D.init
  inv_update : ∀ pre s e, Inv pre s → S.Legal (pre ++ [e]) →
    Inv (pre ++ [e]) (D.update s e)
  initial : project D.init = S.init
  update : ∀ pre s e, Inv pre s → S.Legal (pre ++ [e]) →
    project (D.update s e) = S.step (project s) e
  observes : ∀ pre s, Inv pre s → ∀ q, D.query s q = S.query (project s) q

namespace GuardedStateProjection
variable {D : MRDTSig} {S : SequentialSpec D}

def Rel (H : GuardedStateProjection D S) (s : D.State) (a : S.State) : Prop :=
  H.project s = a

theorem local_simulates (H : GuardedStateProjection D S)
    {pre : List (Op D.AppOp)} {s : D.State} {a : S.State} {e : Op D.AppOp}
    (inv : H.Inv pre s) (rel : H.Rel s a) (legal : S.Legal (pre ++ [e])) :
    H.Rel (D.update s e) (S.step a e) := by
  change H.project s = a at rel
  subst a
  exact H.update pre s e inv legal

theorem run_facts (H : GuardedStateProjection D S) (ops : List (Op D.AppOp))
    (legal : S.Legal ops) :
    H.Inv ops (applySeq D.toUpdateSig D.init ops) ∧
      H.project (applySeq D.toUpdateSig D.init ops) = S.run ops := by
  apply legal_snoc_induction (Legal := S.Legal)
    (Inv := fun pre => H.Inv pre (applySeq D.toUpdateSig D.init pre) ∧
      H.project (applySeq D.toUpdateSig D.init pre) = S.run pre)
    (fun pre e h => H.prefix_closed pre [e] h) ?_ ?_ legal
  · exact ⟨H.inv_initial, H.initial⟩
  · intro pre e h facts
    rw [applySeq_append_single, SequentialSpec.run_append_single]
    refine ⟨H.inv_update pre _ e facts.1 h, ?_⟩
    rw [H.update pre _ e facts.1 h, facts.2]

theorem run_invariant (H : GuardedStateProjection D S) (ops : List (Op D.AppOp))
    (legal : S.Legal ops) : H.Inv ops (applySeq D.toUpdateSig D.init ops) :=
  (H.run_facts ops legal).1

theorem run_project (H : GuardedStateProjection D S) (ops : List (Op D.AppOp))
    (legal : S.Legal ops) : H.project (applySeq D.toUpdateSig D.init ops) = S.run ops :=
  (H.run_facts ops legal).2

theorem query_agrees (H : GuardedStateProjection D S) (ops : List (Op D.AppOp))
    (legal : S.Legal ops) (q : D.Query) :
    D.query (applySeq D.toUpdateSig D.init ops) q = S.query (S.run ops) q := by
  rw [H.observes ops _ (H.run_invariant ops legal) q, H.run_project ops legal]

/-- Strengthening the accepted history discipline requires no new state or
transition proof. The machine, query and represented-state relation stay fixed. -/
def restrict (H : GuardedStateProjection D S) (Legal : List (Op D.AppOp) → Prop)
    (prefix_closed : ∀ pre suf, Legal (pre ++ suf) → Legal pre)
    (implies : ∀ ops, Legal ops → S.Legal ops) :
    GuardedStateProjection D { S with Legal := Legal } where
  Inv := H.Inv
  project := H.project
  prefix_closed := prefix_closed
  inv_initial := H.inv_initial
  inv_update pre s e inv legal := H.inv_update pre s e inv (implies _ legal)
  initial := H.initial
  update pre s e inv legal := H.update pre s e inv (implies _ legal)
  observes := H.observes

end GuardedStateProjection
end Sal.MRDTs
