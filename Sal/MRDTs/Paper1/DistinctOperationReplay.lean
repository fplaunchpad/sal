import Sal.MRDTs.Paper1.ConcreteReplay

/-! A proposed distinct-application-operation exactness law. It does not by
itself justify exchanging equal-payload events. The explicit repair below
recovers the existing replay theorem without changing concrete commutation. -/
namespace Sal.MRDTs.Paper1.DistinctOperationReplay
open Foundation

structure Laws (D : UpdateSig) (P : OperationPolicy D.AppOp) : Prop where
  noncomm_exact : ∀ a b : Op D.AppOp, a.op ≠ b.op →
    (¬ D.commutes a b ↔ P.before a.op b.op ∨ P.before b.op a.op)
  no_chain : ∀ a b c : Op D.AppOp,
    distinctOps a b → distinctOps b c →
    ¬ (P.before a.op b.op ∧ P.before b.op c.op)
  conditional_commutation :
    ∀ (s : D.State) (a b c : Op D.AppOp) (between : List (Op D.AppOp)),
    distinctOps a b → distinctOps a c → distinctOps b c →
    P.before a.op b.op → ¬ D.commutes b c →
    D.update (applySeq D (D.update (D.update s b) a) between) c =
      D.update (applySeq D (D.update (D.update s a) b) between) c

variable {D : UpdateSig} {P : OperationPolicy D.AppOp}

theorem policy_irrefl (L : Laws D P) (x : D.AppOp) : ¬ P.before x x := by
  have no := L.no_chain (0,0,x) (1,0,x) (2,0,x)
    (by simp [distinctOps, Op.time]) (by simp [distinctOps, Op.time])
  exact fun h => no ⟨h,h⟩

/-- A sufficient global repair. Same-replica pairs are deliberately excluded:
their actual noncommutation still creates the required causal order edge.
The certified alternative needs only its existing represented-state diamond. -/
def EqualOperationCommutes (D : UpdateSig) : Prop :=
  ∀ a b : Op D.AppOp, distinctOps a b → a.rep ≠ b.rep → a.op = b.op → D.commutes a b

def Laws.toGuarded (L : Laws D P) (equal : EqualOperationCommutes D) :
    GuardedReplay.Laws D P where
  noncomm_exact a b distinct replica := by
    by_cases same : a.op = b.op
    · have commute := equal a b distinct replica same
      simp [commute, same, policy_irrefl L]
    · exact L.noncomm_exact a b same
  no_chain := L.no_chain
  conditional_commutation := L.conditional_commutation

theorem replay_equal {D : MRDTSig} {P : OperationPolicy D.AppOp}
    (L : Laws D.toUpdateSig P) (equal : EqualOperationCommutes D.toUpdateSig)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp))
    (supported : ConcreteMRDT.Supported C E) (s : D.State)
    {left right : List (Op D.AppOp)}
    (hl : listPermOf left E) (hr : listPermOf right E)
    (ol : respects left (paperOrder P C E))
    (or : respects right (paperOrder P C E)) :
    applySeq D.toUpdateSig s left = applySeq D.toUpdateSig s right :=
  ConcreteMRDT.replay_equal (L.toGuarded equal) C E supported s hl hr ol or

end Sal.MRDTs.Paper1.DistinctOperationReplay
