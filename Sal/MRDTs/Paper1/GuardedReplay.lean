import Sal.MRDTs.Paper1.RestrictedReplay

/-!
# Event-guarded laws for the semantic paper order

The user supplies an operation policy; event comparisons project to payloads.
Exactness is required only at distinct timestamps and different replicas.
The conditional law below uses actual noncommutation, matching the absorber in
`paperOrder`. It follows from the payload conditional-commutation assumption
in Neem's manuscript (`_references/Neem/lin.tex`, definitions of payload
commutation and conditional commutation). Neem's F* interface instead uses
policy conflict at this position, which is not interchangeable with actual
noncommutation outside the exactness guard. We do not claim that the guarded
F* obligations alone imply this contract.
-/

namespace Sal.MRDTs.Paper1.GuardedReplay
open Foundation

structure Laws (D : UpdateSig) (P : OperationPolicy D.AppOp) : Prop where
  noncomm_exact : ∀ a b : Op D.AppOp,
    distinctOps a b → a.rep ≠ b.rep →
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

/-- Earlier uniform certificates imply these guarded sufficient conditions. -/
def ofUniform {D : UpdateSig} {P : OperationPolicy D.AppOp}
    (L : RestrictedLaws D P) : Laws D P where
  noncomm_exact a b _ _ := L.noncomm_exact a b
  no_chain a b c _ _ := L.no_chain a.op b.op c.op
  conditional_commutation s a b c between _ _ _ :=
    L.conditional_commutation s a b c between

end Sal.MRDTs.Paper1.GuardedReplay
