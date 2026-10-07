import Sal.MRDTs.Paper1.EventBridge
import Sal.MRDTs.Paper1.CertifiedReplay

/-! Payload policy restrictions at certified replay scope. These conditions
are distinct from the diamond theorem's algebraic hypotheses. Exactness is
needed only for concurrent eligible events and compares their effects on
represented prefixes at which both are ready. No-chain retains both original
timestamp guards, including the possible triple (a,b,a). Original issuance is
checked at mint origins; readiness is not a claim of reissuability. -/
namespace Sal.MRDTs.Paper1.CertifiedReplay
open Foundation
variable {D : UpdateSig}

def Commutes (S : Scope D) (a b : Op D.AppOp) : Prop :=
  ∀ H s, S.represented H s → Ready S H a → Ready S H b →
    D.update (D.update s a) b = D.update (D.update s b) a

structure PolicyLaws (S : Scope D) (P : OperationPolicy D.AppOp) : Prop where
  concurrent_exact : ∀ a b, a ∈ S.events → b ∈ S.events →
    distinctOps a b → a.rep ≠ b.rep →
    ¬ S.context.vis a b → ¬ S.context.vis b a →
    (¬ Commutes S a b ↔ P.before a.op b.op ∨ P.before b.op a.op)
  no_chain : ∀ a b c, a ∈ S.events → b ∈ S.events → c ∈ S.events →
    distinctOps a b → distinctOps b c →
    ¬ (P.before a.op b.op ∧ P.before b.op c.op)

/-- Concurrent raw commutation is a stronger sufficient hypothesis for the
empty payload policy. No arbitrary-state commutation is required by the
policy contract itself. -/
theorem emptyPolicyLaws (S : Scope D)
    (commute : ∀ a b, a ∈ S.events → b ∈ S.events →
      ¬ S.context.vis a b → ¬ S.context.vis b a → Commutes S a b) :
    PolicyLaws S (commutingPolicy D.AppOp) where
  concurrent_exact a b ha hb _ _ hv hw := by
    simp [commutingPolicy,commute a b ha hb hv hw]
  no_chain _ _ _ _ _ _ _ _ := by simp [commutingPolicy]

/-- In the empty-policy case the original semantic order only has causal
edges, so the scoped replay diamonds discharge local policy exactness. -/
theorem emptyPolicyLaws_of_diamonds (S : Scope D)
    (laws : Laws S (commutingPolicy D.AppOp)) :
    PolicyLaws S (commutingPolicy D.AppOp) := by
  apply emptyPolicyLaws S
  intro a b _ _ notab notba H s represented readyA readyB
  exact laws.diamond H s a b represented readyA readyB notab notba
    (by simp [paperOrder,commutingPolicy,notab])
    (by simp [paperOrder,commutingPolicy,notba])

/-- The certified sufficient class keeps policy restrictions explicit alongside
its represented-state update and exchange equations. -/
structure RestrictedLaws (S : Scope D) (P : OperationPolicy D.AppOp) : Prop where
  replay : Laws S P
  policy : PolicyLaws S P

def restrictedEmpty (S : Scope D) (laws : Laws S (commutingPolicy D.AppOp)) :
    RestrictedLaws S (commutingPolicy D.AppOp) :=
  ⟨laws,emptyPolicyLaws_of_diamonds S laws⟩

end Sal.MRDTs.Paper1.CertifiedReplay
