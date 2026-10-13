import Sal.MRDTs.Paper1.ConcreteReplay
import Sal.MRDTs.Paper1.InvariantReplay
import Sal.MRDTs.Paper1.CertifiedPolicy

/-! The paper-facing split policy is equivalent to the previous combined
exactness contract on precisely the same domains. Equal application payloads
retain distinct event metadata. No-chain retains the repeated endpoint (a,b,a);
the causal/absorber relation and conditional-commutation premise are unchanged. -/
namespace Sal.MRDTs.Paper1.SplitPolicy
open Foundation
variable {D : UpdateSig} {P : OperationPolicy D.AppOp}

/-- Equal-payload commutation on arbitrary states, with the original event guards. -/
def EqualOperationCommutes (D : UpdateSig) : Prop :=
  ∀ a b : Op D.AppOp, distinctOps a b → a.rep ≠ b.rep → a.op = b.op → D.commutes a b

/-- Payload-distinct exactness with precisely the former metadata guards. -/
structure EventDistinctLaws (D : UpdateSig) (P : OperationPolicy D.AppOp) : Prop where
  noncomm_exact : ∀ a b : Op D.AppOp, distinctOps a b → a.rep ≠ b.rep →
    a.op ≠ b.op → (¬ D.commutes a b ↔ P.before a.op b.op ∨ P.before b.op a.op)
  no_chain : ∀ a b c : Op D.AppOp, distinctOps a b → distinctOps b c →
    ¬ (P.before a.op b.op ∧ P.before b.op c.op)
  conditional_commutation :
    ∀ (s : D.State) (a b c : Op D.AppOp) (between : List (Op D.AppOp)),
    distinctOps a b → distinctOps a c → distinctOps b c →
    P.before a.op b.op → ¬ D.commutes b c →
    D.update (applySeq D (D.update (D.update s b) a) between) c =
      D.update (applySeq D (D.update (D.update s a) b) between) c

theorem guarded_policy_irrefl (L : GuardedReplay.Laws D P) (x : D.AppOp) :
    ¬ P.before x x := by
  have no := L.no_chain (0,0,x) (1,0,x) (2,0,x)
    (by simp [distinctOps, Op.time]) (by simp [distinctOps, Op.time])
  exact fun h => no ⟨h,h⟩

theorem guarded_self_commutation (L : GuardedReplay.Laws D P) :
    EqualOperationCommutes D := by
  classical
  intro a b distinct replica same
  by_contra bad
  have edge := (L.noncomm_exact a b distinct replica).mp bad
  simpa [same, guarded_policy_irrefl L] using edge

def guarded_to_distinct (L : GuardedReplay.Laws D P) : EventDistinctLaws D P where
  noncomm_exact a b distinct replica _ := L.noncomm_exact a b distinct replica
  no_chain := L.no_chain
  conditional_commutation := L.conditional_commutation

def distinct_to_guarded (L : EventDistinctLaws D P)
    (self : EqualOperationCommutes D) : GuardedReplay.Laws D P where
  noncomm_exact a b distinct replica := by
    by_cases same : a.op = b.op
    · have no := L.no_chain a b a distinct (by
        simpa [distinctOps, Op.time, ne_comm] using distinct)
      have diagonal : ¬ P.before b.op b.op := fun h => no (by simpa [same] using And.intro h h)
      simp [self a b distinct replica same, same, diagonal]
    · exact L.noncomm_exact a b distinct replica same
  no_chain := L.no_chain
  conditional_commutation := L.conditional_commutation

theorem guarded_iff_repaired : GuardedReplay.Laws D P ↔
    EventDistinctLaws D P ∧ EqualOperationCommutes D :=
  ⟨fun L => ⟨guarded_to_distinct L, guarded_self_commutation L⟩,
    fun ⟨L,self⟩ => distinct_to_guarded L self⟩

/-- Raw paper contract: distinct-payload exactness and equal-payload commutation. -/
structure Laws (D : UpdateSig) (P : OperationPolicy D.AppOp) : Prop extends EventDistinctLaws D P where
  self_commutation : EqualOperationCommutes D

def Laws.toGuarded (L : Laws D P) : GuardedReplay.Laws D P :=
  distinct_to_guarded L.toEventDistinctLaws L.self_commutation

def Laws.ofGuarded (L : GuardedReplay.Laws D P) : Laws D P :=
  ⟨guarded_to_distinct L, guarded_self_commutation L⟩

theorem laws_iff_guarded : Laws D P ↔ GuardedReplay.Laws D P :=
  ⟨Laws.toGuarded, Laws.ofGuarded⟩

namespace Certified
variable {S : CertifiedReplay.Scope D}

/-- Exactly the equal-payload portion removed from concurrent exactness. -/
def SelfCommutes (S : CertifiedReplay.Scope D) : Prop :=
  ∀ a b, a ∈ S.events → b ∈ S.events → distinctOps a b → a.rep ≠ b.rep →
    ¬ S.context.vis a b → ¬ S.context.vis b a → a.op = b.op →
    CertifiedReplay.Commutes S a b

theorem existing_self_commutation (L : CertifiedReplay.PolicyLaws S P) :
    SelfCommutes S := by
  classical
  intro a b ha hb distinct replica notab notba same
  by_contra bad
  have edge := (L.concurrent_exact a b ha hb distinct replica notab notba).mp bad
  have no := L.no_chain a b a ha hb ha distinct (by
    simpa [distinctOps, Op.time, ne_comm] using distinct)
  have diagonal : P.before b.op b.op := by simpa [same] using edge
  exact no (by simpa [same] using And.intro diagonal diagonal)

/-- The revised exactness domain keeps metadata guards. Removing them is
a stronger premise unless event support is proved explicitly. -/
structure EventDistinctPolicy (S : CertifiedReplay.Scope D) (P : OperationPolicy D.AppOp) : Prop where
  concurrent_exact : ∀ a b, a ∈ S.events → b ∈ S.events →
    distinctOps a b → a.rep ≠ b.rep → a.op ≠ b.op →
    ¬ S.context.vis a b → ¬ S.context.vis b a →
    (¬ CertifiedReplay.Commutes S a b ↔ P.before a.op b.op ∨ P.before b.op a.op)
  no_chain : ∀ a b c, a ∈ S.events → b ∈ S.events → c ∈ S.events →
    distinctOps a b → distinctOps b c → ¬ (P.before a.op b.op ∧ P.before b.op c.op)

def existing_to_distinct (L : CertifiedReplay.PolicyLaws S P) : EventDistinctPolicy S P where
  concurrent_exact a b ha hb distinct replica _ := L.concurrent_exact a b ha hb distinct replica
  no_chain := L.no_chain

def repaired_to_existing (L : EventDistinctPolicy S P) (self : SelfCommutes S) :
    CertifiedReplay.PolicyLaws S P where
  concurrent_exact a b ha hb distinct replica notab notba := by
    by_cases same : a.op = b.op
    · have no := L.no_chain a b a ha hb ha distinct (by
        simpa [distinctOps, Op.time, ne_comm] using distinct)
      have diagonal : ¬ P.before b.op b.op := fun h => no (by simpa [same] using And.intro h h)
      simp [self a b ha hb distinct replica notab notba same, same, diagonal]
    · exact L.concurrent_exact a b ha hb distinct replica same notab notba
  no_chain := L.no_chain

theorem existing_iff_repaired : CertifiedReplay.PolicyLaws S P ↔
    EventDistinctPolicy S P ∧ SelfCommutes S :=
  ⟨fun L => ⟨existing_to_distinct L, existing_self_commutation L⟩,
    fun ⟨L,self⟩ => repaired_to_existing L self⟩

/-- Split policy with exactly the prior scope and state domain. -/
structure PolicyLaws (S : CertifiedReplay.Scope D)
    (P : OperationPolicy D.AppOp) : Prop extends EventDistinctPolicy S P where
  self_commutation : SelfCommutes S

def PolicyLaws.toExisting (L : PolicyLaws S P) : CertifiedReplay.PolicyLaws S P :=
  repaired_to_existing L.toEventDistinctPolicy L.self_commutation

def PolicyLaws.ofExisting (L : CertifiedReplay.PolicyLaws S P) : PolicyLaws S P :=
  ⟨existing_to_distinct L, existing_self_commutation L⟩

theorem policy_iff_existing : PolicyLaws S P ↔ CertifiedReplay.PolicyLaws S P :=
  ⟨PolicyLaws.toExisting, PolicyLaws.ofExisting⟩

/-- Retain the independent represented-prefix update and exchange certificate. -/
structure RestrictedLaws (S : CertifiedReplay.Scope D)
    (P : OperationPolicy D.AppOp) : Prop where
  replay : CertifiedReplay.Laws S P
  policy : PolicyLaws S P

def RestrictedLaws.toExisting (L : RestrictedLaws S P) : CertifiedReplay.RestrictedLaws S P :=
  ⟨L.replay, L.policy.toExisting⟩

def RestrictedLaws.ofExisting (L : CertifiedReplay.RestrictedLaws S P) : RestrictedLaws S P :=
  ⟨L.replay, PolicyLaws.ofExisting L.policy⟩

theorem restricted_iff_existing : RestrictedLaws S P ↔ CertifiedReplay.RestrictedLaws S P :=
  ⟨RestrictedLaws.toExisting, RestrictedLaws.ofExisting⟩
end Certified

namespace Invariant
variable {Inv : D.State → Prop}
variable {S : InvariantReplay.Scope D}

/-- Equal-payload commutation on every invariant state. This domain is
independent of represented-prefix readiness and is retained unchanged. -/
def SelfCommutes (S : InvariantReplay.Scope D) (Inv : D.State → Prop) : Prop :=
  ∀ a b, a ∈ S.events → b ∈ S.events → distinctOps a b → a.rep ≠ b.rep →
    ¬ S.context.vis a b → ¬ S.context.vis b a → a.op = b.op →
    InvariantOrder.Commutes D Inv a b

theorem existing_self_commutation (L : InvariantReplay.PolicyLaws S Inv P) :
    SelfCommutes S Inv := by
  classical
  intro a b ha hb distinct replica notab notba same
  by_contra bad
  have edge := (L.concurrent_exact a b ha hb distinct replica notab notba).mp bad
  have no := L.no_chain a b a ha hb ha distinct (by
    simpa [distinctOps, Op.time, ne_comm] using distinct)
  have diagonal : P.before b.op b.op := by simpa [same] using edge
  exact no (by simpa [same] using And.intro diagonal diagonal)

/-- The revised exactness domain keeps metadata guards. Removing them is
a stronger premise unless event support is proved explicitly. -/
structure EventDistinctPolicy (S : InvariantReplay.Scope D) (Inv : D.State → Prop) (P : OperationPolicy D.AppOp) : Prop where
  concurrent_exact : ∀ a b, a ∈ S.events → b ∈ S.events →
    distinctOps a b → a.rep ≠ b.rep → a.op ≠ b.op →
    ¬ S.context.vis a b → ¬ S.context.vis b a →
    (¬ InvariantOrder.Commutes D Inv a b ↔ P.before a.op b.op ∨ P.before b.op a.op)
  no_chain : ∀ a b c, a ∈ S.events → b ∈ S.events → c ∈ S.events →
    distinctOps a b → distinctOps b c → ¬ (P.before a.op b.op ∧ P.before b.op c.op)

def existing_to_distinct (L : InvariantReplay.PolicyLaws S Inv P) : EventDistinctPolicy S Inv P where
  concurrent_exact a b ha hb distinct replica _ := L.concurrent_exact a b ha hb distinct replica
  no_chain := L.no_chain

def repaired_to_existing (L : EventDistinctPolicy S Inv P) (self : SelfCommutes S Inv) :
    InvariantReplay.PolicyLaws S Inv P where
  concurrent_exact a b ha hb distinct replica notab notba := by
    by_cases same : a.op = b.op
    · have no := L.no_chain a b a ha hb ha distinct (by
        simpa [distinctOps, Op.time, ne_comm] using distinct)
      have diagonal : ¬ P.before b.op b.op := fun h => no (by simpa [same] using And.intro h h)
      simp [self a b ha hb distinct replica notab notba same, same, diagonal]
    · exact L.concurrent_exact a b ha hb distinct replica same notab notba
  no_chain := L.no_chain

theorem existing_iff_repaired : InvariantReplay.PolicyLaws S Inv P ↔
    EventDistinctPolicy S Inv P ∧ SelfCommutes S Inv :=
  ⟨fun L => ⟨existing_to_distinct L, existing_self_commutation L⟩,
    fun ⟨L,self⟩ => repaired_to_existing L self⟩

/-- Split policy with exactly the prior scope and state domain. -/
structure PolicyLaws (S : InvariantReplay.Scope D) (Inv : D.State → Prop)
    (P : OperationPolicy D.AppOp) : Prop extends EventDistinctPolicy S Inv P where
  self_commutation : SelfCommutes S Inv

def PolicyLaws.toExisting (L : PolicyLaws S Inv P) : InvariantReplay.PolicyLaws S Inv P :=
  repaired_to_existing L.toEventDistinctPolicy L.self_commutation

def PolicyLaws.ofExisting (L : InvariantReplay.PolicyLaws S Inv P) : PolicyLaws S Inv P :=
  ⟨existing_to_distinct L, existing_self_commutation L⟩

theorem policy_iff_existing : PolicyLaws S Inv P ↔ InvariantReplay.PolicyLaws S Inv P :=
  ⟨PolicyLaws.toExisting, PolicyLaws.ofExisting⟩

/-- Retain the independent represented-prefix update and exchange certificate. -/
structure RestrictedLaws (S : InvariantReplay.Scope D) (Inv : D.State → Prop)
    (P : OperationPolicy D.AppOp) : Prop where
  replay : InvariantReplay.Laws S Inv P
  policy : PolicyLaws S Inv P

def RestrictedLaws.toExisting (L : RestrictedLaws S Inv P) : InvariantReplay.RestrictedLaws S Inv P :=
  ⟨L.replay, L.policy.toExisting⟩

def RestrictedLaws.ofExisting (L : InvariantReplay.RestrictedLaws S Inv P) : RestrictedLaws S Inv P :=
  ⟨L.replay, PolicyLaws.ofExisting L.policy⟩

theorem restricted_iff_existing : RestrictedLaws S Inv P ↔ InvariantReplay.RestrictedLaws S Inv P :=
  ⟨RestrictedLaws.toExisting, RestrictedLaws.ofExisting⟩
end Invariant

end Sal.MRDTs.Paper1.SplitPolicy
