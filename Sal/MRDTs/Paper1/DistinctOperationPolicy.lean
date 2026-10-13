import Sal.MRDTs.Paper1.CertifiedPolicy
import Sal.MRDTs.Paper1.InvariantReplay

/-! Payload-distinct policy exactness at fixed eligible concurrent events.
The replay diamond is retained independently, including for equal payloads.
Neither concrete commutation nor the causal and absorber order is changed.
These are scoped sufficient contracts, not a replacement for the raw guarded
convergence theorem or a derivation of diamonds from the five merge VCs. -/
namespace Sal.MRDTs.Paper1.DistinctOperationPolicy
open Foundation

/-- Supported concurrent events with different payloads satisfy the former
metadata guards. This implication uses the replay context's issuance facts. -/
theorem metadata_guards {D : UpdateSig} (C : ReplayContext D)
    {a b : Op D.AppOp} (ha : a ∈ C.events) (hb : b ∈ C.events)
    (payload : a.op ≠ b.op) (notab : ¬ C.vis a b) (notba : ¬ C.vis b a) :
    distinctOps a b ∧ a.rep ≠ b.rep := by
  have ne : a ≠ b := fun eq => payload (congrArg Op.op eq)
  obtain ⟨ra,sa,hla,hsa⟩ := ha
  obtain ⟨rb,sb,hlb,hsb⟩ := hb
  refine ⟨C.timestamps_distinct hla hsa hlb hsb ne, ?_⟩
  intro same
  exact (C.vis_total_same_replica hla hsa hlb hsb ne same).elim notab notba

namespace Certified
variable {D : UpdateSig}

structure PolicyLaws (S : CertifiedReplay.Scope D) (P : OperationPolicy D.AppOp) : Prop where
  concurrent_exact : ∀ a b, a ∈ S.events → b ∈ S.events → a.op ≠ b.op →
    ¬ S.context.vis a b → ¬ S.context.vis b a →
    (¬ CertifiedReplay.Commutes S a b ↔ P.before a.op b.op ∨ P.before b.op a.op)
  no_chain : ∀ a b c, a ∈ S.events → b ∈ S.events → c ∈ S.events →
    distinctOps a b → distinctOps b c → ¬ (P.before a.op b.op ∧ P.before b.op c.op)

structure RestrictedLaws (S : CertifiedReplay.Scope D) (P : OperationPolicy D.AppOp) : Prop where
  replay : CertifiedReplay.Laws S P
  policy : PolicyLaws S P

/-- Existing certificates adapt without changing their implementations,
sequential languages, issuance predicates, or replay diamonds. -/
def ofExisting {S : CertifiedReplay.Scope D} {P : OperationPolicy D.AppOp}
    (supported : S.events ⊆ S.context.events)
    (laws : CertifiedReplay.RestrictedLaws S P) : RestrictedLaws S P where
  replay := laws.replay
  policy := {
    concurrent_exact := fun a b ha hb payload notab notba => by
      obtain ⟨distinct,replica⟩ := metadata_guards S.context (supported ha) (supported hb) payload notab notba
      exact laws.policy.concurrent_exact a b ha hb distinct replica notab notba
    no_chain := laws.policy.no_chain }

/-- Equal-payload exchanges are justified by the retained concrete diamond,
never by the payload-distinct policy equation. -/
theorem canonical_unique {S : CertifiedReplay.Scope D} {P : OperationPolicy D.AppOp}
    (laws : RestrictedLaws S P) {initial a b : D.State}
    (represented : S.represented ∅ initial)
    (ha : CertifiedReplay.Canonical S P initial a)
    (hb : CertifiedReplay.Canonical S P initial b) : a = b :=
  CertifiedReplay.canonical_unique laws.replay represented ha hb
end Certified

namespace Invariant
variable {D : UpdateSig} {Inv : D.State → Prop}

structure PolicyLaws (S : InvariantReplay.Scope D) (Inv : D.State → Prop)
    (P : OperationPolicy D.AppOp) : Prop where
  concurrent_exact : ∀ a b, a ∈ S.events → b ∈ S.events → a.op ≠ b.op →
    ¬ S.context.vis a b → ¬ S.context.vis b a →
    (¬ InvariantOrder.Commutes D Inv a b ↔ P.before a.op b.op ∨ P.before b.op a.op)
  no_chain : ∀ a b c, a ∈ S.events → b ∈ S.events → c ∈ S.events →
    distinctOps a b → distinctOps b c → ¬ (P.before a.op b.op ∧ P.before b.op c.op)

structure RestrictedLaws (S : InvariantReplay.Scope D) (Inv : D.State → Prop)
    (P : OperationPolicy D.AppOp) : Prop where
  replay : InvariantReplay.Laws S Inv P
  policy : PolicyLaws S Inv P

def ofExisting {S : InvariantReplay.Scope D} {P : OperationPolicy D.AppOp}
    (supported : S.events ⊆ S.context.events)
    (laws : InvariantReplay.RestrictedLaws S Inv P) : RestrictedLaws S Inv P where
  replay := laws.replay
  policy := {
    concurrent_exact := fun a b ha hb payload notab notba => by
      obtain ⟨distinct,replica⟩ := metadata_guards S.context (supported ha) (supported hb) payload notab notba
      exact laws.policy.concurrent_exact a b ha hb distinct replica notab notba
    no_chain := laws.policy.no_chain }

theorem canonical_unique {S : InvariantReplay.Scope D} {P : OperationPolicy D.AppOp}
    (laws : RestrictedLaws S Inv P) {initial a b : D.State}
    (represented : S.represented ∅ initial)
    (ha : InvariantReplay.Canonical S Inv P initial a)
    (hb : InvariantReplay.Canonical S Inv P initial b) : a = b :=
  InvariantReplay.canonical_unique laws.replay represented ha hb
end Invariant

end Sal.MRDTs.Paper1.DistinctOperationPolicy
