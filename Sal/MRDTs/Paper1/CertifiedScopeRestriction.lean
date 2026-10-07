import Sal.MRDTs.Paper1.CertifiedReplay

/-! A stored version contains a causally closed subset of the configuration's
eligible events. Restricting replay scope to that history preserves the local
update and exchange laws. The semantic order still uses the version's own
absorber set; no equality of differently indexed orders is assumed. -/
namespace Sal.MRDTs.Paper1.CertifiedReplay
open Foundation
variable {D : UpdateSig}

def restrict (S : Scope D) (E : Set (Op D.AppOp)) : Scope D where
  context := S.context
  events := E
  represented H s := H ⊆ E ∧ S.represented H s

theorem paperOrder_restrict (P : OperationPolicy D.AppOp)
    (C : ReplayContext D) {E F : Set (Op D.AppOp)} (sub : E ⊆ F)
    {a b : Op D.AppOp} (order : paperOrder P C F a b) : paperOrder P C E a b := by
  rcases order with causal | ⟨ab,ba,policy,noAbsorber⟩
  · exact Or.inl causal
  · exact Or.inr ⟨ab,ba,policy,fun ⟨c,member,vis,nc⟩ =>
      noAbsorber ⟨c,sub member,vis,nc⟩⟩

theorem ready_of_restrict {S : Scope D} {E H : Set (Op D.AppOp)}
    (sub : E ⊆ S.events)
    (closed : ∀ a ∈ S.events, ∀ b ∈ E, S.context.vis a b → a ∈ E)
    {e : Op D.AppOp} (ready : Ready (restrict S E) H e) : Ready S H e :=
  ⟨sub ready.1,ready.2.1,fun p hp vis => ready.2.2 p (closed p hp e ready.1 vis) vis⟩

theorem restrict_laws {S : Scope D} {P : OperationPolicy D.AppOp}
    (laws : Laws S P) (E : Set (Op D.AppOp)) (sub : E ⊆ S.events)
    (closed : ∀ a ∈ S.events, ∀ b ∈ E, S.context.vis a b → a ∈ E) :
    Laws (restrict S E) P := by
  constructor
  · intro H s e represented ready
    exact ⟨Set.insert_subset ready.1 represented.1,
      laws.update_closed H s e represented.2 (ready_of_restrict sub closed ready)⟩
  · intro H s a b represented readyA readyB notab notba noab noba
    exact laws.diamond H s a b represented.2
      (ready_of_restrict sub closed readyA) (ready_of_restrict sub closed readyB)
      notab notba
      (fun edge => noab (paperOrder_restrict P S.context sub edge))
      (fun edge => noba (paperOrder_restrict P S.context sub edge))

end Sal.MRDTs.Paper1.CertifiedReplay
