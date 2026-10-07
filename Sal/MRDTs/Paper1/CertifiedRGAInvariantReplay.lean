import Sal.MRDTs.Paper1.InvariantReplay
import Sal.MRDTs.Paper1.CertifiedRGAInvariant
import Sal.MRDTs.Paper1.CertifiedRGAExecution
import Sal.MRDTs.Paper1.CertifiedRGAScope

namespace Sal.MRDTs.Paper1.CertifiedRGAInvariantReplay
open Foundation Sal.EmbedRGA Instances.EmbedRGA
variable {α : Type} [DecidableEq α] [Inhabited α]

def policy : OperationPolicy (EOp α) := commutingPolicy (EOp α)

noncomputable def scope (Γ : OrderedPrefixCode) (C : Configuration (E Γ α))
    (H : Set (Op (EOp α))) :=
  InvariantReplay.restrict (CertifiedRGAScope.Embedded.scope Γ C.replayContext) H

theorem represented_valid (Γ : OrderedPrefixCode)
    (C : ReplayContext (E Γ α).toUpdateSig) (honest : EHonestCore Γ C)
    (trans : Transitive C.vis) (irrefl : ∀ e, ¬ C.vis e e)
    (H : Set (Op (EOp α))) (s : EState α)
    (represented : CertifiedRGAScope.Embedded.represented Γ C H s) :
    CertifiedRGAInvariant.Valid Γ C s :=
  CertifiedRGAInvariant.represented_valid Γ C H s
    ⟨honest,trans,irrefl,represented.1,represented.2.2⟩

theorem concurrent_commutes (Γ : OrderedPrefixCode)
    (C : ReplayContext (E Γ α).toUpdateSig) (honest : EHonestCore Γ C)
    (a b : Op (EOp α)) (ha : a ∈ C.events) (hb : b ∈ C.events)
    (notab : ¬ C.vis a b) (notba : ¬ C.vis b a) :
    InvariantOrder.Commutes (E Γ α).toUpdateSig (CertifiedRGAInvariant.Valid Γ C) a b := by
  apply (CertifiedRGAInvariant.invariant_commutes_iff Γ C honest a b ha hb).mpr
  rcases a with ⟨ats,ar,ao⟩
  rcases b with ⟨bt,br,bo⟩
  cases ao <;> cases bo <;> simp only [Instances.ProductionRGA.embedSemanticCommutes]
  · intro same
    apply notab
    apply e_vis_of_rc_of_honest honest hb ha
    simpa [UpdateSig.rc,ReplayPolicy.Before,EReplayPolicy,eRcOrder] using same
  · intro same
    apply notba
    apply e_vis_of_rc_of_honest honest ha hb
    simpa [UpdateSig.rc,ReplayPolicy.Before,EReplayPolicy,eRcOrder] using same

theorem fullLaws (Γ : OrderedPrefixCode) (C : Configuration (E Γ α))
    (mint : MintHonest (E Γ α) (generation Γ).CanIssue C)
    (trans : Transitive C.vis) (irrefl : ∀ e, ¬ C.vis e e) :
    InvariantReplay.RestrictedLaws (CertifiedRGAScope.Embedded.scope Γ C.replayContext)
      (CertifiedRGAInvariant.Valid Γ C.replayContext) policy := by
  have honest := eHonest_core (eHonest_of_mint mint)
  have comm := concurrent_commutes Γ C.replayContext honest
  refine ⟨InvariantReplay.laws_of_concurrent_commutation _ _ _
    (represented_valid Γ C.replayContext honest trans irrefl)
    (CertifiedRGAScope.Embedded.update_closed Γ C.replayContext (fun _ _ vis => C.vis_src vis))
    comm,InvariantReplay.emptyPolicyLaws _ _ comm⟩

theorem laws (Γ : OrderedPrefixCode) {C : Configuration (E Γ α)}
    (execution : CertifiedExecution (E Γ α) (generation Γ) C)
    {v : Version} {s : EState α} {H : Set (Op (EOp α))} (hv : C.ver v = some (s,H)) :
    InvariantReplay.RestrictedLaws (scope Γ C H)
      (CertifiedRGAInvariant.Valid Γ C.replayContext) policy := by
  have good := CertifiedRGAExecution.Embedded.canonicalConfig Γ execution
  exact InvariantReplay.restrict_restrictedLaws
    (fullLaws Γ C execution.mintHonest (fun _ _ _ h k => good.vis_trans h k) good.vis_irrefl) H
    (fun e he => good.version_events_supported v s H hv e he)
    (fun a _ b hb vis => good.version_events_causal v s H hv a b vis hb)

theorem storedCanonical (Γ : OrderedPrefixCode) {C : Configuration (E Γ α)}
    (execution : CertifiedExecution (E Γ α) (generation Γ) C)
    {v : Version} {s : EState α} {H : Set (Op (EOp α))} (hv : C.ver v = some (s,H)) :
    InvariantReplay.Canonical (scope Γ C H)
      (CertifiedRGAInvariant.Valid Γ C.replayContext) policy (E Γ α).init s := by
  have rep := CertifiedRGAExecution.Embedded.representedVersions Γ execution hv
  obtain ⟨xs,perm,causal,fold⟩ := rep.2.2.2.2
  refine ⟨xs,perm,InvariantReplay.legal_of_causal_enumeration rep.2.2.1 perm causal,causal,?_,fold⟩
  apply causal.imp
  intro a b hn edge
  rcases edge with ⟨vis,_⟩ | ⟨_,_,bad,_⟩
  · exact hn vis
  · exact bad

theorem initial_represented (Γ : OrderedPrefixCode) (C : Configuration (E Γ α))
    (H : Set (Op (EOp α))) : (scope Γ C H).represented ∅ (E Γ α).init :=
  ⟨Set.empty_subset _,Set.empty_subset _,by simp,[],⟨List.nodup_nil,by simp⟩,List.Pairwise.nil,rfl⟩

theorem canonical_unique (Γ : OrderedPrefixCode) {C : Configuration (E Γ α)}
    (execution : CertifiedExecution (E Γ α) (generation Γ) C)
    {v : Version} {s : EState α} {H : Set (Op (EOp α))} (hv : C.ver v = some (s,H))
    {a b : EState α}
    (ha : InvariantReplay.Canonical (scope Γ C H) (CertifiedRGAInvariant.Valid Γ C.replayContext)
      policy (E Γ α).init a)
    (hb : InvariantReplay.Canonical (scope Γ C H) (CertifiedRGAInvariant.Valid Γ C.replayContext)
      policy (E Γ α).init b) : a = b :=
  InvariantReplay.canonical_unique (laws Γ execution hv).replay (initial_represented Γ C H) ha hb

/-- Every two complete causal replays of a stored history agree as raw states.
The revised order uses the configuration invariant throughout both replays. -/
theorem replay_equal (Γ : OrderedPrefixCode) {C : Configuration (E Γ α)}
    (execution : CertifiedExecution (E Γ α) (generation Γ) C)
    {v : Version} {s : EState α} {H : Set (Op (EOp α))} (hv : C.ver v = some (s,H))
    {π₁ π₂ : List (Op (EOp α))} (p₁ : listPermOf π₁ H) (p₂ : listPermOf π₂ H)
    (c₁ : respects π₁ C.vis) (c₂ : respects π₂ C.vis) :
    applySeq (E Γ α).toUpdateSig (E Γ α).init π₁ =
      applySeq (E Γ α).toUpdateSig (E Γ α).init π₂ := by
  have good := CertifiedRGAExecution.Embedded.canonicalConfig Γ execution
  apply InvariantReplay.convergence_on (laws Γ execution hv).replay
    (initial_represented Γ C H) p₁ p₂
    (InvariantReplay.legal_of_causal_enumeration good.vis_irrefl p₁ c₁)
    (InvariantReplay.legal_of_causal_enumeration good.vis_irrefl p₂ c₂) c₁ c₂
  · apply c₁.imp
    intro a b hn edge
    rcases edge with ⟨vis,_⟩ | ⟨_,_,bad,_⟩
    · exact hn vis
    · exact bad
  · apply c₂.imp
    intro a b hn edge
    rcases edge with ⟨vis,_⟩ | ⟨_,_,bad,_⟩
    · exact hn vis
    · exact bad

#print axioms laws
#print axioms storedCanonical
#print axioms concurrent_commutes
end Sal.MRDTs.Paper1.CertifiedRGAInvariantReplay
