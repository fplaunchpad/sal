import Sal.MRDTs.Paper1.CertifiedFugueInvariant
import Sal.MRDTs.Paper1.CertifiedRGAFugue
import Sal.MRDTs.Paper1.InvariantReplay

namespace Sal.MRDTs.Paper1.CertifiedFugueInvariantReplay
open Foundation Sal.EmbedRGA
open Instances.SidedEmbedRGA Instances.SidedEmbedRGA.FugueMax
attribute [local instance] Instances.SidedEmbedRGA.FugueMax.rc

def policy : OperationPolicy Payload := commutingPolicy Payload
noncomputable def scope (Γ : OrderedPrefixCode) (C : Configuration (datatype Γ))
    (H : Set (Op Payload)) :=
  InvariantReplay.restrict (CertifiedPrefixScope.scope (datatype Γ) C.replayContext) H

theorem concurrent_commutes (Γ : OrderedPrefixCode) (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    (a b : Op Payload) (ha : a ∈ C.events) (hb : b ∈ C.events)
    (notab : ¬ C.vis a b) (notba : ¬ C.vis b a) :
    InvariantOrder.Commutes (datatype Γ).toUpdateSig (CertifiedFugueInvariant.Valid Γ C.replayContext) a b := by
  apply (CertifiedFugueInvariant.invariant_commutes_iff Γ C mint trans a b ha hb).mpr
  rcases a with ⟨ats,ar,⟨ao,al,aro,ac⟩⟩
  rcases b with ⟨bts,br,⟨bo,bl,bro,bc⟩⟩
  cases ao <;> cases bo <;> simp only [CertifiedFugueInvariant.SemanticCommutes]
  · intro same
    apply notab
    exact rc_visible C mint trans ha hb ((rc_before Γ _ _).mpr ⟨rfl,by simpa only [same]⟩)
  · intro same
    apply notba
    exact rc_visible C mint trans hb ha ((rc_before Γ _ _).mpr ⟨rfl,by simpa only [same]⟩)

theorem fullLaws (Γ : OrderedPrefixCode) (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    (irrefl : ∀ e, ¬ C.vis e e) :
    InvariantReplay.RestrictedLaws (CertifiedPrefixScope.scope (datatype Γ) C.replayContext)
      (CertifiedFugueInvariant.Valid Γ C.replayContext) policy := by
  have comm := concurrent_commutes Γ C mint trans
  refine ⟨InvariantReplay.laws_of_concurrent_commutation _ _ _ ?_
    (CertifiedRGAFugue.laws Γ C mint trans policy).update_closed comm,
    InvariantReplay.emptyPolicyLaws _ _ comm⟩
  intro H s rep
  exact CertifiedFugueInvariant.represented_valid Γ C.replayContext H s
    ⟨⟨C,mint,rfl⟩,trans,irrefl,rep.1,rep.2.2⟩

theorem laws (Γ : OrderedPrefixCode) {C : Configuration (datatype Γ)}
    (execution : CertifiedExecution (datatype Γ) (FugueMax.generation Γ) C)
    {v : Version} {s : State} {H : Set (Op Payload)} (hv : C.ver v = some (s,H)) :
    InvariantReplay.RestrictedLaws (scope Γ C H)
      (CertifiedFugueInvariant.Valid Γ C.replayContext) policy := by
  have good := CertifiedFugueVCExecution.canonicalConfig Γ execution
  exact InvariantReplay.restrict_restrictedLaws
    (fullLaws Γ C execution.mintHonest (fun _ _ _ h k => good.vis_trans h k) good.vis_irrefl) H
    (fun e he => good.version_events_supported v s H hv e he)
    (fun a _ b hb vis => good.version_events_causal v s H hv a b vis hb)

theorem storedCanonical (Γ : OrderedPrefixCode) {C : Configuration (datatype Γ)}
    (execution : CertifiedExecution (datatype Γ) (FugueMax.generation Γ) C)
    {v : Version} {s : State} {H : Set (Op Payload)} (hv : C.ver v = some (s,H)) :
    InvariantReplay.Canonical (scope Γ C H) (CertifiedFugueInvariant.Valid Γ C.replayContext)
      policy (datatype Γ).init s := by
  have rep := CertifiedFugueVCExecution.representedVersions Γ execution hv
  obtain ⟨xs,perm,causal,fold⟩ := rep.2.2.2.2
  refine ⟨xs,perm,InvariantReplay.legal_of_causal_enumeration rep.2.2.1 perm causal,causal,?_,fold⟩
  apply causal.imp
  intro a b hn edge
  rcases edge with ⟨vis,_⟩ | ⟨_,_,bad,_⟩
  · exact hn vis
  · exact bad

theorem initial_represented (Γ : OrderedPrefixCode) (C : Configuration (datatype Γ))
    (H : Set (Op Payload)) : (scope Γ C H).represented ∅ (datatype Γ).init :=
  ⟨Set.empty_subset _,Set.empty_subset _,by simp,[],⟨List.nodup_nil,by simp⟩,List.Pairwise.nil,rfl⟩

theorem canonical_unique (Γ : OrderedPrefixCode) {C : Configuration (datatype Γ)}
    (execution : CertifiedExecution (datatype Γ) (FugueMax.generation Γ) C)
    {v : Version} {s : State} {H : Set (Op Payload)} (hv : C.ver v = some (s,H))
    {a b : State}
    (ha : InvariantReplay.Canonical (scope Γ C H) (CertifiedFugueInvariant.Valid Γ C.replayContext)
      policy (datatype Γ).init a)
    (hb : InvariantReplay.Canonical (scope Γ C H) (CertifiedFugueInvariant.Valid Γ C.replayContext)
      policy (datatype Γ).init b) : a = b :=
  InvariantReplay.canonical_unique (laws Γ execution hv).replay (initial_represented Γ C H) ha hb

#print axioms laws
#print axioms storedCanonical
end Sal.MRDTs.Paper1.CertifiedFugueInvariantReplay
