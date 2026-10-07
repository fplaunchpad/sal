import Sal.MRDTs.Paper1.CertifiedRGAExecution
import Sal.MRDTs.Paper1.CertifiedScopeRestriction
import Sal.MRDTs.Paper1.CertifiedPolicy

namespace Sal.MRDTs.Paper1.CertifiedRGACertificate
open Foundation Sal.EmbedRGA
namespace Embedded
open Instances.EmbedRGA
variable {α : Type} [DecidableEq α] [Inhabited α]

abbrev policy : OperationPolicy (EOp α) := commutingPolicy (EOp α)
def scope (Γ : OrderedPrefixCode) (C : Configuration (E Γ α)) (H : Set (Op (EOp α))) :=
  CertifiedReplay.restrict (CertifiedRGAScope.Embedded.scope Γ C.replayContext) H

theorem laws (Γ : OrderedPrefixCode) {C : Configuration (E Γ α)}
    (execution : CertifiedExecution (E Γ α) (generation Γ) C)
    {v : Version} {s : EState α} {H : Set (Op (EOp α))}
    (hv : C.ver v = some (s,H)) : CertifiedReplay.RestrictedLaws (scope Γ C H) policy := by
  have good := CertifiedRGAExecution.Embedded.canonicalConfig Γ execution
  apply CertifiedReplay.restrictedEmpty
  exact CertifiedReplay.restrict_laws (CertifiedRGAIssuance.Embedded.laws Γ C
    execution.mintHonest policy) H
    (fun e he => good.version_events_supported v s H hv e he)
    (fun a _ b hb vis => good.version_events_causal v s H hv a b vis hb)

theorem storedCanonical (Γ : OrderedPrefixCode) {C : Configuration (E Γ α)}
    (execution : CertifiedExecution (E Γ α) (generation Γ) C)
    {v : Version} {s : EState α} {H : Set (Op (EOp α))}
    (hv : C.ver v = some (s,H)) :
    CertifiedReplay.Canonical (scope Γ C H) policy (E Γ α).init s := by
  have rep := CertifiedRGAExecution.Embedded.representedVersions Γ execution hv
  obtain ⟨xs,perm,ordered,fold⟩ := rep.2.2.2.2
  refine ⟨xs,perm,CertifiedReplay.legal_of_causal_enumeration rep.2.2.1 perm ordered,ordered,?_,fold⟩
  apply ordered.imp
  intro a b noVis edge
  rcases edge with causal | concurrent
  · exact noVis causal.1
  · exact concurrent.2.2.1.elim

end Embedded
namespace Sided
open Instances.SidedEmbedRGA

abbrev policy : OperationPolicy (SOp) := commutingPolicy (SOp)
def scope (Γ : OrderedPrefixCode) (C : Configuration (S Γ)) (H : Set (Op (SOp))) :=
  CertifiedReplay.restrict (CertifiedRGAScope.Sided.scope Γ C.replayContext) H

theorem laws (Γ : OrderedPrefixCode) {C : Configuration (S Γ)}
    (execution : CertifiedExecution (S Γ) (generation Γ) C)
    {v : Version} {s : SState} {H : Set (Op (SOp))}
    (hv : C.ver v = some (s,H)) : CertifiedReplay.RestrictedLaws (scope Γ C H) policy := by
  have good := CertifiedRGAExecution.Sided.canonicalConfig Γ execution
  apply CertifiedReplay.restrictedEmpty
  exact CertifiedReplay.restrict_laws (CertifiedRGAIssuance.Sided.laws Γ C
    execution.mintHonest policy) H
    (fun e he => good.version_events_supported v s H hv e he)
    (fun a _ b hb vis => good.version_events_causal v s H hv a b vis hb)

theorem storedCanonical (Γ : OrderedPrefixCode) {C : Configuration (S Γ)}
    (execution : CertifiedExecution (S Γ) (generation Γ) C)
    {v : Version} {s : SState} {H : Set (Op (SOp))}
    (hv : C.ver v = some (s,H)) :
    CertifiedReplay.Canonical (scope Γ C H) policy (S Γ).init s := by
  have rep := CertifiedRGAExecution.Sided.representedVersions Γ execution hv
  obtain ⟨xs,perm,ordered,fold⟩ := rep.2.2.2.2
  refine ⟨xs,perm,CertifiedReplay.legal_of_causal_enumeration rep.2.2.1 perm ordered,ordered,?_,fold⟩
  apply ordered.imp
  intro a b noVis edge
  rcases edge with causal | concurrent
  · exact noVis causal.1
  · exact concurrent.2.2.1.elim

end Sided
end Sal.MRDTs.Paper1.CertifiedRGACertificate
