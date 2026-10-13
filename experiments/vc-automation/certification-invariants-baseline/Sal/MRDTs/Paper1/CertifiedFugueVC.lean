import Sal.MRDTs.Paper1.Automation.AutomatedFugue
import Sal.MRDTs.Paper1.CertifiedFugueVCAlgebra

set_option maxHeartbeats 2000000

namespace Sal.MRDTs.Paper1.CertifiedFugueVC
open Foundation Sal.EmbedRGA
open Instances.SidedEmbedRGA Instances.SidedEmbedRGA.FugueMax
open CertifiedFugueVCReplay CertifiedFugueVCAlgebra
attribute [local instance] Instances.SidedEmbedRGA.FugueMax.rc

private theorem state_ext {s t : State} (live : s.live = t.live) (births : s.births = t.births) : s = t := by
  cases s; cases t; cases live; cases births; rfl

theorem mergeVCs (Γ : OrderedPrefixCode) : ConcreteMRDT.Raw.MergeVCs
    policy (representation Γ) (scheme Γ) := by
  exact Sal.MRDTs.Paper1.Automation.AutomatedFugue.automated_vcs Γ

theorem representationJoin (Γ : OrderedPrefixCode) : ConcreteMRDT.RepresentationJoin
    (representation Γ) := by
  apply ConcreteMRDT.Raw.representationJoin_of_vcs (mergeVCs Γ) (unique Γ)
    (initial Γ) (finite Γ)
  intro C E₁ E₂ a b trans irrefl _ _ ha _
  exact replaySupply Γ C ha.1 trans irrefl

#print axioms representationJoin
#print axioms mergeVCs
end Sal.MRDTs.Paper1.CertifiedFugueVC
