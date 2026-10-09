import Sal.MRDTs.Paper1.Automation.AutomatedRGA
import Sal.MRDTs.Paper1.CertifiedRGASidedVCAlgebra

set_option maxHeartbeats 2000000

namespace Sal.MRDTs.Paper1.CertifiedRGAVC
open Foundation Sal.EmbedRGA
namespace Sided
open Instances.SidedEmbedRGA CertifiedRGAVCReplay.Sided CertifiedRGAVCAlgebra.Sided

theorem mergeVCs (Γ : OrderedPrefixCode) : ConcreteMRDT.Raw.MergeVCs
    policy (representation Γ) (scheme Γ) := by
  exact Sal.MRDTs.Paper1.Automation.AutomatedRGA.Sided.automated_vcs Γ

theorem representationJoin (Γ : OrderedPrefixCode) : ConcreteMRDT.RepresentationJoin
    (representation Γ) := by
  apply ConcreteMRDT.Raw.representationJoin_of_vcs (mergeVCs Γ) (unique Γ)
    (initial Γ) (finite Γ)
  intro C E₁ E₂ a b trans irrefl _ _ ha _
  exact replaySupply Γ C ha.1 trans irrefl

#print axioms representationJoin
#print axioms mergeVCs
end Sided
end Sal.MRDTs.Paper1.CertifiedRGAVC
