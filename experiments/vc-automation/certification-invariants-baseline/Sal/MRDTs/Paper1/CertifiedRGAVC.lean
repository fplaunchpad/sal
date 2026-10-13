import Sal.MRDTs.Paper1.Automation.AutomatedRGA
import Sal.MRDTs.Paper1.CertifiedRGAVCAlgebra

set_option maxHeartbeats 2000000

namespace Sal.MRDTs.Paper1.CertifiedRGAVC
open Foundation Sal.EmbedRGA
namespace Embedded
open Instances.EmbedRGA CertifiedRGAVCReplay.Embedded CertifiedRGAVCAlgebra.Embedded
variable {α : Type} [DecidableEq α] [Inhabited α]

theorem mergeVCs (Γ : OrderedPrefixCode) : ConcreteMRDT.Raw.MergeVCs
    policy (representation (α := α) Γ) (scheme Γ) := by
  exact Sal.MRDTs.Paper1.Automation.AutomatedRGA.Embedded.automated_vcs Γ

theorem representationJoin (Γ : OrderedPrefixCode) : ConcreteMRDT.RepresentationJoin
    (representation (α := α) Γ) := by
  apply ConcreteMRDT.Raw.representationJoin_of_vcs (mergeVCs Γ) (unique Γ)
    (initial Γ) (finite Γ)
  intro C E₁ E₂ a b trans irrefl _ _ ha _
  exact replaySupply Γ C ha.1 trans irrefl

#print axioms representationJoin
#print axioms mergeVCs
end Embedded
end Sal.MRDTs.Paper1.CertifiedRGAVC
