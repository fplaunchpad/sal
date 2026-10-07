import Sal.MRDTs.Paper1.CertifiedRGAVC
import Sal.MRDTs.Instances.Peritext

/-! Peritext's payload-specific signature has the same raw state and operations
as embedded RGA. Its query boundary does not affect the equality VCs. -/
namespace Sal.MRDTs.Paper1.CertifiedPeritextVC
open Foundation Sal.EmbedRGA Instances.Peritext

abbrev representation (Γ : OrderedPrefixCode) :=
  CertifiedRGAVCReplay.Embedded.representation (α := Element) Γ

theorem mergeVCs (Γ : OrderedPrefixCode) : AbstractMRDT.Raw.MergeVCs
    (CertifiedRGAVCReplay.Embedded.model (α := Element) Γ)
    CertifiedRGAVCReplay.Embedded.policy (representation Γ)
    (CertifiedRGAVCReplay.Embedded.scheme Γ) :=
  CertifiedRGAVC.Embedded.mergeVCs Γ

theorem representationJoin (Γ : OrderedPrefixCode) :
    AbstractMRDT.RepresentationJoin (representation Γ) :=
  CertifiedRGAVC.Embedded.representationJoin Γ

#print axioms representationJoin
end Sal.MRDTs.Paper1.CertifiedPeritextVC
