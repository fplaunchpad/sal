import Sal.MRDTs.Paper1.Automation.AutomatedCore
import Sal.MRDTs.Paper1.CertifiedRGACoreAlgebra

namespace Sal.MRDTs.Paper1.CertifiedRGACoreMergeVC
open Foundation Classical Sal.EmbedRGA Instances.SidedPeritext Instances.SidedEmbedRGA
open CertifiedRGACoreVC CertifiedRGACoreAlgebra

theorem sorted (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (H : Set (Op (Core Γ).AppOp)) (s : (Core Γ).State) (rep : representation Γ C H s) : SSorted s.1 :=
  CertifiedRGAVCAlgebra.Sided.sorted Γ _ _ _ (represented_text Γ C H s rep)

theorem merge_sorted (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (A B : Set (Op (Core Γ).AppOp)) (l a b : (Core Γ).State)
    (ha : representation Γ C A a) (hb : representation Γ C B b) :
    SSorted ((Core Γ).merge l a b).1 :=
  CertifiedRGAVCAlgebra.Sided.merge_sorted Γ _ _ _ _ _ _
    (represented_text Γ C A a ha) (represented_text Γ C B b hb)

theorem mergeVCs (Γ : OrderedPrefixCode) : ConcreteMRDT.Raw.MergeVCs
    (policy Γ) (representation Γ) (scheme Γ) := by
  exact Sal.MRDTs.Paper1.Automation.AutomatedCore.automated_vcs Γ

theorem representationJoin (Γ : OrderedPrefixCode) : ConcreteMRDT.RepresentationJoin (representation Γ) := by
  apply ConcreteMRDT.Raw.representationJoin_of_vcs (mergeVCs Γ) (unique Γ) (initial Γ) (finite Γ)
  intro C E₁ E₂ a b trans irr _ _ ha _
  exact replaySupply Γ C ha.1 ha.2.1 trans irr

#print axioms mergeVCs
#print axioms representationJoin
end Sal.MRDTs.Paper1.CertifiedRGACoreMergeVC
