import CommonVerification
import AutomatedRGA
import GenericMonotoneProduct
import GenericQueryLift
import Sal.MRDTs.Paper1.CertifiedRGACoreVC
import Sal.MRDTs.Paper1.CertifiedRGARichVC

/-! Direct declarations for the unchanged Core/RichCore certified ports.
All product history reasoning is supplied by GenericMonotoneProduct; text
collection/ordering facts come from the new finite ordered-record Kit. -/
namespace NeemExpansion.AutomatedCore
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT Sal.EmbedRGA Classical
open Sal.MRDTs.Instances.SidedPeritext Sal.MRDTs.Instances.SidedEmbedRGA
noncomputable section

theorem evidence (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (H : Set (Op (Core Γ).AppOp)) (s : (Core Γ).State)
    (rep : CertifiedRGACoreVC.representation Γ C H s) :
    MonotoneProduct.Evidence (AutomatedRGA.Sided.kit Γ) C H s := by
  refine ⟨AutomatedRGA.Sided.issuer Γ _ rep.1,?_,?_⟩
  · intro e he n target
    apply rep.2.1 (inlOp e) (mem_projReplayContext₁_events.mp he) n
    exact congrArg Sum.inl target
  · exact ⟨rep.2.2.2.2.1,rep.2.2.2.2.2⟩

def input (Γ : OrderedPrefixCode) : CommonVerification.Input (Core Γ)
    (CertifiedRGACoreVC.policy Γ) (CertifiedRGACoreVC.representation Γ)
    (CertifiedRGACoreVC.scheme Γ) :=
  .product (AutomatedRGA.Sided.kit Γ) (evidence Γ)

register_mrdt_input input

theorem automated_vcs (Γ : OrderedPrefixCode) : Raw.MergeVCs
    (CertifiedRGACoreVC.policy Γ) (CertifiedRGACoreVC.representation Γ)
    (CertifiedRGACoreVC.scheme Γ) :=
  by mrdt_verify

def rich_input (Γ : OrderedPrefixCode) : CommonVerification.Input (RichCore Γ)
    (CertifiedRGARichVC.policy Γ) (CertifiedRGARichVC.representation Γ)
    (CertifiedRGARichVC.scheme Γ) :=
  .queryLift Sal.MRDTs.Instances.PeritextRender.MType (List (Nat×Bool)) renderState (input Γ)

register_mrdt_input rich_input

theorem rich_automated_vcs (Γ : OrderedPrefixCode) : Raw.MergeVCs
    (CertifiedRGARichVC.policy Γ) (CertifiedRGARichVC.representation Γ)
    (CertifiedRGARichVC.scheme Γ) := by mrdt_verify

#print axioms automated_vcs
#print axioms rich_automated_vcs
end
end NeemExpansion.AutomatedCore
