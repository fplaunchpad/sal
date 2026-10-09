import Sal.MRDTs.Paper1.Automation.CommonVerification
import Sal.MRDTs.Paper1.Automation.AutomatedRGA
import Sal.MRDTs.Paper1.Automation.GenericMonotoneProduct
import Sal.MRDTs.Paper1.Automation.GenericQueryLift
import Sal.MRDTs.Paper1.CertifiedRGACoreVC

/-! Direct declarations for the unchanged Core/RichCore certified ports.
All product history reasoning is supplied by GenericMonotoneProduct; text
collection/ordering facts come from the new finite ordered-record Kit. -/
namespace Sal.MRDTs.Paper1.Automation.AutomatedCore
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT Sal.EmbedRGA Classical
open Sal.MRDTs.Instances.SidedPeritext Sal.MRDTs.Instances.SidedEmbedRGA
noncomputable section

theorem evidence (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (H : Set (Op (Core Γ).AppOp)) (s : (Core Γ).State)
    (rep : CertifiedRGACoreVC.representation Γ C H s) :
    MonotoneProduct.Evidence (AutomatedRGA.Sided.kit Γ) C H s := by
  derive_product_evidence rep with (AutomatedRGA.Sided.issuer Γ)

def input (Γ : OrderedPrefixCode) : CommonVerification.Input (Core Γ)
    (CertifiedRGACoreVC.policy Γ) (CertifiedRGACoreVC.representation Γ)
    (CertifiedRGACoreVC.scheme Γ) :=
  .product (AutomatedRGA.Sided.kit Γ) (evidence Γ)

register_mrdt_input input

theorem automated_vcs (Γ : OrderedPrefixCode) : Raw.MergeVCs
    (CertifiedRGACoreVC.policy Γ) (CertifiedRGACoreVC.representation Γ)
    (CertifiedRGACoreVC.scheme Γ) :=
  by mrdt_verify

#print axioms automated_vcs
end
end Sal.MRDTs.Paper1.Automation.AutomatedCore
