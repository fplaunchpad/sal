import Sal.MRDTs.Paper1.Automation.AutomatedCore
import Sal.MRDTs.Paper1.CertifiedRGARichContract

namespace Sal.MRDTs.Paper1.Automation.AutomatedRichCore
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT Sal.EmbedRGA
open Sal.MRDTs.Instances.SidedPeritext
noncomputable section
def rich_input (Γ : OrderedPrefixCode) : CommonVerification.Input (RichCore Γ)
    (CertifiedRGARichVC.policy Γ) (CertifiedRGARichVC.representation Γ)
    (CertifiedRGARichVC.scheme Γ) :=
  .queryLift Sal.MRDTs.Instances.PeritextRender.MType (List (Nat×Bool)) renderState (Sal.MRDTs.Paper1.Automation.AutomatedCore.input Γ)

register_mrdt_input rich_input

theorem rich_automated_vcs (Γ : OrderedPrefixCode) : Raw.MergeVCs
    (CertifiedRGARichVC.policy Γ) (CertifiedRGARichVC.representation Γ)
    (CertifiedRGARichVC.scheme Γ) := by mrdt_verify

end
end Sal.MRDTs.Paper1.Automation.AutomatedRichCore
