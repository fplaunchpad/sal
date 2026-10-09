import Sal.MRDTs.Paper1.CertifiedRGACoreVC

namespace Sal.MRDTs.Paper1.CertifiedRGARichVC
open Foundation Sal.EmbedRGA Instances.SidedPeritext
noncomputable section
abbrev representation (Γ : OrderedPrefixCode) : ConcreteMRDT.Representation (RichCore Γ) :=
  CertifiedRGACoreVC.representation Γ

def policy (Γ : OrderedPrefixCode) : OperationPolicy (RichCore Γ).AppOp := CertifiedRGACoreVC.policy Γ

def scheme (Γ : OrderedPrefixCode) (C : ReplayContext (RichCore Γ).toUpdateSig) :
    ConcreteMRDT.MetadataDependencies C where
  before := C.vis
  causal _ _ h := h
  covers _ _ h _ := h

end
end Sal.MRDTs.Paper1.CertifiedRGARichVC
