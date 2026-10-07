import Sal.MRDTs.Paper1.CertifiedRGAProducts
import Sal.MRDTs.Paper1.CertifiedRGAFugue
import Sal.MRDTs.Instances.Peritext

/-! Original issuance evidence supplies concrete scoped replay laws for all
six embedded production signatures, including ordinary and virtual certified
configurations. These adapters do not invoke a merge correctness theorem. -/
namespace Sal.MRDTs.Paper1.CertifiedRGAIssuance
open Foundation Sal.EmbedRGA

namespace Embedded
open Instances.EmbedRGA
variable {α : Type} [DecidableEq α] [Inhabited α]
theorem laws (Γ : OrderedPrefixCode) (C : Configuration (E Γ α))
    (mint : MintHonest (E Γ α) eApplicable C) (P : OperationPolicy (EOp α)) :
    CertifiedReplay.Laws (CertifiedRGAScope.Embedded.scope Γ C.replayContext) P :=
  CertifiedRGAScope.Embedded.laws Γ C.replayContext (eHonest_core (eHonest_of_mint mint))
    (fun _ _ vis => C.vis_src vis) P
end Embedded

namespace Sided
open Instances.SidedEmbedRGA
theorem laws (Γ : OrderedPrefixCode) (C : Configuration (S Γ))
    (mint : MintHonest (S Γ) sApplicable C) (P : OperationPolicy SOp) :
    CertifiedReplay.Laws (CertifiedRGAScope.Sided.scope Γ C.replayContext) P :=
  CertifiedRGAScope.Sided.laws Γ C.replayContext (sHonest_core (sHonest_of_mint mint))
    (fun _ _ vis => C.vis_src vis) P
end Sided

namespace Peritext
open Instances.Peritext Instances.EmbedRGA
theorem laws (Γ : OrderedPrefixCode) (C : Configuration (D Γ))
    (mint : MintHonest (D Γ) eApplicable C) (P : OperationPolicy (EOp Element)) :
    CertifiedReplay.Laws (CertifiedRGAScope.Embedded.scope Γ C.replayContext) P :=
  Embedded.laws Γ C mint P
end Peritext

namespace SidedPeritext
open Instances.SidedPeritext Instances.SidedEmbedRGA

theorem laws (Γ : OrderedPrefixCode) (C : Configuration (Core Γ))
    (mint : MintHonest (Core Γ) (coreGuard Γ) C) (P : OperationPolicy (Core Γ).AppOp) :
    CertifiedReplay.Laws (CertifiedPrefixScope.scope (Core Γ) C.replayContext) P := by
  apply CertifiedRGAProducts.SidedPeritext.laws Γ C.replayContext _ (fun _ _ vis => C.vis_src vis) P
  simpa only [projConf₁_core] using sHonest_core (coreHonest_of_mint C mint)

theorem rich_laws (Γ : OrderedPrefixCode) (C : Configuration (RichCore Γ))
    (mint : MintHonest (RichCore Γ) (coreGuard Γ) C) (P : OperationPolicy (RichCore Γ).AppOp) :
    CertifiedReplay.Laws (CertifiedPrefixScope.scope (RichCore Γ) C.replayContext) P := by
  apply CertifiedRGAProducts.SidedPeritext.rich_laws Γ C.replayContext _ (fun _ _ vis => C.vis_src vis) P
  have hc := coreHonest_of_mint (asCoreConfig C) (mintHonest_to_core mint)
  have hh := sHonest_core hc
  simpa only [projConf₁_core,asCoreConfig] using hh
end SidedPeritext

namespace FugueMax
open Instances.SidedEmbedRGA.FugueMax
theorem laws (Γ : OrderedPrefixCode) (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    (P : OperationPolicy Payload) :
    CertifiedReplay.Laws (CertifiedPrefixScope.scope (datatype Γ) C.replayContext) P :=
  CertifiedRGAFugue.laws Γ C mint trans P
end FugueMax

#print axioms Embedded.laws
#print axioms Sided.laws
#print axioms Peritext.laws
#print axioms SidedPeritext.laws
#print axioms SidedPeritext.rich_laws
#print axioms FugueMax.laws
end Sal.MRDTs.Paper1.CertifiedRGAIssuance
