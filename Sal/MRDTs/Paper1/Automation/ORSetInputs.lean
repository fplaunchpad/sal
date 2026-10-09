import Sal.MRDTs.Paper1.Automation.CommonVerification
import Sal.MRDTs.Paper1.Automation.AutomatedORSet
import Sal.MRDTs.Paper1.Automation.AutomatedEfficientORSet
namespace Sal.MRDTs.Paper1.Automation.CommonInstances
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 ConcreteMRDT
open Sal.MRDTs.Paper1.Automation.CommonVerification
namespace OrdinaryORSet
open ORSet
variable {α : Type} [DecidableEq α]
def input : Input (D α) (conflict α) (RawReplay.representation (α := α)) (RawReplay.scheme (α := α)) :=
  .policy AutomatedORSet.kit (.witness AutomatedORSet.noncomm_full (fun _ _ _ rep => rep.1))
register_mrdt_input input
end OrdinaryORSet
namespace EfficientORSet
open Instances.EfficientORSet
variable {α : Type} [DecidableEq α]
def input : Input (D α) (Sal.MRDTs.Paper1.EfficientORSet.EventSpec.conflict α)
    (Sal.MRDTs.Paper1.EfficientORSet.RawReplay.representation (α := α))
    (Sal.MRDTs.Paper1.EfficientORSet.RawReplay.scheme (α := α)) :=
  .policy AutomatedEfficientORSet.kit
    (.mask AutomatedEfficientORSet.maskKit AutomatedEfficientORSet.semantic_shape)
register_mrdt_input input
end EfficientORSet
end Sal.MRDTs.Paper1.Automation.CommonInstances
