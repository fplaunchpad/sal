import Sal.MRDTs.Paper1.Automation.CommonVerification
import Sal.MRDTs.Paper1.Automation.AutomatedORSet
import Sal.MRDTs.Paper1.Automation.AutomatedEfficientORSet
import Sal.MRDTs.Paper1.Automation.InputDerivation
namespace Sal.MRDTs.Paper1.Automation.CommonInstances
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 ConcreteMRDT
open Sal.MRDTs.Paper1.Automation.CommonVerification
open Sal.MRDTs.Paper1.Automation.InputDerivation
set_option maxHeartbeats 4000000
namespace OrdinaryORSet
open ORSet
variable {α : Type} [DecidableEq α]
local instance policyData : PolicyData (D α) := ⟨ORSet.order⟩
attribute [local policy_expansion_simps] policyData LocalAssembly.ofMRDT D
  step merge ORSet.order conflict Op.op Op.rep Op.time
attribute [local mrdt_implementation] RawReplay.representation ConcreteRep.representation
def input : Input (D α) (conflict α) (RawReplay.representation (α := α)) (RawReplay.scheme (α := α)) :=
  by derive_mrdt_input
register_mrdt_input input
end OrdinaryORSet
namespace EfficientORSet
open Instances.EfficientORSet
variable {α : Type} [DecidableEq α]
local instance policyData : PolicyData (D α) := ⟨rc.order⟩
local instance maskData : MaskData (D α) (Sal.MRDTs.Paper1.EfficientORSet.EventSpec.conflict α) where
  Record := Record α
  recordDecidableEq := inferInstance
  description := AutomatedEfficientORSet.maskDescription
attribute [local policy_expansion_simps] policyData LocalAssembly.ofMRDT D
  update merge rc Sal.MRDTs.Paper1.EfficientORSet.EventSpec.conflict Op.op Op.rep Op.time
attribute [local policy_expansion_simps] maskData
  AutomatedEfficientORSet.maskDescription AutomatedEfficientORSet.birth kills
attribute [local mask_implementation] maskData
  AutomatedEfficientORSet.maskDescription AutomatedEfficientORSet.birth kills
attribute [local mask_implementation] D update
  Sal.MRDTs.Paper1.EfficientORSet.RawReplay.representation
  Sal.MRDTs.Paper1.EfficientORSet.ConcreteRep.representation Represents live dead
def input : Input (D α) (Sal.MRDTs.Paper1.EfficientORSet.EventSpec.conflict α)
    (Sal.MRDTs.Paper1.EfficientORSet.RawReplay.representation (α := α))
    (Sal.MRDTs.Paper1.EfficientORSet.RawReplay.scheme (α := α)) :=
  by derive_mrdt_input
register_mrdt_input input
end EfficientORSet
end Sal.MRDTs.Paper1.Automation.CommonInstances
