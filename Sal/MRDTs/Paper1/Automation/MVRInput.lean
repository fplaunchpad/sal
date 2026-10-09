import Sal.MRDTs.Paper1.Automation.CommonVerification
import Sal.MRDTs.Paper1.Automation.AutomatedMVR
namespace Sal.MRDTs.Paper1.Automation.CommonInstances
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 ConcreteMRDT
open Sal.MRDTs.Paper1.Automation.CommonVerification
namespace MVR
open Instances.MVRLive CertifiedQueueMVR.MVR.RawVC
def input : Input D policy representation scheme :=
  .immutable AutomatedMVR.model rfl (fun _ _ _ => Iff.rfl)
register_mrdt_input input
end MVR
end Sal.MRDTs.Paper1.Automation.CommonInstances
