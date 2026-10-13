import Sal.MRDTs.Paper1.Automation.CommonVerification
import Sal.MRDTs.Paper1.Automation.TransferLWW
import Sal.MRDTs.Paper1.Automation.TransferNativeRGA
import Sal.MRDTs.Paper1.Automation.TransferGuardedCommuting
import Sal.MRDTs.Paper1.Automation.TransferAegisSheet
namespace Sal.MRDTs.Paper1.Automation.CommonInstances
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 ConcreteMRDT
open Sal.MRDTs.Paper1.Automation.CommonVerification
namespace LWW
open Instances.LWWRegister

def kernels : TransferSimple.EmptyPastKernels D := TransferLWW.kernels
def input : Input D (commutingPolicy D.AppOp)
    (CommutingPort.representation D) (CommutingPort.scheme all_comm) :=
  .commuting all_comm kernels rfl rfl rfl
register_mrdt_input input
end LWW
namespace NativeRGA
open Instances.RGA
def input : Input RGAM (commutingPolicy RGAM.AppOp)
    (CommutingPort.representation RGAM) (CommutingPort.scheme RGAM_all_comm) :=
  .commuting RGAM_all_comm TransferProduct.NativeRGA.kernels rfl rfl rfl
register_mrdt_input input
end NativeRGA
namespace Bounded
open Instances.BoundedCounter
def input : Input BC (commutingPolicy BC.AppOp)
    (CommutingPort.representation BC) (CommutingPort.scheme BC_all_comm) :=
  .commuting BC_all_comm TransferGuardedCommuting.Bounded.kernels rfl rfl rfl
register_mrdt_input input
end Bounded
namespace Tree
open Instances.TreeMove
def input : Input D (commutingPolicy D.AppOp)
    (CommutingPort.representation D) (CommutingPort.scheme all_comm) :=
  .commuting all_comm TransferGuardedCommuting.Tree.kernels rfl rfl rfl
register_mrdt_input input
end Tree
namespace Aegis
open Instances.AegisSheet
def input : Input D (commutingPolicy D.AppOp)
    (CommutingPort.representation D) (CommutingPort.scheme all_comm) :=
  .commuting all_comm TransferAegisSheet.kernels rfl rfl rfl
register_mrdt_input input
end Aegis
end Sal.MRDTs.Paper1.Automation.CommonInstances
