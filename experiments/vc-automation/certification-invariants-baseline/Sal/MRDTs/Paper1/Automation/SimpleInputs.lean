import Sal.MRDTs.Paper1.Automation.CommonVerification
import Sal.MRDTs.Paper1.Automation.TransferSimple
namespace Sal.MRDTs.Paper1.Automation.CommonInstances
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 ConcreteMRDT
open Sal.MRDTs.Paper1.Automation.CommonVerification
namespace Add
open Instances.AddStore
variable {A : Type} [DecidableEq A]
def input : Input (D A) (commutingPolicy A) (CommutingPort.representation (D A))
    (CommutingPort.scheme (all_comm (α := A))) :=
  .commuting all_comm TransferSimple.Add.kernels rfl rfl rfl
register_mrdt_input input
end Add
namespace Finite
open Instances.FinsetStore
variable {A : Type} [DecidableEq A]
def input : Input (D A) (commutingPolicy A) (CommutingPort.representation (D A))
    (CommutingPort.scheme (all_comm (α := A))) :=
  .commuting all_comm TransferSimple.Finite.kernels rfl rfl rfl
register_mrdt_input input
end Finite
namespace Delta
open Instances.FlatCounters
variable {A : Type} [DecidableEq A]
def input (delta : A → Int) : Input (D A delta) (commutingPolicy A)
    (CommutingPort.representation (D A delta)) (CommutingPort.scheme (all_comm delta)) :=
  .commuting (all_comm delta) (TransferSimple.Delta.kernels delta) rfl rfl rfl
register_mrdt_input input
end Delta
namespace Boolean
open Instances.FlatGrowOnly
variable {A : Type} [DecidableEq A]
def input : Input (D A) (commutingPolicy A) (CommutingPort.representation (D A))
    (CommutingPort.scheme (all_comm (A := A))) :=
  .commuting all_comm TransferSimple.Boolean.kernels rfl rfl rfl
register_mrdt_input input
end Boolean
end Sal.MRDTs.Paper1.Automation.CommonInstances
