import Sal.MRDTs.Paper1.Automation.TransferSimple
import Sal.MRDTs.Instances.RGA
namespace Sal.MRDTs.Paper1.Automation.TransferProduct
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
namespace NativeRGA
open Instances.RGA

theorem kernels : TransferSimple.EmptyPastKernels RGAM := by
  constructor <;> mrdt_representation [RGAM,rgaUpdate]

end NativeRGA
end Sal.MRDTs.Paper1.Automation.TransferProduct
