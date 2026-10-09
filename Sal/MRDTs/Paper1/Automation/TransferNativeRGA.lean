import Sal.MRDTs.Paper1.Automation.TransferSimple
import Sal.MRDTs.Instances.RGA
namespace Sal.MRDTs.Paper1.Automation.TransferProduct
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
namespace NativeRGA
open Instances.RGA

theorem kernels : TransferSimple.EmptyPastKernels RGAM := by
  constructor
  · intro l a b
    apply Prod.ext <;> funext x <;> simp [RGAM, Bool.or_comm]
  · intro s
    apply Prod.ext <;> funext x <;> simp [RGAM]
  · intro s e
    rcases e with ⟨t,r,op⟩
    cases op <;> apply Prod.ext <;> funext x <;>
      simp [RGAM, rgaUpdate, Bool.or_comm]
  · intro l B t b e
    rcases e with ⟨ts,r,op⟩
    cases op <;> apply Prod.ext <;> funext x <;>
      simp [RGAM, rgaUpdate, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
  · intro B t₀ t₁ t₂ e
    rcases e with ⟨ts,r,op⟩
    cases op <;> apply Prod.ext <;> funext x <;>
      simp [RGAM, rgaUpdate, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]


end NativeRGA
end Sal.MRDTs.Paper1.Automation.TransferProduct
