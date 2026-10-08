import CommonVerification
import AutomatedORSet
import AutomatedEfficientORSet
import AutomatedMVR
import AutomatedRGA
import TransferLWW
import TransferProductExpansion
import TransferGuardedCommuting
import TransferAegisSheet

/-! Registered finite annotations for the current contracts. Completed datatype
VC theorems are neither registered nor invoked. The shared command selects an
input from the implementation/policy/representation/metadata indices. -/
namespace NeemExpansion.CommonInstances
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 ConcreteMRDT
open CommonVerification Sal.EmbedRGA

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
namespace LWW
open Instances.LWWRegister
attribute [local mrdt_implementation] D update
def kernels : TransferSimple.EmptyPastKernels D := by
  constructor <;> mrdt_finite
def input : Input D Sal.MRDTs.Paper1.LWW.GuardedPort.policy
    (CommutingPort.representation D) (CommutingPort.scheme all_comm) :=
  .commuting all_comm kernels rfl rfl rfl
register_mrdt_input input
end LWW
namespace NativeRGA
open Instances.RGA
def input : Input RGAM (commutingPolicy RGAOp)
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
namespace MVR
open Instances.MVRLive CertifiedQueueMVR.MVR.RawVC
def input : Input D policy representation scheme :=
  .immutable AutomatedMVR.model rfl (fun _ _ _ => Iff.rfl)
register_mrdt_input input
end MVR
namespace Embedded
open Instances.EmbedRGA CertifiedRGAVCReplay.Embedded
variable {α : Type} [DecidableEq α] [Inhabited α]
def input (Γ : OrderedPrefixCode) : Input (E Γ α) policy (representation (α := α) Γ) (scheme Γ) :=
  .ordered (AutomatedRGA.Embedded.kit Γ) (fun _ _ _ => Iff.rfl) (AutomatedRGA.Embedded.adapter Γ)
register_mrdt_input input
end Embedded
namespace Sided
open Instances.SidedEmbedRGA CertifiedRGAVCReplay.Sided
def input (Γ : OrderedPrefixCode) : Input (S Γ) policy (representation Γ) (scheme Γ) :=
  .ordered (AutomatedRGA.Sided.kit Γ) (fun _ _ _ => Iff.rfl) (AutomatedRGA.Sided.adapter Γ)
register_mrdt_input input
end Sided

variable {α : Type} [DecidableEq α]
theorem ordinaryORSet : Raw.MergeVCs (ORSet.conflict α)
    (ORSet.RawReplay.representation (α := α)) (ORSet.RawReplay.scheme (α := α)) := by mrdt_verify
theorem efficientORSet : Raw.MergeVCs (Sal.MRDTs.Paper1.EfficientORSet.EventSpec.conflict α)
    (Sal.MRDTs.Paper1.EfficientORSet.RawReplay.representation (α := α))
    (Sal.MRDTs.Paper1.EfficientORSet.RawReplay.scheme (α := α)) := by mrdt_verify

theorem gset : Raw.MergeVCs (commutingPolicy Nat)
    (CommutingPort.representation (Instances.AddStore.D Nat))
    (CommutingPort.scheme (Instances.AddStore.all_comm (α := Nat))) := by mrdt_verify
theorem addStore : Raw.MergeVCs (commutingPolicy Nat)
    (CommutingPort.representation (Instances.AddStore.D Nat))
    (CommutingPort.scheme (Instances.AddStore.all_comm (α := Nat))) := by mrdt_verify
theorem finiteAdd : Raw.MergeVCs (commutingPolicy Nat)
    (CommutingPort.representation (Instances.FinsetStore.D Nat))
    (CommutingPort.scheme (Instances.FinsetStore.all_comm (α := Nat))) := by mrdt_verify
theorem counter : Raw.MergeVCs (commutingPolicy Unit)
    (CommutingPort.representation (Instances.FlatCounters.D Unit (fun _ => 1)))
    (CommutingPort.scheme (Instances.FlatCounters.all_comm (fun _ : Unit => 1))) := by mrdt_verify
theorem ioc : Raw.MergeVCs (commutingPolicy Instances.FlatCounters.IOCOp)
    (CommutingPort.representation (Instances.FlatCounters.D Instances.FlatCounters.IOCOp (fun _ => 1)))
    (CommutingPort.scheme (Instances.FlatCounters.all_comm (fun _ : Instances.FlatCounters.IOCOp => 1))) := by mrdt_verify
theorem pn : Raw.MergeVCs (commutingPolicy Instances.FlatCounters.PNOp)
    (CommutingPort.representation (Instances.FlatCounters.D Instances.FlatCounters.PNOp Instances.FlatCounters.pnDelta))
    (CommutingPort.scheme (Instances.FlatCounters.all_comm Instances.FlatCounters.pnDelta)) := by mrdt_verify
theorem booleanSet : Raw.MergeVCs (commutingPolicy Nat)
    (CommutingPort.representation (Instances.FlatGrowOnly.D Nat))
    (CommutingPort.scheme (Instances.FlatGrowOnly.all_comm (A := Nat))) := by mrdt_verify
theorem booleanMap : Raw.MergeVCs (commutingPolicy (Nat × Nat))
    (CommutingPort.representation (Instances.FlatGrowOnly.D (Nat × Nat)))
    (CommutingPort.scheme (Instances.FlatGrowOnly.all_comm (A := Nat × Nat))) := by mrdt_verify
theorem lww : Raw.MergeVCs Sal.MRDTs.Paper1.LWW.GuardedPort.policy
    (CommutingPort.representation Instances.LWWRegister.D)
    (CommutingPort.scheme Instances.LWWRegister.all_comm) := by mrdt_verify
theorem nativeRGA : Raw.MergeVCs (commutingPolicy Instances.RGA.RGAOp)
    (CommutingPort.representation Instances.RGA.RGAM)
    (CommutingPort.scheme Instances.RGA.RGAM_all_comm) := by mrdt_verify
theorem bounded : Raw.MergeVCs (commutingPolicy Instances.BoundedCounter.BC.AppOp)
    (CommutingPort.representation Instances.BoundedCounter.BC)
    (CommutingPort.scheme Instances.BoundedCounter.BC_all_comm) := by mrdt_verify
theorem tree : Raw.MergeVCs (commutingPolicy Instances.TreeMove.D.AppOp)
    (CommutingPort.representation Instances.TreeMove.D)
    (CommutingPort.scheme Instances.TreeMove.all_comm) := by mrdt_verify
theorem aegis : Raw.MergeVCs (commutingPolicy Instances.AegisSheet.D.AppOp)
    (CommutingPort.representation Instances.AegisSheet.D)
    (CommutingPort.scheme Instances.AegisSheet.all_comm) := by mrdt_verify
theorem mvr : Raw.MergeVCs CertifiedQueueMVR.MVR.RawVC.policy
    CertifiedQueueMVR.MVR.RawVC.representation CertifiedQueueMVR.MVR.RawVC.scheme := by mrdt_verify
theorem sided (Γ : OrderedPrefixCode) : Raw.MergeVCs CertifiedRGAVCReplay.Sided.policy
    (CertifiedRGAVCReplay.Sided.representation Γ) (CertifiedRGAVCReplay.Sided.scheme Γ) := by mrdt_verify
theorem embedded {α : Type} [DecidableEq α] [Inhabited α] (Γ : OrderedPrefixCode) :
    Raw.MergeVCs CertifiedRGAVCReplay.Embedded.policy
      (CertifiedRGAVCReplay.Embedded.representation (α := α) Γ)
      (CertifiedRGAVCReplay.Embedded.scheme Γ) := by mrdt_verify
theorem anchored_queue : Raw.MergeVCs CertifiedRGAVCReplay.Embedded.policy
    (CertifiedRGAVCReplay.Embedded.representation (α := Nat) unaryCode)
    (CertifiedRGAVCReplay.Embedded.scheme unaryCode) := by mrdt_verify
theorem peritext (Γ : OrderedPrefixCode) : Raw.MergeVCs CertifiedRGAVCReplay.Embedded.policy
    (CertifiedPeritextVC.representation Γ) (CertifiedRGAVCReplay.Embedded.scheme Γ) := by mrdt_verify

#print axioms ordinaryORSet
#print axioms efficientORSet
#print axioms embedded
#print axioms mvr
end NeemExpansion.CommonInstances
