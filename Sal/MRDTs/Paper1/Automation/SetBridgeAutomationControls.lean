import Sal.MRDTs.Paper1.ORSetEventSpec
import Sal.MRDTs.Paper1.EfficientORSetEventSpec
import Sal.MRDTs.Paper1.Automation.SequentialBridgeControls

/-! Pin the representation relations of the generated proof certificates to
the original projections. These equalities cannot be supplied by a weaker
query relation or a constant abstraction. -/
namespace Sal.MRDTs.Paper1.Automation.SetBridgeAutomationControls
variable (α : Type) [DecidableEq α]

example : (ORSet.simulation (α := α)).Rel =
    (fun s a => ORSet.view s = a) := rfl

example : (ORSet.EventSpec.simulation (α := α)).Rel =
    (fun s a => ORSet.view s = a) := rfl

example : (EfficientORSet.EventSpec.simulation (α := α)).Rel =
    (fun s a => Instances.EfficientORSet.elements s = a) := rfl

example : ¬ (ORSet.EventSpec.simulation (α := Nat)).Rel
    ({(7, 1)} : Finset (Nat × Nat)) (∅ : Finset Nat) := by
  change ¬ ORSet.view {(7, 1)} = ∅
  simp [ORSet.view]

example : ¬ (EfficientORSet.EventSpec.simulation (α := Nat)).Rel
    ({(0, 1, 7)} : Finset (Nat × Nat × Nat)) (∅ : Finset Nat) := by
  change ¬ Instances.EfficientORSet.elements {(0, 1, 7)} = ∅
  simp [Instances.EfficientORSet.elements]

end Sal.MRDTs.Paper1.Automation.SetBridgeAutomationControls
