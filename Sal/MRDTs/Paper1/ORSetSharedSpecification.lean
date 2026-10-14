import Sal.MRDTs.Paper1.ORSetEventSpec
import Sal.MRDTs.Paper1.EfficientORSetEventSpec

/-! Ordinary and efficient OR-set have the same sequential client semantics.
This identifies whole accepted histories, including interspersed queries.
It makes no identification of their concrete states or conflict policies. -/
namespace Sal.MRDTs.Paper1.ORSetSharedSpecification
open Foundation
variable {α : Type} [DecidableEq α]

def efficientAction : ORSet.Update α → Instances.EfficientORSet.SetOp α
  | .add x => .add x
  | .remove x => .remove x

def efficientEvent (e : Op (ORSet.Update α)) :
    Op (Instances.EfficientORSet.SetOp α) :=
  (e.time, e.rep, efficientAction e.op)

/-- Retaining event metadata and renaming the two request constructors
preserves the complete independent history specification. -/
theorem specification_eq : ORSet.EventSpec.spec α =
    (EfficientORSet.EventSpec.spec α).withInputs efficientEvent := by
  have hm : (ORSet.EventSpec.model α).machine =
      (EfficientORSet.EventSpec.model α).machine.withInputs efficientEvent := by
    unfold ORSet.EventSpec.model EfficientORSet.EventSpec.model NaturalSetSpec.model
      DeterministicSpec.machine HistoryMachine.withInputs
    congr 1
    funext s label t
    cases label with
    | query q v => rfl
    | update e =>
      rcases e with ⟨time, rep, op⟩
      cases op <;> rfl
  change (ORSet.EventSpec.model α).machine.toSpec = _
  rw [hm]
  exact (EfficientORSet.EventSpec.model α).machine.toSpec_withInputs efficientEvent

theorem admits_iff (history : List (SeqLabel (Op (ORSet.Update α)) α Bool)) :
    (ORSet.EventSpec.spec α).admits history ↔
      (EfficientORSet.EventSpec.spec α).admits
        (history.map (SeqLabel.mapUpdate efficientEvent)) := by
  rw [specification_eq]
  rfl

#print axioms specification_eq
#print axioms admits_iff
end Sal.MRDTs.Paper1.ORSetSharedSpecification
