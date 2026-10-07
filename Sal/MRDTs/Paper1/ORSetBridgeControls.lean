import Sal.MRDTs.Paper1.ORSetEventSpec
import Sal.MRDTs.Paper1.EfficientORSetEventSpec

/-! Hand-derived full-input controls for the ordinary-set history bridge.
Metadata is retained in update labels. An add followed by removal returns
false; true is the tempting no-op-removal result and must be rejected. -/
namespace Sal.MRDTs.Paper1.ORSetBridgeControls
open Foundation
open Sal.MRDTs.Instances.EfficientORSet (SetOp setStep)

/-- PASS+FAIL for the exact paper OR-set's independent ordinary-set language. -/
theorem exact_remove_control : (ORSet.EventSpec.spec Nat).admits
      [.update (1, 0, .add 7), .update (2, 1, .remove 7), .query 7 false] ∧
    ¬ (ORSet.EventSpec.spec Nat).admits
      [.update (1, 0, .add 7), .update (2, 1, .remove 7), .query 7 true] := by
  change (ORSet.EventSpec.model Nat).toSpec.admits
      (DeterministicSpec.updateLabels [(1, 0, ORSet.Update.add 7),
        (2, 1, ORSet.Update.remove 7)] ++ [.query 7 false]) ∧
    ¬ (ORSet.EventSpec.model Nat).toSpec.admits
      (DeterministicSpec.updateLabels [(1, 0, ORSet.Update.add 7),
        (2, 1, ORSet.Update.remove 7)] ++ [.query 7 true])
  rw [DeterministicSpec.updates_query_iff, DeterministicSpec.updates_query_iff]
  simp [ORSet.EventSpec.model, ORSet.abstractStep, Op.op]

/-- PASS+FAIL for the production efficient OR-set's independent set language. -/
theorem efficient_remove_control : (EfficientORSet.EventSpec.spec Nat).admits
      [.update (1, 0, .add 7), .update (2, 1, .remove 7), .query 7 false] ∧
    ¬ (EfficientORSet.EventSpec.spec Nat).admits
      [.update (1, 0, .add 7), .update (2, 1, .remove 7), .query 7 true] := by
  change (EfficientORSet.EventSpec.model Nat).toSpec.admits
      (DeterministicSpec.updateLabels [(1, 0, SetOp.add 7),
        (2, 1, SetOp.remove 7)] ++ [.query 7 false]) ∧
    ¬ (EfficientORSet.EventSpec.model Nat).toSpec.admits
      (DeterministicSpec.updateLabels [(1, 0, SetOp.add 7),
        (2, 1, SetOp.remove 7)] ++ [.query 7 true])
  rw [DeterministicSpec.updates_query_iff, DeterministicSpec.updates_query_iff]
  simp [EfficientORSet.EventSpec.model, setStep]

/-- One-element ordinary-set language over the mutant's exact input tuples. -/
def mutantSpec : HistorySpec (Op CriterionCounterexample.Update) Unit Bool :=
  CriterionCounterexample.spec.withInputs Op.op

/-- PASS+FAIL pins the intended causal answer independently of the mutant. -/
theorem mutant_causal_control : mutantSpec.admits
      [.update CriterionCounterexample.addEvent, .update CriterionCounterexample.removeEvent,
        .query () false] ∧
    ¬ mutantSpec.admits
      [.update CriterionCounterexample.addEvent, .update CriterionCounterexample.removeEvent,
        .query () true] :=
  ⟨CriterionCounterexample.causal_history_admitted,
    CriterionCounterexample.causal_history_rejects_true⟩

/-- Retaining timestamp and replica labels cannot hide the no-op-removal bug.
Surjective metadata stripping reflects contextual commutation exactly. -/
theorem mutant_compatibility_fails :
    ¬ CommutationCompatibility CriterionCounterexample.D id mutantSpec := by
  intro compatible
  apply CriterionCounterexample.commutationCompatibility_fails
  intro a b commute
  exact (HistorySpec.withInputs_commutes_iff CriterionCounterexample.spec Op.op
    (fun op => ⟨(0, 0, op), rfl⟩) a b).mp (compatible a b commute)

/-- PASS+FAIL for the bridge VC: both genuine set implementations pass, while
identity removal fails against the same independent ordinary-set behavior. -/
theorem compatibility_controls :
    CommutationCompatibility (ORSet.D Nat) id (ORSet.EventSpec.spec Nat) ∧
    CommutationCompatibility (Sal.MRDTs.Instances.EfficientORSet.D Nat) id
      (EfficientORSet.EventSpec.spec Nat) ∧
    ¬ CommutationCompatibility CriterionCounterexample.D id mutantSpec :=
  ⟨ORSet.EventSpec.commutationCompatibility,
    EfficientORSet.EventSpec.commutationCompatibility, mutant_compatibility_fails⟩

#print axioms exact_remove_control
#print axioms efficient_remove_control
#print axioms mutant_causal_control
#print axioms mutant_compatibility_fails
#print axioms compatibility_controls
end Sal.MRDTs.Paper1.ORSetBridgeControls
