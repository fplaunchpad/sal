import Sal.MRDTs.Paper1.EventBridge
import Sal.MRDTs.Paper1.Capstone

/-! The exact paper OR-set with the full timestamp/replica/update alphabet.
The independent ordinary-set machine may ignore metadata; it stores neither
add tags nor implementation states. Concrete updates, merge, and issuance are
unchanged. -/
namespace Sal.MRDTs.Paper1.ORSet.EventSpec
open Foundation
variable {α : Type} [DecidableEq α]

def model (α : Type) [DecidableEq α] :
    DeterministicSpec (Op (Update α)) α Bool where
  State := Finset α
  initial := ∅
  update s e := abstractStep s e.op
  query s x := decide (x ∈ s)

def spec (α : Type) [DecidableEq α] : HistorySpec (Op (Update α)) α Bool :=
  (model α).toSpec

theorem spec_eq : spec α = (ORSet.spec α).toSpec.withInputs Op.op :=
  by
    have hm : (model α).machine = (ORSet.spec α).machine.withInputs Op.op := by
      unfold model ORSet.spec DeterministicSpec.machine HistoryMachine.withInputs
      congr 1
      funext s label t
      cases label <;> rfl
    change (model α).machine.toSpec = _
    rw [hm]
    exact (ORSet.spec α).machine.toSpec_withInputs Op.op

/-- Ignoring irrelevant event inputs preserves contextual specification
conflicts exactly, rather than merely preserving selected examples. -/
theorem commutes_iff (a b : Op (Update α)) :
    (spec α).Commutes a b ↔ (ORSet.spec α).toSpec.Commutes a.op b.op := by
  rw [spec_eq]
  exact HistorySpec.withInputs_commutes_iff _ Op.op
    (fun op => ⟨(0, 0, op), rfl⟩) a b

def projectionDescription : MachineProjection (D α) (model α) id where
  project := view
  initial := by simp [D, model, view]
  update := finiteDescription.project_update
  observes _ _ := rfl

def simulation : EventSequentialSimulation (D α) (model α) := by
  derive_projected_simulation projectionDescription

theorem commutationCompatibility : CommutationCompatibility (D α) id (spec α) := by
  intro a b hc
  apply projectionDescription.language_commutes _ a b hc
  intro s
  exact ⟨s.image (fun x => (x, 0)), finiteDescription.representative
    (fun x => (x, 0)) (fun _ => rfl) s⟩

theorem foldHistorySound : EventFoldHistorySound (D α) (spec α) := simulation.sound

/-- The full-input guarantee is discharged by the generic restricted-policy
bridge, including every stored ancestor version. -/
theorem certifiedVersionsRAV :
    EventCertifiedSpecificationRAV (D α) (conflict α) (spec α) (issuance α) := by
  letI : ReplayPolicy (D α).toUpdateSig := (conflict α).lift
  apply event_certified_of_join_total restrictedLaws _ commutationCompatibility foldHistorySound
  intro C _
  rw [conflict_lift_eq]
  exact @Join.at (D α) policy join C.replayContext

theorem certifiedVersionsRA :
    EventCertifiedSpecificationRA (D α) (conflict α) (spec α) (issuance α) :=
  certifiedVersionsRAV.ordinary


theorem certifiedRA (C : Configuration (D α))
    (reach : MintCertifiedReach (D α) (issuance α) C) :
    EventSpecificationRALinearizable (D α) (conflict α) (spec α) C := by
  rw [spec_eq]
  exact projected_withInputs (project := id)
    (projected_original_iff.mpr (specificationCertifiedRA C reach))

theorem certifiedRAV (C : Configuration (D α))
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) (issuance α) C) :
    EventSpecificationRALinearizable (D α) (conflict α) (spec α) C := by
  rw [spec_eq]
  exact projected_withInputs (project := id)
    (projected_original_iff.mpr (specificationCertifiedRAV C reach))

theorem certifiedLiteralRA (C : Configuration (D α))
    (reach : MintCertifiedReach (D α) (issuance α) C) :
    EventRALinearizable (D α) (conflict α) (spec α) C := (certifiedRA C reach).active

theorem certifiedLiteralRAV (C : Configuration (D α))
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) (issuance α) C) :
    EventRALinearizable (D α) (conflict α) (spec α) C := (certifiedRAV C reach).active

theorem certifiedExecutions (trace : List (Label (D α) × Configuration (D α)))
    (execution : (certifiedTS (D α) (issuance α)).Execution (initConfig (D α)) trace) :
    ProjectedSpecificationExecution (D α) (conflict α) id (spec α) (initConfig (D α)) trace :=
  projected_certified_executions certifiedRA trace execution

theorem certifiedExecutionsV (trace : List (Label (D α) × Configuration (D α)))
    (execution : (certifiedTSV (D α) (issuance α)).Execution (initConfig (D α)) trace) :
    ProjectedSpecificationExecution (D α) (conflict α) id (spec α) (initConfig (D α)) trace :=
  projected_certified_executionsV certifiedRAV trace execution

/-- Exact OR-set also explains arbitrary raw executions with the full inputs. -/
theorem rawRA {C : Configuration (D α)}
    (reach : (labeledTS (D α)).ReachableFrom (initConfig (D α)) C) :
    EventSpecificationRALinearizable (D α) (conflict α) (spec α) C := by
  rw [spec_eq]
  exact projected_withInputs (project := id)
    (projected_original_iff.mpr (rawSpecificationRA reach))

/-- PASS+FAIL: metadata need not increase in a chosen history; ordinary set
removal still has an observable effect. -/
example : (spec Nat).admits [.update (9, 4, .add 7), .update (2, 1, .remove 7),
      .query 7 false] ∧
    ¬ (spec Nat).admits [.update (9, 4, .add 7), .update (2, 1, .remove 7),
      .query 7 true] := by
  change (model Nat).toSpec.admits
      (DeterministicSpec.updateLabels [(9, 4, Update.add 7), (2, 1, Update.remove 7)] ++
        [.query 7 false]) ∧
    ¬ (model Nat).toSpec.admits
      (DeterministicSpec.updateLabels [(9, 4, Update.add 7), (2, 1, Update.remove 7)] ++
        [.query 7 true])
  rw [DeterministicSpec.updates_query_iff, DeterministicSpec.updates_query_iff]
  simp [model, abstractStep, Op.op]

#print axioms simulation
#print axioms certifiedVersionsRA
#print axioms certifiedVersionsRAV
#print axioms certifiedRA
#print axioms certifiedRAV
#print axioms rawRA
end Sal.MRDTs.Paper1.ORSet.EventSpec
