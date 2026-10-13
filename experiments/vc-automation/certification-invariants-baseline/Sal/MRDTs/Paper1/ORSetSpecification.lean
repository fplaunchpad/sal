import Sal.MRDTs.Paper1.ORSetVerified
import Sal.MRDTs.Paper1.SpecificationVisibility

/-! Positive comparison for the separately stated specification-visible criterion.
The exact paper OR-set preserves conflicts observable in the ordinary-set
history language, in addition to satisfying the active literal criterion. -/
namespace Sal.MRDTs.Paper1.ORSet
open Sal.MRDTs.Foundation
variable {α : Type} [DecidableEq α]

/-- Concrete commutation entails a contextual swap in the natural set language.
Every abstract finite set has a concrete representative, obtained by tagging
all its elements with zero. These are proof states, not issued histories. -/
theorem language_commutes_of_concrete (a b : Op (Update α))
    (hc : (D α).toUpdateSig.commutes a b) :
    (spec α).toSpec.Commutes a.op b.op := by
  apply projectionDescription.language_commutes _ a b hc
  intro s
  exact ⟨s.image (fun x => (x, 0)), finiteDescription.representative
    (fun x => (x, 0)) (fun _ => rfl) s⟩

/-- The specification-visible criterion's additional sequential premise holds for the exact OR-set. -/
theorem specificationConflictsCovered :
    SpecificationConflictsCovered (D α) (spec α).toSpec := by
  intro a b hn hc
  exact hn (language_commutes_of_concrete a b hc)

/-- An ordinary set history ending with a read distinguishes add/remove order,
so same-element adds and removes really conflict in the independent language. -/
theorem natural_add_remove_conflict (x : α) :
    ¬ (spec α).toSpec.Commutes (.add x) (.remove x) := by
  intro h
  have accepted : (spec α).toSpec.admits
      (DeterministicSpec.updateLabels [.add x, .remove x] ++ [.query x false]) := by
    rw [DeterministicSpec.updates_query_iff]
    simp [spec, abstractStep]
  have rejected : ¬ (spec α).toSpec.admits
      (DeterministicSpec.updateLabels [.remove x, .add x] ++ [.query x false]) := by
    rw [DeterministicSpec.updates_query_iff]
    simp [spec, abstractStep]
  apply rejected
  simpa [DeterministicSpec.updateLabels] using
    (h [] [.query x false]).mp (by simpa [DeterministicSpec.updateLabels] using accepted)

/-- Virtual and ordinary certified reachability both satisfy the separate
specification-visible criterion. This theorem does not redefine the active criterion. -/
theorem specificationCertifiedRAV :
    ∀ C, MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) (issuance α) C →
      SpecificationRALinearizable (D α) (conflict α) (spec α).toSpec C := by
  letI : ReplayPolicy (D α).toUpdateSig := (conflict α).lift
  intro C reach
  have hjoin : ∀ C, MintHonest (D α) (issuance α).CanIssue C →
      @JoinAt (D α) (conflict α).lift C.replayContext := by
    intro C _
    rw [conflict_lift_eq]
    exact @Join.at (D α) policy join C.replayContext
  exact specificationRA_of_canonical_total restrictedLaws
    (canonicalConfig_of_mintCertifiedV hjoin reach) specificationConflictsCovered foldHistorySound

theorem specificationCertifiedRA :
    ∀ C, MintCertifiedReach (D α) (issuance α) C →
      SpecificationRALinearizable (D α) (conflict α) (spec α).toSpec C := by
  intro C reach
  exact specificationCertifiedRAV C reach.toV

#print axioms specificationConflictsCovered
#print axioms natural_add_remove_conflict
#print axioms specificationCertifiedRAV
#print axioms specificationCertifiedRA
end Sal.MRDTs.Paper1.ORSet
