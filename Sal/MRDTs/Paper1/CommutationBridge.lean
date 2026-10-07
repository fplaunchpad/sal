import Sal.MRDTs.Paper1.HistoryInputs
import Sal.MRDTs.Paper1.ORSetSpecification
import Sal.MRDTs.Paper1.CriterionCounterexample

/-!
# Observable commutation compatibility for the sequential-history bridge

This VC relates concrete updates to an independent history language. It is
separate from the five merge VCs and does not replace history acceptance.
`HistorySpec.Commutes` observes language admission in all prefix/suffix
contexts, including future updates and queries; it never compares abstract
machine states. Global compatibility is sufficient, not necessary: the issued
chosen-history route remains available when this VC fails.
-/
namespace Sal.MRDTs.Paper1
open Foundation

/-- Concrete commutation must preserve contextual observable commutation.
Use `project := id` for the agreed full timestamp/replica/operation inputs. -/
def CommutationCompatibility (D : MRDTSig) {U : Type}
    (project : Op D.AppOp → U) (S : HistorySpec U D.Query D.Value) : Prop :=
  ∀ a b, D.toUpdateSig.commutes a b → S.Commutes (project a) (project b)

/-- The previously used conflict-coverage premise is precisely the
contrapositive of commutation compatibility for operation-only labels. -/
theorem commutationCompatibility_iff_conflictsCovered {D : MRDTSig}
    {S : HistorySpec D.AppOp D.Query D.Value} :
    CommutationCompatibility D Op.op S ↔ SpecificationConflictsCovered D S := by
  classical
  constructor
  · intro compatible a b conflict commute
    exact conflict (compatible a b commute)
  · intro covered a b commute
    by_contra conflict
    exact covered a b conflict commute

theorem projectedSpecVisibility_sub_paperOrder {D : MRDTSig}
    {U : Type} {project : Op D.AppOp → U} {S : HistorySpec U D.Query D.Value}
    {P : OperationPolicy D.AppOp}
    (compatible : CommutationCompatibility D project S)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp)) (a b : Op D.AppOp)
    (h : projectedSpecVisibility project S C a b) : paperOrder P C E a b :=
  Or.inl ⟨h.1, fun commute => h.2 (compatible a b commute)⟩

/-- For full event inputs, a literal RA witness already preserves specification
conflict visibility when the compatibility VC holds. No history premise is
lost: it is supplied by `literal`. -/
theorem eventSpecificationRA_of_compatibility {D : MRDTSig}
    {P : OperationPolicy D.AppOp} {S : HistorySpec (Op D.AppOp) D.Query D.Value}
    {C : Configuration D}
    (compatible : CommutationCompatibility D id S)
    (literal : EventRALinearizable D P S C) :
    EventSpecificationRALinearizable D P S C := by
  intro r v s E hh hv q
  obtain ⟨π, hp, ho, ha⟩ := literal r v s E hh hv q
  refine ⟨π, hp, ho, ?_, ha⟩
  exact ho.imp (fun {_ _} h => h ∘
    projectedSpecVisibility_sub_paperOrder compatible C.replayContext E _ _)

/-- Compatibility strengthens the existing five-VC soundness route. The
independent sequential-history acceptance premise is still required. -/
theorem specificationRA_of_fiveVCs_compatible {D : MRDTSig}
    {P : OperationPolicy D.AppOp} {S : HistorySpec D.AppOp D.Query D.Value}
    {I : Issuance D}
    (restricted : RestrictedLaws D.toUpdateSig P) (vcs : PaperMergeVCs D P)
    (compatible : CommutationCompatibility D Op.op S)
    (sequential : FoldHistorySound D S)
    {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C) :
    SpecificationRALinearizable D P S C := by
  letI : ReplayPolicy D.toUpdateSig := P.lift
  exact specificationRA_of_canonical_total restricted
    (canonicalConfig_of_mintCertifiedV
      (fun C _ => (vcs.toCanonical restricted).join C.replayContext) reach)
    (commutationCompatibility_iff_conflictsCovered.mp compatible) sequential

/-- Positive control: the exact OR-set and its ordinary-set language satisfy
the compatibility VC. -/
theorem ORSet.commutationCompatibility {α : Type} [DecidableEq α] :
    CommutationCompatibility (ORSet.D α) Op.op (ORSet.spec α).toSpec :=
  ORSet.language_commutes_of_concrete

/-- Positive control for the agreed full-input alphabet; the ordinary-set
specification is allowed to ignore metadata. -/
theorem ORSet.eventCommutationCompatibility {α : Type} [DecidableEq α] :
    CommutationCompatibility (ORSet.D α) id
      ((ORSet.spec α).toSpec.withInputs Op.op) := by
  intro a b commute
  exact HistorySpec.withInputs_commutes _ _
    (ORSet.commutationCompatibility a b commute)

/-- Negative control: the no-op-removal mutant fails the bridge VC even though
it satisfies the literal RA criterion. -/
theorem CriterionCounterexample.commutationCompatibility_fails :
    ¬ CommutationCompatibility CriterionCounterexample.D Op.op
      CriterionCounterexample.spec := by
  intro compatible
  exact CriterionCounterexample.specification_conflicts_coverage_fails
    (commutationCompatibility_iff_conflictsCovered.mp compatible)

end Sal.MRDTs.Paper1
