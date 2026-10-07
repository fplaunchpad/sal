import Sal.MRDTs.Paper1.QueryReplay
import Sal.MRDTs.Paper1.ORSetEventSpec

/-! Exact tagged OR-set through the same observable canonical-history bridge
as the efficient representation. Concrete equality proofs remain sufficient
evidence; equality in the replay algebra is observational for both sets. -/
namespace Sal.MRDTs.Paper1.ORSet.QuerySpec
open Foundation
open QueryReplay
open Classical
variable {α : Type} [DecidableEq α]

def abstraction : QueryReplay.Abstraction (D α) where
  Abstract := Finset α
  abs := view
  step s e := abstractStep s e.op
  read s x := decide (x ∈ s)
  update_abs := view_step
  query_abs _ _ := rfl
  separates a b h := by
    ext x
    have hx := h x
    by_cases ha : x ∈ a <;> by_cases hb : x ∈ b <;> simp_all

theorem specificationCompatibility :
    QueryReplay.SpecificationCompatibility (D α) (EventSpec.spec α) := by
  intro a b hc
  apply DeterministicSpec.language_commutes
  intro s
  let repr : State α := s.image (fun x => (x,0))
  have hv : view repr = s := by
    simp [repr,view,Finset.image_image,Function.comp_def]
  have same := (abstraction.equivalent_iff _ _).mp (hc repr)
  change view (step (step repr a) b) = view (step (step repr b) a) at same
  simpa only [view_step,hv] using same

theorem commutes_iff_concrete (a b : Op (Update α)) :
    QueryReplay.Commutes (D α) a b ↔ (D α).toUpdateSig.commutes a b := by
  constructor
  · intro hc
    by_contra hn
    have hs := (EventSpec.commutes_iff a b).mp (specificationCompatibility a b hc)
    rcases (restrictedLaws.noncomm_exact a b).mp hn with edge | edge
    · obtain ⟨x,ha,hb⟩ := edge
      rw [ha,hb] at hs
      exact natural_add_remove_conflict x (HistorySpec.commutes_symm hs)
    · obtain ⟨x,hb,ha⟩ := edge
      rw [ha,hb] at hs
      exact natural_add_remove_conflict x hs
  · exact of_state_commutes

theorem laws : QueryReplay.Laws (D α) (conflict α) :=
  QueryReplay.Laws.of_concrete restrictedLaws commutes_iff_concrete

theorem canonical_of_execution {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) (issuance α) C) :
    ∀ v s E, C.ver v = some (s,E) →
      QueryReplay.Canonical (D α) (conflict α) C.replayContext E s := by
  letI : ReplayPolicy (D α).toUpdateSig := (conflict α).lift
  have hjoin : ∀ C, MintHonest (D α) (issuance α).CanIssue C →
      @JoinAt (D α) (conflict α).lift C.replayContext := by
    intro C _
    rw [conflict_lift_eq]
    exact @Join.at (D α) policy join C.replayContext
  have canonical := canonicalConfig_of_mintCertifiedV hjoin reach
  intro v s E hv
  exact QueryReplay.canonical_of_concrete restrictedLaws laws C.replayContext E s
    (canonical.canonical v s E hv)

theorem certifiedVersionsRAV {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) (issuance α) C) :
    QueryReplay.VersionsRALinearizable (D α) (conflict α) (EventSpec.spec α) C :=
  QueryReplay.of_canonical laws (canonical_of_execution reach)
    specificationCompatibility EventSpec.foldHistorySound

theorem certifiedVersionsRA {C : Configuration (D α)}
    (reach : MintCertifiedReach (D α) (issuance α) C) :
    QueryReplay.VersionsRALinearizable (D α) (conflict α) (EventSpec.spec α) C :=
  certifiedVersionsRAV reach.toV

theorem certifiedRA {C : Configuration (D α)}
    (reach : MintCertifiedReach (D α) (issuance α) C) :
    QueryReplay.RALinearizable (D α) (conflict α) (EventSpec.spec α) C :=
  (certifiedVersionsRA reach).heads

theorem certifiedRAV {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) (issuance α) C) :
    QueryReplay.RALinearizable (D α) (conflict α) (EventSpec.spec α) C :=
  (certifiedVersionsRAV reach).heads

end Sal.MRDTs.Paper1.ORSet.QuerySpec
