import Sal.MRDTs.Paper1.GuardedORSet

/-! Research oracle: exact noncommutation restricted to distinct application
operations, retaining concrete equality and the production implementation.
Equal application operations remain outside the equation; causal ordering and
raw noncommutation still control them, including their role as absorbers. -/
namespace Sal.MRDTs.Paper1.EfficientORSet.DistinctOperation
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]

/-- No timestamp or replica side condition is needed for distinct payloads. -/
theorem noncomm_exact (a b : Event α) (hne : a.op ≠ b.op) :
    (¬ (D α).toUpdateSig.commutes a b ↔
      (EventSpec.conflict α).before a.op b.op ∨
      (EventSpec.conflict α).before b.op a.op) := by
  constructor
  · intro hn
    have he := EventSpec.noncomm_same_element a b hn
    rcases a with ⟨ta, ra, oa⟩
    rcases b with ⟨tb, rb, ob⟩
    cases oa with
    | add x =>
      cases ob with
      | add y => exact False.elim (hne (by simpa [Op.op, element] using he))
      | remove y =>
        have hxy : x = y := he
        subst y
        exact Or.inr ⟨x, rfl, rfl⟩
    | remove x =>
      cases ob with
      | add y =>
        have hxy : x = y := he
        subst y
        exact Or.inl ⟨x, rfl, rfl⟩
      | remove y => exact False.elim (hne (by simpa [Op.op, element] using he))
  · rintro (⟨x, ha, hb⟩ | ⟨x, hb, ha⟩)
    · rcases a with ⟨ta, ra, oa⟩
      rcases b with ⟨tb, rb, ob⟩
      change oa = .remove x at ha
      change ob = .add x at hb
      subst oa
      subst ob
      intro hc
      exact EventSpec.add_remove_noncomm tb rb ta ra x (fun s => (hc s).symm)
    · rcases a with ⟨ta, ra, oa⟩
      rcases b with ⟨tb, rb, ob⟩
      change oa = .add x at ha
      change ob = .remove x at hb
      subst oa
      subst ob
      exact EventSpec.add_remove_noncomm ta ra tb rb x

/-- Equal timestamps and replicas do not compromise the revised exact law. -/
theorem same_metadata_control :
    ¬ (D Nat).toUpdateSig.commutes (1,0,.add 7) (1,0,.remove 7) ∧
    ¬ (EventSpec.conflict Nat).before (.add 7) (.remove 7) := by
  refine ⟨(noncomm_exact (1,0,.add 7) (1,0,.remove 7) (by decide)).mpr
    (Or.inr ⟨7,rfl,rfl⟩), ?_⟩
  rintro ⟨x,h,_⟩
  cases h

/-- Equal payloads neither imply nor refute concrete commutation. -/
theorem equal_operation_controls (x : α) :
    (D α).toUpdateSig.commutes (1,0,.add x) (2,1,.add x) ∧
    ¬ (D α).toUpdateSig.commutes (1,0,.add x) (2,0,.add x) :=
  ⟨EventSpec.distinct_replicas_adds_commute x, EventSpec.same_replica_adds_noncomm x⟩

/-- Causal replay keeps repeated local adds in order despite their exemption
from operation-policy exactness. The order still tests raw commutation. -/
theorem equal_operation_causal_order (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Event α)) (x : α)
    (hvis : C.vis (1,0,.add x) (2,0,.add x)) :
    paperOrder (EventSpec.conflict α) C E (1,0,.add x) (2,0,.add x) ∧
    ¬ (EventSpec.conflict α).before (.add x) (.add x) := by
  refine ⟨Or.inl ⟨hvis, EventSpec.same_replica_adds_noncomm x⟩, ?_⟩
  rintro ⟨y,h,_⟩
  cases h

/-- A same-operation causal successor really absorbs the differing prefixes;
a successor on another replica fails to do so. Both expected states are
hand-derived: the final local add replaces the old local tag. -/
theorem equal_operation_absorber_controls :
    update (update (update (∅ : State Nat) (2,0,.add 7)) (1,1,.remove 7))
      (3,0,.add 7) = {(0,3,7)} ∧
    update (update (update (∅ : State Nat) (1,1,.remove 7)) (2,0,.add 7))
      (3,0,.add 7) = {(0,3,7)} ∧
    update (update (∅ : State Nat) (2,0,.add 7)) (1,1,.remove 7) ≠
      update (update ∅ (1,1,.remove 7)) (2,0,.add 7) ∧
    update (update (update (∅ : State Nat) (2,0,.add 7)) (1,1,.remove 7))
      (3,2,.add 7) ≠
    update (update (update ∅ (1,1,.remove 7)) (2,0,.add 7))
      (3,2,.add 7) := by decide

#print axioms noncomm_exact
#print axioms equal_operation_absorber_controls
end Sal.MRDTs.Paper1.EfficientORSet.DistinctOperation
