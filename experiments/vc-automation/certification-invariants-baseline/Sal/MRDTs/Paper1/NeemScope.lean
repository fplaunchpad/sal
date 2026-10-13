import Sal.MRDTs.Paper1.EfficientORSetEventSpec

/-! Audit of the local Neem F★ artifact. App_mrdt.fsti:64 requires distinct
timestamps AND different replica IDs for rc_non_comm. The efficient model uses
raw equality. This theorem checks that guarded scope; it does not claim the
unqualified operation-level condition displayed in Neem/lin.tex:387. -/
namespace Sal.MRDTs.Paper1.EfficientORSet.NeemScope
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
open Classical
variable {α : Type} [DecidableEq α]

theorem adds_commute_of_replica_ne (ta ra tb rb : Nat) (x y : α) (ne : ra ≠ rb) :
    (D α).toUpdateSig.commutes (ta,ra,.add x) (tb,rb,.add y) := by
  intro s
  change update (update s (ta,ra,.add x)) (tb,rb,.add y) =
    update (update s (tb,rb,.add y)) (ta,ra,.add x)
  ext p
  rcases p with ⟨r,t,z⟩
  simp only [update,Finset.mem_insert,Finset.mem_filter,Prod.mk.injEq]
  grind

theorem removes_commute (ta ra tb rb : Nat) (x y : α) :
    (D α).toUpdateSig.commutes (ta,ra,.remove x) (tb,rb,.remove y) := by
  intro s
  change update (update s (ta,ra,.remove x)) (tb,rb,.remove y) =
    update (update s (tb,rb,.remove y)) (ta,ra,.remove x)
  ext p
  rcases p with ⟨r,t,z⟩
  simp only [update,Finset.mem_filter]
  tauto

theorem guarded_noncomm_exact (a b : Event α) (ne : a.rep ≠ b.rep) :
    ¬ (D α).toUpdateSig.commutes a b ↔
      (EventSpec.conflict α).before a.op b.op ∨ (EventSpec.conflict α).before b.op a.op := by
  rcases a with ⟨ta,ra,ao⟩
  rcases b with ⟨tb,rb,bo⟩
  change ra ≠ rb at ne
  cases ao with
  | add x =>
    cases bo with
    | add y =>
      simp [EventSpec.conflict, Op.op, adds_commute_of_replica_ne ta ra tb rb x y ne]
    | remove y =>
      by_cases h : x = y
      · subst y
        simp [EventSpec.conflict, Op.op, EventSpec.add_remove_noncomm ta ra tb rb x]
      · have commute := EventSpec.different_elements_commute (ta,ra,.add x) (tb,rb,.remove y) h
        simp [EventSpec.conflict, Op.op, commute, h, Ne.symm h]
  | remove x =>
    cases bo with
    | remove y =>
      simp [EventSpec.conflict, Op.op, removes_commute ta ra tb rb x y]
    | add y =>
      by_cases h : x = y
      · subst y
        have noncomm : ¬ (D α).toUpdateSig.commutes (ta,ra,.remove x) (tb,rb,.add x) := by
          intro commute
          exact EventSpec.add_remove_noncomm tb rb ta ra x (fun s => (commute s).symm)
        simp [EventSpec.conflict, Op.op, noncomm]
      · have commute := EventSpec.different_elements_commute (ta,ra,.remove x) (tb,rb,.add y) h
        simp [EventSpec.conflict, Op.op, commute, h, Ne.symm h]

/-- PASS+FAIL: the source's guarded contract holds; the unqualified contract
is refuted by two timestamp-distinct adds from one replica. -/
theorem guarded_vs_unqualified (x : α) :
    (∀ a b : Event α, a.time ≠ b.time → a.rep ≠ b.rep →
      (¬ (D α).toUpdateSig.commutes a b ↔
        (EventSpec.conflict α).before a.op b.op ∨ (EventSpec.conflict α).before b.op a.op)) ∧
    ¬ RestrictedLaws (D α).toUpdateSig (EventSpec.conflict α) :=
  ⟨fun a b _ ne => guarded_noncomm_exact a b ne,
    EventSpec.restrictedLaws_impossible x (EventSpec.conflict α)⟩

end Sal.MRDTs.Paper1.EfficientORSet.NeemScope
