import Sal.MRDTs.Paper1.AbstractORSet

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

theorem concrete_iff_observable_of_replica_ne (a b : Event α) (ne : a.rep ≠ b.rep) :
    (D α).toUpdateSig.commutes a b ↔ QueryReplay.Commutes (D α) a b := by
  refine ⟨QueryReplay.of_state_commutes,?_⟩
  intro hc
  rcases a with ⟨ta,ra,ao⟩
  rcases b with ⟨tb,rb,bo⟩
  change ra ≠ rb at ne
  cases ao with
  | add x =>
    cases bo with
    | add y => exact adds_commute_of_replica_ne ta ra tb rb x y ne
    | remove y =>
      by_cases h : x = y
      · subst y
        exact False.elim (QuerySpec.add_remove_conflict ta ra tb rb x hc)
      · exact EventSpec.different_elements_commute _ _ h
  | remove x =>
    cases bo with
    | remove y => exact removes_commute ta ra tb rb x y
    | add y =>
      by_cases h : x = y
      · subst y
        exact False.elim (QuerySpec.add_remove_conflict tb rb ta ra x (QuerySpec.commutes_symm hc))
      · exact EventSpec.different_elements_commute _ _ h

theorem guarded_noncomm_exact (a b : Event α) (ne : a.rep ≠ b.rep) :
    ¬ (D α).toUpdateSig.commutes a b ↔
      (EventSpec.conflict α).before a.op b.op ∨ (EventSpec.conflict α).before b.op a.op := by
  rw [concrete_iff_observable_of_replica_ne a b ne]
  exact QuerySpec.noncomm_exact a b

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
