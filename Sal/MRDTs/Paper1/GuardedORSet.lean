import Sal.MRDTs.Paper1.GuardedReplay
import Sal.MRDTs.Paper1.NeemScope
import Sal.MRDTs.Paper1.ORSetEventSpec

namespace Sal.MRDTs.Paper1.EfficientORSet.Guarded
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
open Classical
variable {α : Type} [DecidableEq α]

def AgreeAway (r : Nat) (x : α) (s t : State α) : Prop :=
  ∀ p, ¬ (p.1 = r ∧ p.2.2 = x) → (p ∈ s ↔ p ∈ t)

theorem agree_update {r : Nat} {x : α} {s t : State α}
    (h : AgreeAway r x s t) (e : Event α) :
    AgreeAway r x (update s e) (update t e) := by
  intro p hp
  have hh := h p hp
  rcases e with ⟨et, er, eo⟩
  cases eo <;> simp only [update, Finset.mem_insert, Finset.mem_filter] <;> tauto

theorem agree_fold {r : Nat} {x : α} {s t : State α}
    (h : AgreeAway r x s t) (es : List (Event α)) :
    AgreeAway r x (applySeq (D α).toUpdateSig s es)
      (applySeq (D α).toUpdateSig t es) := by
  induction es generalizing s t with
  | nil => exact h
  | cons e es ih => exact ih (agree_update h e)

theorem initial_agree (s : State α) (ta ra tb rb : Nat) (x : α) :
    AgreeAway rb x (update (update s (tb,rb,.add x)) (ta,ra,.remove x))
      (update (update s (ta,ra,.remove x)) (tb,rb,.add x)) := by
  intro p hp
  rcases p with ⟨r,t,y⟩
  simp only [update, Finset.mem_insert, Finset.mem_filter, Prod.mk.injEq]
  simp only at hp
  grind

theorem finish_remove {r : Nat} {x : α} {s t : State α}
    (h : AgreeAway r x s t) (tc rc : Nat) :
    update s (tc,rc,.remove x) = update t (tc,rc,.remove x) := by
  ext p
  by_cases hp : p.2.2 = x
  · simp [update, hp]
  · have hh := h p (by tauto)
    simp only [update, Finset.mem_filter]
    tauto

theorem finish_add {r : Nat} {x : α} {s t : State α}
    (h : AgreeAway r x s t) (tc : Nat) :
    update s (tc,r,.add x) = update t (tc,r,.add x) := by
  ext p
  by_cases hp : p.1 = r ∧ p.2.2 = x
  · simp [update, hp.1, hp.2]
  · have hh := h p hp
    simp only [update, Finset.mem_insert, Finset.mem_filter]
    tauto

theorem conditional (s : State α) (a b c : Event α) (between : List (Event α))
    (hab : (EventSpec.conflict α).before a.op b.op)
    (hn : ¬ (D α).toUpdateSig.commutes b c) :
    update (applySeq (D α).toUpdateSig (update (update s b) a) between) c =
      update (applySeq (D α).toUpdateSig (update (update s a) b) between) c := by
  obtain ⟨x, ha, hb⟩ := hab
  have he := EventSpec.noncomm_same_element b c hn
  rcases a with ⟨ta,ra,ao⟩
  rcases b with ⟨tb,rb,bo⟩
  rcases c with ⟨tc,rc,co⟩
  change ao = .remove x at ha
  change bo = .add x at hb
  subst ao
  subst bo
  have hh := agree_fold (initial_agree s ta ra tb rb x) between
  cases co with
  | remove y =>
    change x = y at he
    subst y
    exact finish_remove hh tc rc
  | add y =>
    change x = y at he
    subst y
    have hr : rb = rc := by
      by_contra hne
      exact hn (NeemScope.adds_commute_of_replica_ne tb rb tc rc x x hne)
    subst rc
    exact finish_add hh tc

def laws : GuardedReplay.Laws (D α).toUpdateSig (EventSpec.conflict α) where
  noncomm_exact a b _ ne := NeemScope.guarded_noncomm_exact a b ne
  no_chain a b c _ _ := EventSpec.no_chain a.op b.op c.op
  conditional_commutation s a b c between _ _ _ := conditional s a b c between

/-- PASS+FAIL: the raw absorber is a same-replica add, which the payload
policy does not classify as a conflict. The swapped prefixes really differ. -/
example :
    update (applySeq (D Nat).toUpdateSig
      (update (update ∅ (2,0,.add 7)) (1,1,.remove 7))
      [(3,1,.add 7), (4,2,.add 9)]) (5,0,.add 7) =
    update (applySeq (D Nat).toUpdateSig
      (update (update ∅ (1,1,.remove 7)) (2,0,.add 7))
      [(3,1,.add 7), (4,2,.add 9)]) (5,0,.add 7) ∧
    update (update (∅ : State Nat) (2,0,.add 7)) (1,1,.remove 7) ≠
      update (update ∅ (1,1,.remove 7)) (2,0,.add 7) ∧
    ¬ (EventSpec.conflict Nat).before (SetOp.add 7) (SetOp.add 7) := by
  refine ⟨?_, ?_, ?_⟩
  · exact conditional ∅ (1,1,.remove 7) (2,0,.add 7) (5,0,.add 7)
      [(3,1,.add 7), (4,2,.add 9)] ⟨7,rfl,rfl⟩ (by
        intro hc
        have bad := hc (∅ : State Nat)
        change update (update ∅ (2,0,.add 7)) (5,0,.add 7) =
          update (update ∅ (5,0,.add 7)) (2,0,.add 7) at bad
        have hm : (0,2,7) ∈ update (update (∅ : State Nat) (5,0,.add 7))
            (2,0,.add 7) := by decide
        rw [← bad] at hm
        exact (by decide : (0,2,7) ∉ update
          (update (∅ : State Nat) (2,0,.add 7)) (5,0,.add 7)) hm)
  · decide
  · rintro ⟨x,h,_⟩
    cases h

#print axioms laws
#print axioms conditional

end Sal.MRDTs.Paper1.EfficientORSet.Guarded

namespace Sal.MRDTs.Paper1.ORSet.Guarded
open Foundation
variable {α : Type} [DecidableEq α]
def laws : GuardedReplay.Laws (D α).toUpdateSig (conflict α) :=
  GuardedReplay.ofUniform restrictedLaws
end Sal.MRDTs.Paper1.ORSet.Guarded
