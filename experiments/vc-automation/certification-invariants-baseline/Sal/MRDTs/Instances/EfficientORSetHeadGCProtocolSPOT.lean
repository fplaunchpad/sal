import Sal.MRDTs.Instances.EfficientORSetHeadGCProtocol
import Sal.MRDTs.Instances.EfficientORSetHeadGCSPOT

/-! # Non-vacuous protocol execution

Construct two retirements separated by independent updates and merges,
then remove the element and synchronize. The general trace theorem is applied
to the constructed execution. Events 3 and 4 are genuinely concurrent.
-/

namespace Sal.MRDTs.Instances.EfficientORSet.HeadGC.Protocol.SPOT
open Sal.MRDTs.Foundation
open Retirement

def causal (a b : Ev) : Prop := a.1 < b.1 ∧ ¬ (a.1 = 3 ∧ b.1 = 4)
instance (a b : Ev) : Decidable (causal a b) := inferInstanceAs (Decidable (_ ∧ _))

theorem causal_trans : Transitive causal := by
  intro a b c hab hbc
  refine ⟨Nat.lt_trans hab.1 hbc.1, ?_⟩
  rintro ⟨ha, hc⟩
  have h1 : 3 < b.1 := ha ▸ hab.1
  have h2 : b.1 < 4 := hc ▸ hbc.1
  exact (Nat.not_lt_of_ge (Nat.succ_le_of_lt h1)) h2

theorem causal_clock : ∀ a b, causal a b → a.1 < b.1 := fun _ _ h => h.1

instance (r x : Nat) (e : Ev) : Decidable (kills r x e) := by
  unfold kills
  split <;> infer_instance

def isAdd (e : Ev) : Bool := match e.2.2 with | .add _ => true | .remove _ => false

def recordOf (e : Ev) : Record Nat :=
  (e.2.1, e.1, match e.2.2 with | .add x => x | .remove x => x)

def candidates (E : Finset Ev) : State Nat :=
  (E.filter fun e => isAdd e = true).image recordOf

theorem mem_candidates (E : Finset Ev) (p : Record Nat) :
    p ∈ candidates E ↔ birth p ∈ E := by
  simp only [candidates, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨e, ⟨he, hadd⟩, hp⟩
    rcases e with ⟨t,r,op⟩
    cases op with
    | add x =>
        have heq : (r,t,x) = p := hp
        subst p
        exact he
    | remove x => simp [isAdd] at hadd
  · intro hp
    exact ⟨birth p, ⟨hp, rfl⟩, rfl⟩

def interpret (E : Finset Ev) : State Nat :=
  (candidates E).filter fun p => ∀ e ∈ E, ¬ (causal (birth p) e ∧ kills p.1 p.2.2 e)

theorem interpret_represents (E : Finset Ev) : Represents causal (↑E) (interpret E) := by
  intro p
  simp only [interpret, Finset.mem_filter, mem_candidates, live, dead,
    Finset.mem_coe, birth]
  simp only [not_exists, not_and]

def sem (h : Heads 2) : Semantic causal 2 := ⟨h, fun r => interpret (h r),
  fun r => interpret_represents (h r)⟩

def a : Ev := (1,0,.add 0)
def b : Ev := (2,1,.add 0)
def c : Ev := (3,0,.add 0)
def d : Ev := (4,1,.add 0)
def rem : Ev := (5,0,.remove 0)

def h0 : Heads 2 := fun _ => {a,b}
def h1 : Heads 2 := Function.update h0 0 (insert c (h0 0))
def h2 : Heads 2 := Function.update h1 1 (insert d (h1 1))
def h3 : Heads 2 := Function.update h2 0 (h2 0 ∪ h2 1)
def h4 : Heads 2 := Function.update h3 1 (h3 1 ∪ h3 0)
def h5 : Heads 2 := Function.update h4 0 (insert rem (h4 0))
def h6 : Heads 2 := Function.update h5 1 (h5 1 ∪ h5 0)

def w0 := initial (sem h0)
def w1 := collect w0 0 (1,2,0)
def w1b := collect w1 1 (1,2,0)
def w2 := applyHead w1b (sem h1) 0 c
def w3 := applyHead w2 (sem h2) 1 d
def l1 := interpret (h2 0 ∩ h2 1)
def w4 := mergeHeads w3 (sem h3) 0 1 l1
def l2 := interpret (h3 1 ∩ h3 0)
def w5 := mergeHeads w4 (sem h4) 1 0 l2
def w6 := collect w5 0 (1,4,0)
def w7 := applyHead w6 (sem h5) 0 rem
def l3 := interpret (h5 1 ∩ h5 0)
def w8 := mergeHeads w7 (sem h6) 1 0 l3

theorem first_collect : Step causal w0 w1 := by
  apply Step.collect 0 (0,1,0) (1,2,0) (by decide) rfl
  · intro j; fin_cases j <;> decide
  · intro j; fin_cases j <;> decide

theorem delayed_collect : Step causal w1 w1b := Step.collectKnown 1 (1,2,0) (by decide)

theorem first_add : Step causal w1b w2 := by
  apply Step.apply (sem h1) 0 c rfl
  · funext j; fin_cases j <;> decide
  · decide
  · have fresh : ∀ j : Fin 2, ∀ e ∈ h0 j, e.1 ≠ c.1 := by decide
    exact fun j p hp => (fresh j (birth p) hp).symm

theorem second_add : Step causal w2 w3 := by
  apply Step.apply (sem h2) 1 d rfl
  · funext j; fin_cases j <;> decide
  · decide
  · have fresh : ∀ j : Fin 2, ∀ e ∈ h1 j, e.1 ≠ d.1 := by decide
    exact fun j p hp => (fresh j (birth p) hp).symm

theorem first_merge : Step causal w3 w4 := by
  apply Step.merge (sem h3) 0 1 l1 rfl
  · funext j; fin_cases j <;> decide
  · exact interpret_represents _

theorem second_merge : Step causal w4 w5 := by
  apply Step.merge (sem h4) 1 0 l2 rfl
  · funext j; fin_cases j <;> decide
  · exact interpret_represents _

theorem second_collect : Step causal w5 w6 := by
  apply Step.collect 0 (0,3,0) (1,4,0) (by decide) rfl
  · intro j; fin_cases j <;> decide
  · intro j; fin_cases j <;> decide

theorem remove_step : Step causal w6 w7 := by
  apply Step.apply (sem h5) 0 rem rfl
  · funext j; fin_cases j <;> decide
  · decide
  · have fresh : ∀ j : Fin 2, ∀ e ∈ h4 j, e.1 ≠ rem.1 := by decide
    exact fun j p hp => (fresh j (birth p) hp).symm

theorem final_merge : Step causal w7 w8 := by
  apply Step.merge (sem h6) 1 0 l3 rfl
  · funext j; fin_cases j <;> decide
  · exact interpret_represents _

theorem execution : Steps causal w0 w8 :=
  (((((((((Steps.refl w0).tail first_collect).tail delayed_collect).tail first_add).tail second_add).tail
    first_merge).tail second_merge).tail second_collect).tail remove_step).tail final_merge

theorem two_retirements_query_correct (r : Fin 2) :
    elements (w8.compact r) = elements (w8.semantic.full r) :=
  repeated_gc_correct causal_trans causal_clock (sem h0) execution r

theorem actual_reclamation :
    (w0.compact 0).card = 2 ∧ (w1.compact 0).card = 1 ∧
    (w5.compact 0).card = 2 ∧ (w6.compact 0).card = 1 ∧
    w6.retired.card = 2 := by decide

theorem retained_element_before_remove : elements (w6.compact 0) = {0} := by decide
theorem observed_remove_after_two_gcs : w8.compact 0 = ∅ ∧ w8.compact 1 = ∅ := by decide
theorem concurrent_updates : ¬ causal c d ∧ ¬ causal d c := by decide

/-- Dropping the global-witness guard loses x. A remove concurrent with b
has already reached the other head; b itself is present at both heads. -/
theorem global_witness_guard_needed :
    let old : State Nat := {(0,1,0)}
    let both := update old b
    let other := merge old (update old (3,0,.remove 0)) both
    (1,2,0) ∈ both ∧ (1,2,0) ∈ other ∧ (0,1,0) ∉ other ∧
    elements (merge both both other) = {0} ∧
    elements (merge both (both.erase (1,2,0)) other) = ∅ := by decide

/-- Dropping the discarded-record global-presence guard loses a concurrent
addition. Both heads have a at collection time, but only one knows b. -/
theorem discarded_presence_guard_needed :
    let old : State Nat := {(0,1,0)}
    let both := update old b
    let other := update old (3,0,.remove 0)
    (1,2,0) ∉ old ∧
    elements (merge old both other) = {0} ∧
    elements (merge old (both.erase (1,2,0)) other) = ∅ := by decide

#print axioms execution
#print axioms two_retirements_query_correct
#print axioms actual_reclamation

end Sal.MRDTs.Instances.EfficientORSet.HeadGC.Protocol.SPOT
