import Sal.MRDTs.Paper1.MetadataDependencies

/-! An abstract-maximal event need not be safe for metadata reconstruction.
Two same-replica adds commute observationally, so either is abstract maximal.
Reappending the older one after the newer one restores an obsolete tag. -/
namespace Sal.MRDTs.Paper1.EfficientORSet.MetadataPeelControl
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
open Classical

abbrev older : Event Nat := (1,0,.add 7)
abbrev newer : Event Nat := (2,0,.add 7)
abbrev events : Set (Event Nat) := {older,newer}
abbrev latest : State Nat := {(0,2,7)}
abbrev previous : State Nat := {(0,1,7)}
def visibility (a b : Event Nat) : Prop := a = older ∧ b = newer

def context : ReplayContext (D Nat).toUpdateSig where
  L _ := some events
  vis := visibility
  timestamps_distinct := by
    intro a b r s r' s' hs ha hs' hb ne
    cases Option.some.inj hs
    cases Option.some.inj hs'
    change a = older ∨ a = newer at ha
    change b = older ∨ b = newer at hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all [older,newer]
  vis_total_same_replica := by
    intro a b r s r' s' hs ha hs' hb ne _
    cases Option.some.inj hs
    cases Option.some.inj hs'
    change a = older ∨ a = newer at ha
    change b = older ∨ b = newer at hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp_all [visibility,older,newer]

theorem older_abstract_maximal (C : ReplayContext (D Nat).toUpdateSig) :
    ∀ e ∈ events, e ≠ older →
      ¬ AbstractMRDT.order (AbstractSpec.model (α := Nat)) (EventSpec.conflict Nat) C events older e := by
  intro e he ne
  change e = older ∨ e = newer at he
  rcases he with h | rfl
  · exact False.elim (ne h)
  · unfold AbstractSpec.model
    rw [AbstractMRDT.ofQuery_order]
    have hc : QueryReplay.Commutes (D Nat) older newer := QuerySpec.adds_commute _ _ _ _ _ _
    simp [QueryReplay.order,EventSpec.conflict,Op.op,hc]

theorem latest_represents : Represents visibility events latest := by
  intro p
  rcases p with ⟨r,t,x⟩
  simp [Represents,live,dead,kills,visibility,events,older,newer,latest,Prod.mk.injEq]
  grind

theorem reappend_older_invalid : ¬ Represents visibility events (update latest older) := by
  intro h
  have mem : (0,1,7) ∈ update latest older := by simp [update]
  have alive := (h (0,1,7)).mp mem
  exact alive.2 ⟨newer,Or.inr rfl,⟨rfl,rfl⟩,⟨rfl,rfl⟩⟩

theorem same_observation : QueryReplay.Equivalent (D Nat) latest (update latest older) := by
  apply (QuerySpec.equivalent_iff_elements _ _).mpr
  change elements latest = elements (update latest older)
  rw [elements_update]
  simp [setStep,elements,older]

/-- Observable conflict closure omits the predecessor whose tag the newer
add must replace, even when the predecessor is visible. -/
theorem observable_dependency_missing (C : ReplayContext (D Nat).toUpdateSig) :
    ¬ visNC (AbstractMRDT.context (AbstractSpec.model (α := Nat)) C) older newer := by
  rintro ⟨_,conflict⟩
  apply conflict
  apply (AbstractMRDT.commutes_iff _ _ _).mpr
  apply (AbstractMRDT.ofQuery_commutes QuerySpec.abstraction _ _).mpr
  exact QuerySpec.adds_commute _ _ _ _ _ _

theorem observable_past_empty :
    AbstractMRDT.causalPast (AbstractSpec.model (α := Nat)) context newer \ {newer} = ∅ := by
  have noedge : ∀ a b, ¬ visNC (AbstractMRDT.context (AbstractSpec.model (α := Nat)) context) a b := by
    intro a b
    rintro ⟨vis,nc⟩
    change visibility a b at vis
    rcases vis with ⟨rfl,rfl⟩
    exact observable_dependency_missing context ⟨⟨rfl,rfl⟩,nc⟩
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx.1 with rfl | chain
    · exact False.elim (hx.2 rfl)
    · cases chain with
      | single edge => exact False.elim (noedge _ _ edge)
      | tail _ edge => exact False.elim (noedge _ _ edge)
  · exact Set.empty_subset _

theorem metadata_past_retains_older :
    older ∈ (AbstractMRDT.MetadataDependencies.ofConcrete
      (AbstractSpec.model (α := Nat)) context).Past newer :=
  Or.inr (.single ⟨⟨rfl,rfl⟩,EventSpec.same_replica_adds_noncomm 7⟩)

/-- Choosing the newer event fixes direct-update metadata, but a causal-delta
reconstruction with an empty observable past retains the obsolete tag. -/
theorem causal_reconstruction_invalid :
    ¬ Represents visibility events (merge ∅ previous (update ∅ newer)) := by
  intro h
  have mem : (0,1,7) ∈ merge ∅ previous (update ∅ newer) := by simp [merge]
  have alive := (h (0,1,7)).mp mem
  exact alive.2 ⟨newer,Or.inr rfl,⟨rfl,rfl⟩,⟨rfl,rfl⟩⟩

theorem causal_reconstruction_observable :
    QueryReplay.Equivalent (D Nat) (merge ∅ previous (update ∅ newer)) (update previous newer) := by
  apply (QuerySpec.equivalent_iff_elements _ _).mpr
  change elements (merge ∅ previous (update ∅ newer)) = elements (update previous newer)
  decide

/-- PASS+FAIL: the genuine tag/history representation is valid before the
rewrite, and future local observations agree, but metadata validity is lost. -/
theorem control (C : ReplayContext (D Nat).toUpdateSig) :
    (∀ e ∈ events, e ≠ older →
      ¬ AbstractMRDT.order (AbstractSpec.model (α := Nat)) (EventSpec.conflict Nat) C events older e) ∧
    Represents visibility events latest ∧
    QueryReplay.Equivalent (D Nat) latest (update latest older) ∧
    ¬ Represents visibility events (update latest older) :=
  ⟨older_abstract_maximal C,latest_represents,same_observation,reappend_older_invalid⟩

end Sal.MRDTs.Paper1.EfficientORSet.MetadataPeelControl
