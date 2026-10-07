import Sal.MRDTs.Paper1.NeemScope
import Sal.MRDTs.Paper1.GuardedReplay

/-! Concrete PASS+FAIL controls for the replica guard and semantic paper order.
The expected tags are hand-derived: each add replaces this replica's old tag. -/
namespace Sal.MRDTs.Paper1.EfficientORSet.GuardedPolicyControls
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
open Classical

abbrev older : Event Nat := (1, 0, .add 7)
abbrev newer : Event Nat := (2, 0, .add 7)
abbrev remote : Event Nat := (2, 1, .add 7)
abbrev events : Set (Event Nat) := {older, newer}
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
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all [older, newer]
  vis_total_same_replica := by
    intro a b r s r' s' hs ha hs' hb ne _
    cases Option.some.inj hs
    cases Option.some.inj hs'
    change a = older ∨ a = newer at ha
    change b = older ∨ b = newer at hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp_all [visibility, older, newer]

theorem events_supported : events ⊆ context.events := by
  intro e he
  exact ⟨0, events, rfl, he⟩

/-- Cross-replica exactness applies; extending it to same-replica adds fails. -/
theorem guarded_exactness_control :
    (@distinctOps (D Nat).toUpdateSig older remote ∧ older.rep ≠ remote.rep ∧
      (¬ (D Nat).toUpdateSig.commutes older remote ↔
        (EventSpec.conflict Nat).before older.op remote.op ∨
        (EventSpec.conflict Nat).before remote.op older.op)) ∧
    (@distinctOps (D Nat).toUpdateSig older newer ∧ ¬ older.rep ≠ newer.rep ∧
      ¬ (¬ (D Nat).toUpdateSig.commutes older newer ↔
        (EventSpec.conflict Nat).before older.op newer.op ∨
        (EventSpec.conflict Nat).before newer.op older.op)) := by
  have same := EventSpec.same_replica_adds_noncomm (7 : Nat)
  have cross := NeemScope.guarded_noncomm_exact older remote (by decide)
  refine ⟨⟨by simp [distinctOps, Op.time], by decide, cross⟩,
    ⟨by simp [distinctOps, Op.time], by decide, ?_⟩⟩
  intro bad
  simpa [EventSpec.conflict, Op.op] using bad.mp same

/-- The two orders retain different tags. -/
theorem tag_control :
    update (update (∅ : State Nat) older) newer = {(0, 2, 7)} ∧
    update (update (∅ : State Nat) newer) older = {(0, 1, 7)} ∧
    update (update (∅ : State Nat) older) newer ≠
      update (update (∅ : State Nat) newer) older := by
  decide

/-- Actual causal noncommutation is retained even though add/add has no policy edge. -/
theorem paperOrder_control :
    paperOrder (EventSpec.conflict Nat) context events older newer ∧
    ¬ @loOn (D Nat).toUpdateSig (EventSpec.conflict Nat).lift context events older newer := by
  refine ⟨Or.inl ⟨⟨rfl, rfl⟩, EventSpec.same_replica_adds_noncomm 7⟩, ?_⟩
  simp [loOn, UpdateSig.rc, ReplayPolicy.Before, OperationPolicy.lift, EventSpec.conflict, Op.op]

end Sal.MRDTs.Paper1.EfficientORSet.GuardedPolicyControls
