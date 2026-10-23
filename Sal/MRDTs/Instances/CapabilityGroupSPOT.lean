import Sal.MRDTs.Instances.CapabilityGroup

/-! Literal expectations are hand-derived from Spec. 2: a grant precedes its
use, revoke wins concurrently, and later revokes preserve precursor uses.
Each block includes a FAIL companion excluding a nearby degenerate policy. -/
namespace Sal.MRDTs.Instances.CapabilityGroup.SPOT

abbrev g : Event := ⟨1, 0, ∅, .grant 1⟩
abbrev a : Event := ⟨2, 1, {1}, .assign 1 10⟩
abbrev r : Event := ⟨3, 0, {1}, .revoke 1⟩
abbrev rAfter : Event := ⟨3, 0, {1, 2}, .revoke 1⟩
abbrev late : Event := ⟨4, 1, {1, 3}, .assign 1 20⟩
abbrev fresh : Event := ⟨4, 0, {1, 3}, .grant 1⟩
abbrev again : Event := ⟨5, 1, {1, 3, 4}, .assign 4 20⟩
abbrev badGrant : Event := ⟨6, 2, {1, 2}, .grant 2⟩
abbrev badRevoke : Event := ⟨6, 2, {1, 2}, .revoke 1⟩
abbrev ungranted : Event := ⟨2, 2, {1}, .assign 1 99⟩
abbrev aNext : Event := ⟨4, 1, {1, 2}, .assign 1 20⟩
abbrev aConcurrent : Event := ⟨4, 1, {1}, .assign 1 20⟩

-- Grant and ordinary use: reject universal denial and wrong-principal borrowing.
example : names 0 {g, a} = {10} := by decide
example : names 0 {g, a} ≠ ∅ := by decide
example : names 0 {g, ungranted} = ∅ := by decide
example : ¬ authorized 0 {g, ungranted} ungranted := by decide
example : names 0 {g, ungranted} ≠ {99} := by decide

-- Concurrent revoke suppresses a stored, causally admitted assignment.
example : admitted 0 {g, a, r} a := by decide
example : ¬ authorized 0 {g, a, r} a := by decide
example : names 0 (merge {g} {g, a} {g, r}) = ∅ := by decide
example : names 0 (merge {g} {g, a} {g, r}) ≠ {10} := by decide
example : merge {g} {g, a} {g, r} ≠ ({g, a} : State) := by decide
example : merge {g} {g, a} {g, r} ≠ ({g, r} : State) := by decide

-- A causal-before-revoke use survives; global grant tombstones would erase it.
example : authorized 0 {g, a, rAfter} a := by decide
example : names 0 {g, a, rAfter} = {10} := by decide
example : names 0 {g, a, rAfter} ≠ ∅ := by decide
example : caps 0 {g, a, rAfter} = ∅ := by decide
example : caps 0 {g, a, rAfter} ≠ {1} := by decide

-- A post-revoke use is rejected; issuing a fresh grant ID restores permission.
example : ¬ admitted 0 {g, r} late := by decide
example : names 0 {g, r, late} = ∅ := by decide
example : names 0 {g, r, late} ≠ {20} := by decide
example : admitted 0 {g, r, fresh} again := by decide
example : names 0 {g, r, fresh, again} = {20} := by decide
example : names 0 {g, r, fresh, again} ≠ ∅ := by decide
example : caps 0 {g, r, fresh, again} = {4} := by decide
example : caps 0 {g, r, fresh, again} ≠ {1, 4} := by decide

-- Delayed delivery changes discursive belief without changing causal admission.
example : names 0 {g, a} = {10} ∧ names 0 (step {g, a} r) = ∅ := by decide
example : admitted 0 {g, a} a ∧ admitted 0 (step {g, a} r) a := by decide
example : ¬ (authorized 0 {g, a} a ↔ authorized 0 (step {g, a} r) a) := by decide

-- Unauthorized administration cannot influence the query or create permission.
example : names 0 (step {g, a} badGrant) = {10} := by decide
example : names 0 (step {g, a} badRevoke) = {10} := by decide
example : names 0 (step {g, a} badRevoke) ≠ ∅ := by decide
example : ¬ authorized 0 (step {g, a} badGrant) badGrant := by decide
example : ¬ authorized 0 (step {g, a} badRevoke) badRevoke := by decide

-- Maximal assignments implement an MV register, not the complete accepted log.
example : names 0 {g, a, aNext} = {20} := by decide
example : names 0 {g, a, aNext} ≠ {10, 20} := by decide
example : names 0 {g, a, aConcurrent} = {10, 20} := by decide
example : names 0 {g, a, aConcurrent} ≠ {20} := by decide

-- Histories used above are structurally valid, with ordered owner administration.
example : WellFormed {g, a, r} := by constructor <;> decide
example : WellFormed {g, a, rAfter} := by constructor <;> decide
example : WellFormed {g, r, fresh, again} := by constructor <;> decide
example : OwnerOrdered 0 {g, a, r} := by decide
example : OwnerOrdered 0 {g, r, fresh, again} := by decide
example : ¬ WellFormed ({⟨2, 1, {1}, .assign 1 10⟩} : State) := by
  intro h
  have hc := h.closed a (by decide) 1 (by decide)
  have hn : ¬ ∃ p ∈ ({a} : State), p.id = 1 := by decide
  exact hn hc

-- Local issuance observes its entire local history; delayed delivery is a
-- compatible union, not retroactive mutation of the event's precursor set.
example : CanIssue 0 ∅ g := by decide
example : CanIssue 0 {g} a := by decide
example : CanIssue 0 {g} r := by decide
example : LocallyAdmitted 0 {g, a, r} := by decide
example : FreshAt {g, r} late := by decide
example : ¬ CanIssue 0 {g, r} late := by decide
example : ¬ FreshAt {g, a} r := by decide
example : CanIssue 0 {g, r} fresh := by decide
example : CanIssue 0 {g, r, fresh} again := by decide
example : ¬ CanIssue 0 {g, a} badGrant := by decide

-- Ownership is insufficient for a revoke that never observed its target grant.
example : ¬ authorized 0 {g, a, ⟨3, 0, ∅, .revoke 1⟩}
    ⟨3, 0, ∅, .revoke 1⟩ := by decide
example : names 0 {g, a, ⟨3, 0, ∅, .revoke 1⟩} = {10} := by decide
example : names 0 {g, a, ⟨3, 0, ∅, .revoke 1⟩} ≠ ∅ := by decide

end Sal.MRDTs.Instances.CapabilityGroup.SPOT
