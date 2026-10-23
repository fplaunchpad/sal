import Sal.MRDTs.Paper1.CapabilityGroupSpec
import Mathlib.Data.Finset.Union

/-! A source/ordinary-ACL guard correspondence for the honest owner-chain cut.
This file proves the general cut and guard facts, not existence of a Sal replay
or equality of a complete sequential run with the source MV name projection. -/
namespace Sal.MRDTs.Instances.CapabilityGroup.OwnerOrder
open Sal.MRDTs.Paper1

/-- Place an assignment after all administration that is not its causal successor.
This includes concurrent administration, enforcing revoke-wins at the cut. -/
abbrev AdminBeforeCut (owner : Actor) (e a : Event) : Prop :=
  a.actor = owner ∧ ¬ before e a

theorem before_trans {s : State} (hs : WellFormed s) {a b c : Event}
    (_ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hab : before a b) (hbc : before b c) : before a c :=
  hs.downward c hc b hb hbc hab

theorem before_asymm {s : State} (hs : WellFormed s) {a b : Event}
    (ha : a ∈ s) (hb : b ∈ s) (hab : before a b) : ¬ before b a := by
  intro hba
  exact (Nat.lt_asymm (hs.ranked b hb a.id hab) (hs.ranked a ha b.id hba))

/-- The proposed cut is a true initial segment of the owner chain: every owner
operation on its left causally precedes every owner operation on its right. -/
theorem cut_is_initial_segment {owner : Actor} {s : State}
    (hs : WellFormed s) (ho : OwnerOrdered owner s) {e a b : Event}
    (he : e ∈ s) (ha : a ∈ s) (hb : b ∈ s)
    (hleft : AdminBeforeCut owner e a) (howner : b.actor = owner)
    (hright : before e b) : before a b := by
  rcases ho a ha b hb hleft.1 howner with h | h | h
  · subst b; exact False.elim (hleft.2 hright)
  · exact h
  · exact False.elim (hleft.2 (before_trans hs he hb ha hright h))

/-- Causal owner precursors lie on the left of the cut. -/
theorem precursor_left_of_cut {owner : Actor} {s : State} (hs : WellFormed s)
    {e a : Event} (he : e ∈ s) (ha : a ∈ s) (hao : a.actor = owner)
    (hae : before a e) : AdminBeforeCut owner e a :=
  ⟨hao, before_asymm hs ha he hae⟩

def grantEntries (owner : Actor) (s : State) (e : Event) : Finset (Id × Actor) :=
  s.biUnion fun g => match g.action with
    | .grant user => if AdminBeforeCut owner e g then {(g.id, user)} else ∅
    | _ => ∅

def revokedIds (owner : Actor) (s : State) (e : Event) : Finset Id :=
  s.biUnion fun r => match r.action with
    | .revoke gid => if revokes owner s r gid ∧ ¬ before e r then {gid} else ∅
    | _ => ∅

/-- The ACL tables at the candidate cut. Entries are immaterial to the guard. -/
def cutStore (owner : Actor) (s : State) (e : Event) : CapabilityGroupSpec.Store :=
  { grants := grantEntries owner s e, revoked := revokedIds owner s e }

@[simp] theorem mem_revokedIds (owner : Actor) (s : State) (e : Event) (gid : Id) :
    gid ∈ revokedIds owner s e ↔
      ∃ r ∈ s, revokes owner s r gid ∧ ¬ before e r := by
  simp only [revokedIds, Finset.mem_biUnion]
  constructor
  · rintro ⟨r, hrs, hmem⟩
    cases ha : r.action with
    | grant user => simp [ha] at hmem
    | assign g n => simp [ha] at hmem
    | revoke g =>
      simp only [ha] at hmem
      split at hmem
      · have hg : gid = g := by simpa using hmem
        subst g
        exact ⟨r, hrs, by assumption⟩
      · simp at hmem
  · rintro ⟨r, hrs, hrev, hnot⟩
    refine ⟨r, hrs, ?_⟩
    simp only [hrev.2.1]
    rw [if_pos ⟨hrev, hnot⟩]
    exact Finset.mem_singleton_self _

theorem admitted_grant_at_cut {owner : Actor} {s : State} (hs : WellFormed s)
    {e : Event} (he : e ∈ s) {gid : Id} {n : Name}
    (ha : e.action = .assign gid n) (hadmit : admitted owner s e) :
    (gid, e.actor) ∈ grantEntries owner s e := by
  have hga : grantFor owner (pre s e) e gid := by
    have hh := hadmit
    simp only [admitted, authorized, ha] at hh
    exact hh.1
  obtain ⟨g, hg, hid, hbefore, howner, haction⟩ := hga
  have hgs : g ∈ s := ((mem_pre s e g).mp hg).1
  apply Finset.mem_biUnion.mpr
  refine ⟨g, hgs, ?_⟩
  simp only [haction]
  have hcut := precursor_left_of_cut hs he hgs howner hbefore
  rw [if_pos hcut]
  simp only [Finset.mem_singleton, hid]

/-- The source authorization predicate is exactly the ordinary sequential ACL
acceptance guard at this cut, for an admitted assignment in a valid history.
The theorem is general in the entire history and all assignments. OwnerOrdered
is needed to realize the cut as one admin-chain prefix (above), not for this
local guard equality itself. -/
theorem source_authorized_iff_cut_guard {owner : Actor} {s : State}
    (hs : WellFormed s) {e : Event} (he : e ∈ s) {gid : Id} {n : Name}
    (ha : e.action = .assign gid n) (hadmit : admitted owner s e) :
    authorized owner s e ↔
      (gid, e.actor) ∈ (cutStore owner s e).grants ∧
        gid ∉ (cutStore owner s e).revoked := by
  have hg := admitted_grant_at_cut hs he ha hadmit
  have hga : grantFor owner s e gid := by
    have hpre : grantFor owner (pre s e) e gid := by
      have hh := hadmit
      simp only [admitted, authorized, ha] at hh
      exact hh.1
    obtain ⟨g, hgm, hid, hb, ho, hact⟩ := hpre
    exact ⟨g, ((mem_pre s e g).mp hgm).1, hid, hb, ho, hact⟩
  simp only [authorized, ha, cutStore, mem_revokedIds]
  constructor
  · intro h
    refine ⟨hg, ?_⟩
    rintro ⟨r, hr, hrev, hnot⟩
    exact hnot (h.2 r hr hrev)
  · rintro ⟨_, h⟩
    refine ⟨hga, ?_⟩
    intro r hr hrev
    by_contra hn
    exact h ⟨r, hr, hrev, hn⟩

-- Hand-derived controls: the concurrent revoke belongs before the assignment
-- at its cut; a causal successor revoke belongs after it.
example : revokedIds 0
    {⟨1, 0, ∅, .grant 1⟩, ⟨2, 1, {1}, .assign 1 10⟩, ⟨3, 0, {1}, .revoke 1⟩}
    ⟨2, 1, {1}, .assign 1 10⟩ = {1} := by decide
example : revokedIds 0
    {⟨1, 0, ∅, .grant 1⟩, ⟨2, 1, {1}, .assign 1 10⟩, ⟨3, 0, {1}, .revoke 1⟩}
    ⟨2, 1, {1}, .assign 1 10⟩ ≠ ∅ := by decide
example : revokedIds 0
    {⟨1, 0, ∅, .grant 1⟩, ⟨2, 1, {1}, .assign 1 10⟩, ⟨3, 0, {1, 2}, .revoke 1⟩}
    ⟨2, 1, {1}, .assign 1 10⟩ = ∅ := by decide
example : revokedIds 0
    {⟨1, 0, ∅, .grant 1⟩, ⟨2, 1, {1}, .assign 1 10⟩, ⟨3, 0, {1, 2}, .revoke 1⟩}
    ⟨2, 1, {1}, .assign 1 10⟩ ≠ {1} := by decide

end Sal.MRDTs.Instances.CapabilityGroup.OwnerOrder
