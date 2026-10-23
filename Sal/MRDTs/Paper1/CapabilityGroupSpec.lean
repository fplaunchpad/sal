import Sal.MRDTs.Instances.CapabilityGroup
import Sal.MRDTs.Paper1.HistorySpec

/-! An independent ordinary ACL and observed-overwrite name specification.
The machine stores granted permissions, revoked grant IDs, and live name
entries. It never invokes the source authorization or DAG query functions.
An assignment explicitly supplies the entry IDs it intends to overwrite;
this avoids the unrelated single-value-register obstruction. Revocation
prevents future assignments and preserves assignments already accepted.
-/
namespace Sal.MRDTs.Paper1.CapabilityGroupSpec
open Sal.MRDTs.Instances.CapabilityGroup

structure Input where
  id : Id
  actor : Actor
  action : Action
  observed : Finset Id
  deriving DecidableEq

structure Store where
  grants : Finset (Id × Actor) := ∅
  revoked : Finset Id := ∅
  entries : Finset (Id × Name) := ∅
  deriving DecidableEq

def project (e : Event) : Input := ⟨e.id, e.actor, e.action, e.past⟩

def update (owner : Actor) (s : Store) (u : Input) : Store :=
  match u.action with
  | .grant user =>
      if u.actor = owner then { s with grants := insert (u.id, user) s.grants } else s
  | .revoke gid =>
      if u.actor = owner ∧ ∃ p ∈ s.grants, p.1 = gid then
        { s with revoked := insert gid s.revoked } else s
  | .assign gid name =>
      if (gid, u.actor) ∈ s.grants ∧ gid ∉ s.revoked then
        { s with entries := (insert (u.id, name)
          (s.entries.filter (fun p => p.1 ∉ u.observed))) } else s

def names (s : Store) : Finset Name := s.entries.image Prod.snd

def machine (owner : Actor) : DeterministicSpec Input Unit (Finset Name) where
  State := Store
  initial := {}
  update := update owner
  query s _ := names s

def spec (owner : Actor) := (machine owner).toSpec

def run (owner : Actor) (inputs : List Input) : Store :=
  inputs.foldl (update owner) {}

theorem accepts_iff (owner : Actor) (inputs : List Input) (answer : Finset Name) :
    (spec owner).admits (inputs.map SeqLabel.update ++ [.query () answer]) ↔
      answer = names (run owner inputs) :=
  (machine owner).updates_query_iff inputs () answer

/-- This ordinary sequential choice is explicit: revocation does not retract
already accepted names. -/
theorem revoke_preserves_names (owner : Actor) (s : Store) (u : Input)
    (gid : Id) (h : u.action = .revoke gid) :
    names (update owner s u) = names s := by
  simp only [update, h]
  split <;> rfl

/-- The owner alone can modify the capability tables. -/
theorem outsider_grant_noop (owner : Actor) (s : Store) (u : Input)
    (user : Actor) (h : u.action = .grant user) (ho : u.actor ≠ owner) :
    update owner s u = s := by simp [update, h, ho]

end Sal.MRDTs.Paper1.CapabilityGroupSpec
