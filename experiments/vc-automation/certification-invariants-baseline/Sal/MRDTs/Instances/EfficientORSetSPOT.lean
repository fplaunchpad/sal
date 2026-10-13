import Sal.MRDTs.Instances.EfficientORSet
import Plausible

namespace Sal.MRDTs.Instances.EfficientORSet.Campaign
open Sal.MRDTs.Foundation

abbrev Event := Op (SetOp Nat)
abbrev Observed := Event × List Timestamp

structure Branch where
  state : State Nat := ∅
  history : List Observed := []
  next : Nat := 1

def build (replica : Nat) : List Nat → Branch → Branch
  | [], b => b
  | n :: ns, b =>
    let op := if n % 3 = 0 then SetOp.remove (n % 5) else .add (n % 5)
    let e : Event := (b.next, replica, op)
    build replica ns {
      state := update b.state e
      history := b.history ++ [(e, b.history.map (fun p => p.1.1))]
      next := b.next + 1 }

def fork (ns : List Nat) : List Observed × State Nat :=
  let base := build 0 (ns.take 3) {}
  let left := build 1 ((ns.drop 3).take 3) base
  let right := build 2 ((ns.drop 6).take 3) { base with next := left.next }
  (left.history ++ right.history.drop base.history.length,
    merge base.state left.state right.state)

/-- Independent observed-remove specification: an addition survives exactly
when no remove of its element observed it. This does not use the efficient
representation, replacement update, or three-way merge. -/
def expected (history : List Observed) : Finset Nat :=
  (history.filterMap fun p => match p.1.2.2 with
    | .remove _ => none
    | .add x => if history.any (fun q =>
        match q.1.2.2 with
        | .add _ => false
        | .remove y => x == y && q.2.contains p.1.1)
      then none else some x).toFinset

def check (ns : List Nat) : Bool :=
  let (history, state) := fork ns
  decide (elements state = expected history) &&
    decide (∀ a ∈ state, ∀ b ∈ state,
      a.1 = b.1 → a.2.2 = b.2.2 → a = b)

/-- The hand-derived negative control must expose resurrection under union. -/
theorem union_control :
    elements (update ∅ SPOT.a ∪ update (update ∅ SPOT.a) SPOT.rem) ≠
      expected [(SPOT.a, []), (SPOT.rem, [1])] := by decide

theorem repeated_add_fork : check [1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by decide
theorem observed_and_concurrent_removes :
    check [1, 6, 1, 6, 1, 6, 1, 1, 6] = true := by decide

open Plausible
#eval Testable.check (∀ ns : List Nat, check ns = true)
  { numInst := 500, maxSize := 30, randomSeed := some 17 }
#eval Testable.check (∀ ns : List Nat, check ns = true)
  { numInst := 500, maxSize := 30, randomSeed := some 91 }

end Sal.MRDTs.Instances.EfficientORSet.Campaign
