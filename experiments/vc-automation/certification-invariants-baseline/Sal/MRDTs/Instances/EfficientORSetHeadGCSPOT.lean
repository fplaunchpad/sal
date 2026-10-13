import Sal.MRDTs.Instances.EfficientORSetHeadGC
import Plausible

/-! # Repeated head-only collection campaign

Three replicas, fresh operations, exact uncollected causal-intersection
bases, and a guard requiring actual presence at every current compact head.
This executable model tests repeated schedules; it is not a StepV reachability
proof or an implementation of the distributed evidence producer.
-/

namespace Sal.MRDTs.Instances.EfficientORSet.HeadGC.Campaign
open Sal.MRDTs.Foundation
open GCResearch

abbrev Event := Op (SetOp Nat)

structure Entry where
  event : Event
  past : Finset Nat

structure Head where
  events : Finset Nat := {1,2}
  full : State Nat := common 0 0 0
  compact : State Nat := common 0 0 0
  deriving Inhabited

structure World where
  log : List Entry := [⟨first 0 0, ∅⟩, ⟨second 0 0 0, {1}⟩]
  heads : Array Head := #[{}, {}, {}]
  next : Nat := 3
  collections : Nat := 0
  merges : Nat := 0

/-- Reconstruct an uncollected state at an event set. A birth is removed by
an observed remove or a later observed add by the same replica. -/
def stateAt (log : List Entry) (events : Finset Nat) : State Nat :=
  (log.filterMap fun p => match p.event.2.2 with
    | .remove _ => none
    | .add x =>
        if p.event.1 ∈ events && !(log.any fun q =>
          q.event.1 ∈ events && p.event.1 ∈ q.past &&
          match q.event.2.2 with
          | .remove y => x == y
          | .add y => x == y && p.event.2.1 == q.event.2.1)
        then some (p.event.2.1, p.event.1, x) else none).toFinset

/-- Independent membership specification: additions are killed only by
observed removes. It does not model efficient-set replica-local replacement. -/
def expectedAt (log : List Entry) (events : Finset Nat) : Finset Nat :=
  (log.filterMap fun p => match p.event.2.2 with
    | .remove _ => none
    | .add x =>
        if p.event.1 ∈ events && !(log.any fun q =>
          q.event.1 ∈ events && p.event.1 ∈ q.past &&
          match q.event.2.2 with
          | .remove y => x == y
          | .add _ => false)
        then some x else none).toFinset

def commonRecords (w : World) : State Nat :=
  w.heads.foldl (fun s h => s ∩ h.compact) (w.heads[0]!).compact

/-- Stable-pair collection affects only the selected head. Historical
materializations are reconstructed exclusively from the unmodified log. -/
def collectHead (w : World) (r x : Nat) : World := Id.run do
  let eligible := (commonRecords w).filter (fun p => p.2.2 = x)
  let drop := eligible \ keepMin eligible
  let h := w.heads[r]!
  let c := h.compact \ drop
  return { w with
    heads := w.heads.set! r { h with compact := c }
    collections := w.collections + (if c = h.compact then 0 else 1) }

def step (w : World) (n : Nat) : World := Id.run do
  let kind := n % 4
  let r := n / 4 % 3
  let peer := n / 12 % 3
  let x := n / 36 % 2
  let h := w.heads[r]!
  if kind < 2 then
    let op := if kind = 0 then SetOp.remove x else .add x
    let e : Event := (w.next, r, op)
    return { w with
      log := w.log ++ [⟨e, h.events⟩]
      next := w.next + 1
      heads := w.heads.set! r {
        events := insert w.next h.events
        full := update h.full e
        compact := update h.compact e } }
  else if kind = 2 then
    let other := w.heads[peer]!
    let base := stateAt w.log (h.events ∩ other.events)
    return { w with
      merges := w.merges + 1
      heads := w.heads.set! r {
        events := h.events ∪ other.events
        full := merge base h.full other.full
        compact := merge base h.compact other.compact } }
  else
    return collectHead w r x

def valid (w : World) : Bool :=
  w.heads.toList.all fun h =>
    decide (h.full = stateAt w.log h.events) &&
    decide (elements h.full = expectedAt w.log h.events) &&
    decide (elements h.compact = expectedAt w.log h.events) &&
    decide (h.compact ⊆ h.full)

def checkFrom : World → List Nat → Bool
  | w, [] => valid w
  | w, n :: ns => valid w && checkFrom (step w n) ns

/-- Force one successful collection before sampling the continuation, so
the campaign cannot pass by never exercising the collector. -/
def check (ns : List Nat) : Bool := checkFrom (collectHead {} 0 0) (ns.take 40)

def run (ns : List Nat) : World := ns.foldl step {}

theorem initial_guard_nonvacuous :
    commonRecords {} = {(0,1,0), (1,2,0)} ∧
    (collectHead {} 0 0).collections = 1 ∧
    ((collectHead {} 0 0).heads[0]!).compact = {(0,1,0)} ∧
    ((collectHead {} 0 0).heads[1]!).compact = common 0 0 0 := by decide

/-- GC at replica 0, observed removal there, merge uncollected replica 1.
The base is the uncollected common state, exactly as in the user's correction. -/
theorem original_base_removal :
    let w := run [3,0,14]
    valid w = true ∧ (w.heads[0]!).compact = ∅ := by decide

theorem concurrent_add_survives :
    let w := run [3,0,5,14]
    valid w = true ∧ elements (w.heads[0]!).compact = {0} := by decide

/-- The retained minimum can be replaced by a fresh add; preserving the
original minimum forever is not a necessary invariant. -/
theorem retained_record_replaced :
    let w := run [3,1,14]
    valid w = true ∧ (w.heads[0]!).compact = {(0,3,0)} := by decide

/-- First coalesce, replace both replicas' local records, synchronize all
three, and collect a new globally present pair. -/
theorem repeated_collection_runs :
    let w := run [3,1,5,14,6,10,3]
    valid w = true ∧ w.collections = 2 := by decide

/-- Mutation control: dropping different representatives loses the element
even with the original base. The continuation checker must detect it. -/
def wrongRepresentatives : World := {
  heads := #[{ compact := {(0,1,0)} }, { compact := {(1,2,0)} }, {}] }

theorem wrong_representatives_detected :
    valid wrongRepresentatives = true ∧
    checkFrom wrongRepresentatives [14] = false := by decide

open Plausible

def negativeCampaign : IO Unit := do
  match ← Testable.checkIO
    (NamedBinder "ns" (∀ ns : List Nat,
      checkFrom wrongRepresentatives (14 :: ns.take 40) = true))
    {numInst := 500, maxSize := 80, randomSeed := some 17} with
  | .failure _ examples shrinks =>
      IO.println s!"Head-only mutation rejected: {examples}; shrinks={shrinks}"
  | _ => throw (IO.userError "Head-only mutation was not rejected")

#eval negativeCampaign

def campaign (seed : Nat) : IO Unit := do
  match ← Testable.checkIO (NamedBinder "ns" (∀ ns : List Nat, check ns = true))
    {numInst := 500, maxSize := 80, randomSeed := some seed} with
  | .success _ => IO.println s!"Head-only seed={seed}: 500 passed, no gaveUp; initial GC forced"
  | .gaveUp n => throw (IO.userError s!"Head-only gaveUp: {n}")
  | .failure _ examples shrinks =>
      throw (IO.userError s!"Head-only failure: {examples}; shrinks={shrinks}")

#eval campaign 17
#eval campaign 91
#eval campaign 2026

def alphabet : List Nat := [0,1,4,5,14,6,26,10,3,7]

set_option maxHeartbeats 2000000 in
theorem exhaustive_short_schedules :
    (alphabet.all fun a => alphabet.all fun b => alphabet.all fun c =>
      check [a,b,c]) = true := by decide

#print axioms original_base_removal
#print axioms repeated_collection_runs
#print axioms exhaustive_short_schedules

end Sal.MRDTs.Instances.EfficientORSet.HeadGC.Campaign
