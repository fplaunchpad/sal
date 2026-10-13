import Sal.MRDTs.Instances.EfficientORSet
import Plausible

/-! # Minimum-timestamp GC research

The naive mixed-materialization rule is refuted. A uniform erasure is an
algebraic repair for merge, but requires a protocol and a continuation
membership invariant before it constitutes a collecting certificate.
-/

namespace Sal.MRDTs.Instances.EfficientORSet.GCResearch
open Sal.MRDTs.Foundation

/-- Keep a timestamp-minimal record for each element. This candidate is used
only on the common state in these tests, where every record is present at
both replicas. It is not an implementation of distributed stability. -/
def keepMin (s : State Nat) : State Nat :=
  s.filter fun p => ∀ q ∈ s, q.2.2 = p.2.2 → p.2.1 ≤ q.2.1

def first (x t : Nat) : Op (SetOp Nat) := (t + 1, 0, .add x)
def second (x t gap : Nat) : Op (SetOp Nat) := (t + gap + 2, 1, .add x)
def removal (x t gap : Nat) : Op (SetOp Nat) := (t + gap + 3, 0, .remove x)

/-- Reachable common prefix: replica 0 adds, replica 1 observes it and adds,
then replica 0 synchronizes. Both heads now contain both records. -/
def common (x t gap : Nat) : State Nat :=
  update (update ∅ (first x t)) (second x t gap)

def fullResult (x t gap : Nat) : State Nat :=
  let s := common x t gap
  merge s (update s (removal x t gap)) s

/-- One replica collects its local materialization of the common version,
then removes x. Its merge-base lookup returns that compacted materialization;
the other replica supplies its uncollected head. -/
def mixedResult (x t gap : Nat) : State Nat :=
  let s := common x t gap
  let c := keepMin s
  merge c (update c (removal x t gap)) s

def originalBaseResult (x t gap : Nat) : State Nat :=
  let s := common x t gap
  merge s (update (keepMin s) (removal x t gap)) s

def uniformResult (x t gap : Nat) : State Nat :=
  let c := keepMin (common x t gap)
  merge c (update c (removal x t gap)) c

theorem timestamps_fresh_and_ordered (x t gap : Nat) :
    0 < (first x t).1 ∧
    (first x t).1 < (second x t gap).1 ∧
    (second x t gap).1 < (removal x t gap).1 := by
  change 0 < t + 1 ∧ t + 1 < t + gap + 2 ∧ t + gap + 2 < t + gap + 3
  omega

theorem collection_really_shrinks :
    common 7 0 0 = {(0,1,7), (1,2,7)} ∧
    keepMin (common 7 0 0) = {(0,1,7)} ∧
    (keepMin (common 7 0 0)).card < (common 7 0 0).card ∧
    elements (keepMin (common 7 0 0)) = elements (common 7 0 0) := by decide

/-- Observed-remove oracle: the removal sees both additions, so x is absent.
No concurrent addition exists in this trace. -/
theorem observed_remove_control : fullResult 7 0 0 = ∅ := by decide

theorem mixed_base_resurrects : mixedResult 7 0 0 = {(1,2,7)} := by decide

theorem naive_min_gc_refuted :
    ¬ (∀ x t gap, elements (mixedResult x t gap) = elements (fullResult x t gap)) := by
  intro h
  have bad := h 7 0 0
  have different : elements (mixedResult 7 0 0) ≠ elements (fullResult 7 0 0) := by decide
  exact different bad

theorem original_base_control : originalBaseResult 7 0 0 = ∅ := by decide
theorem uniform_translation_control : uniformResult 7 0 0 = ∅ := by decide

/-- A genuine concurrent addition must survive both representations. -/
theorem concurrent_add_control :
    let s := common 7 0 0
    let c := keepMin s
    let rem := removal 7 0 0
    let add : Op (SetOp Nat) := (4, 1, .add 7)
    elements (merge s (update s rem) (update s add)) = {7} ∧
    elements (merge c (update c rem) (update c add)) = {7} := by decide

/-- Fixed erasure commutes with merge when ALL THREE operands use it.
This is an algebraic lemma, not a distributed GC certificate. -/
theorem erase_merge (d : Record Nat) (l a b : State Nat) :
    (merge l a b).erase d = merge (l.erase d) (a.erase d) (b.erase d) := by
  ext p
  simp only [merge, Finset.mem_erase, Finset.mem_union, Finset.mem_inter,
    Finset.mem_sdiff]
  tauto

/-- A fresh operation cannot re-mint the discarded record. Under that
condition, uniform erasure also commutes with updates. -/
theorem erase_update (d : Record Nat) (s : State Nat) (e : Op (SetOp Nat))
    (fresh : e.1 ≠ d.2.1) :
    (update s e).erase d = update (s.erase d) e := by
  rcases e with ⟨t, r, op⟩
  cases op with
  | add x =>
      have different : (r,t,x) ≠ d := by
        intro h
        exact fresh (congrArg (fun p : Record Nat => p.2.1) h)
      ext p
      simp only [update, Finset.mem_erase, Finset.mem_insert, Finset.mem_filter]
      constructor
      · rintro ⟨hne, hp | ⟨hp, hk⟩⟩
        · exact Or.inl hp
        · exact Or.inr ⟨⟨hne, hp⟩, hk⟩
      · rintro (hp | ⟨⟨hne, hp⟩, hk⟩)
        · exact ⟨hp ▸ different, Or.inl hp⟩
        · exact ⟨hne, Or.inr ⟨hp, hk⟩⟩
  | remove x =>
      ext p
      simp only [update, Finset.mem_erase, Finset.mem_filter]
      tauto

/-- Query preservation needs an actual surviving witness, in addition to
the algebraic update/merge equations. -/
theorem erase_elements (d a : Record Nat) (s : State Nat)
    (ha : a ∈ s) (different : a ≠ d) (same : a.2.2 = d.2.2) :
    elements (s.erase d) = elements s := by
  ext x
  simp only [elements, Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨p, ⟨_, hp⟩, hx⟩
    exact ⟨p, hp, hx⟩
  · rintro ⟨p, hp, hx⟩
    by_cases hd : p = d
    · subst p
      exact ⟨a, ⟨different, ha⟩, same.trans hx⟩
    · exact ⟨p, ⟨hd, hp⟩, hx⟩

open Plausible

/-- The falsification harness must reject the naive claim, never give up. -/
def expectRefutation (seed : Nat) : IO Unit := do
  let result ← Testable.checkIO
    (NamedBinder "x" (∀ x : Nat, NamedBinder "t" (∀ t : Nat,
      NamedBinder "gap" (∀ gap : Nat,
        decide (elements (mixedResult x t gap) = elements (fullResult x t gap)) = true))))
    { numInst := 500, maxSize := 30, randomSeed := some seed }
  match result with
  | .failure _ examples shrinks =>
      IO.println s!"Expected refutation, seed {seed}; shrinks {shrinks}; {examples}"
  | .gaveUp n => throw (IO.userError s!"GC campaign gave up: {n}")
  | .success _ => throw (IO.userError "Naive GC unexpectedly passed")

#eval expectRefutation 17
#eval expectRefutation 91

/-- Directed sampling varies element, initial clock, and clock gap. Every
case has two common records and a fresh observed remove; no implications
discard generated cases. These are controls for this trace family only. -/
def controls (x t gap : Nat) : Bool :=
  let s := common x t gap
  let c := keepMin s
  decide (elements c = {x}) && decide (c.card = 1) && decide (s.card = 2) &&
  decide (fullResult x t gap = ∅) &&
  decide (originalBaseResult x t gap = ∅) &&
  decide (uniformResult x t gap = ∅) &&
  decide (elements (mixedResult x t gap) = {x})

def checkControls (seed : Nat) : IO Unit := do
  match ← Testable.checkIO
    (NamedBinder "x" (∀ x : Nat, NamedBinder "t" (∀ t : Nat,
      NamedBinder "gap" (∀ gap : Nat, controls x t gap = true))))
    { numInst := 500, maxSize := 30, randomSeed := some seed } with
  | .success _ => IO.println s!"GC controls: 500 passed, seed {seed}, no gaveUp"
  | .gaveUp n => throw (IO.userError s!"GC controls gave up: {n}")
  | .failure _ examples shrinks =>
      throw (IO.userError s!"GC controls failed: {examples}; shrinks {shrinks}")

#eval checkControls 17
#eval checkControls 91

abbrev Observed := Op (SetOp Nat) × List Timestamp

structure Branch where
  full : State Nat
  compact : State Nat
  history : List Observed
  next : Nat

def initialBranch : Branch := {
  full := common 0 0 0
  compact := keepMin (common 0 0 0)
  history := [(first 0 0, []), (second 0 0 0, [1])]
  next := 3 }

def continueBranch (replica : Nat) : List Nat → Branch → Branch
  | [], b => b
  | n :: ns, b =>
      let op := if n % 2 = 0 then SetOp.remove (n / 2 % 3) else .add (n / 2 % 3)
      let e : Op (SetOp Nat) := (b.next, replica, op)
      continueBranch replica ns {
        full := update b.full e
        compact := update b.compact e
        history := b.history ++ [(e, b.history.map (fun p => p.1.1))]
        next := b.next + 1 }

/-- Independent observed-remove oracle. Replica-local replacement is absent
from this specification: membership is surviving additions minus removes
that observed them. -/
def observedElements (history : List Observed) : Finset Nat :=
  (history.filterMap fun p => match p.1.2.2 with
    | .remove _ => none
    | .add x => if history.any (fun q => match q.1.2.2 with
        | .add _ => false
        | .remove y => x == y && q.2.contains p.1.1)
      then none else some x).toFinset

/-- Both replicas enter one common collection epoch. Each then performs up
to six operations with unique timestamps and sequential replica histories.
Every merge operand uses the same fixed erasure. This tests one fork/join,
not arbitrary repeated epochs or asynchronous epoch admission. -/
def continuationCheck (ns : List Nat) : Bool :=
  let left := continueBranch 0 (ns.take 6) initialBranch
  let right := continueBranch 1 ((ns.drop 6).take 6)
    { initialBranch with next := left.next }
  let full := merge initialBranch.full left.full right.full
  let compact := merge initialBranch.compact left.compact right.compact
  let expected := observedElements (left.history ++ right.history.drop 2)
  decide (elements full = expected) && decide (elements compact = expected) &&
    decide (compact = full.erase (1,2,0))

def checkContinuations (seed : Nat) : IO Unit := do
  match ← Testable.checkIO
    (NamedBinder "ns" (∀ ns : List Nat, continuationCheck ns = true))
    { numInst := 500, maxSize := 30, randomSeed := some seed } with
  | .success _ => IO.println s!"Uniform-epoch continuations: 500 passed, seed {seed}, no gaveUp"
  | .gaveUp n => throw (IO.userError s!"Continuation campaign gave up: {n}")
  | .failure _ examples shrinks =>
      throw (IO.userError s!"Continuation failed: {examples}; shrinks {shrinks}")

#eval checkContinuations 17
#eval checkContinuations 91

theorem continuation_controls :
    continuationCheck [1,0,1,0,1,0,1,1,0,0,1,1] = true ∧
    continuationCheck [3,2,5,4,1,0,5,4,3,2,1,0] = true := by decide

set_option maxHeartbeats 2000000 in
theorem exhaustive_continuations :
    ((List.range 6).all fun a => (List.range 6).all fun b =>
      (List.range 6).all fun c => (List.range 6).all fun d =>
        continuationCheck [a,b,3,3,3,3,c,d]) = true := by decide

/-- Deterministic backstop: 512 cases, with no random or native-decide axiom. -/
theorem exhaustive_controls :
    ((List.range 8).all fun x => (List.range 8).all fun t =>
      (List.range 8).all fun gap => controls x t gap) = true := by decide

#print axioms naive_min_gc_refuted
#print axioms erase_merge
#print axioms erase_update
#print axioms erase_elements
#print axioms exhaustive_controls
#print axioms exhaustive_continuations

end Sal.MRDTs.Instances.EfficientORSet.GCResearch
