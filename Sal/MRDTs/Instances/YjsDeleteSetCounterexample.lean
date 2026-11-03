import Mathlib.Data.List.Basic

/-! A restricted executable counterpart of one measured Yjs partial-delivery
execution.

Research question: does Yjs's delivery rule keep every displayed version of a
`Y.Text` causally closed? Yjs holds back an update only while a struct in it
lacks its clock predecessor or an origin; a delete set is applied as soon as
the ids it names exist. An update carrying only a delete set therefore never
waits for its causal predecessors.

Source: Yjs 13.6.31, measured in `experiments/yjs-oracle/results/campaign.json`,
regression Y-007 shape A. Client 1 issues three requests:

1. insert `a` bold: marker bold (1:0), `a` (1:1), marker clear (1:2);
2. insert `b` after `a`, plain: `b` (1:3), placed after the clear marker;
3. unbold `[0,2)`: no structs, and the delete set `{1:0, 1:2}`.

Replica 2 receives update 1, then update 3, and never update 2. Both markers
exist there, so both are deleted, and replica 2 shows `a` plain. The causally
closed versions of client 1's history show `a*`, `a* b` and `a b`; none shows
`a` plain without `b`. Under the sequential specification (characters with
marks, unbold over the interval from `a` to `b`) the version made of requests 1
and 3 has no admitted view, since `b` exists in no state built from them.

The rendering walk is the one of the marker counterexample module, restricted
to the `bold` key. This module is a semantic counterpart of the measured
execution: it fixes the item lists, the rendering and a model of the delivery
condition. It does not model Yjs's integration algorithm or prove source
correspondence.
-/
namespace Sal.MRDTs.Instances.YjsDeleteSetCounterexample

/-- An item identifier: client and clock. -/
abbrev ItemId := Nat × Nat

/-- A `Y.Text` item restricted to the `bold` key: a character, or a format
marker whose value is `some true` (bold) or `none` (clear). -/
inductive Entry where
  | char (ch : Char) (id : ItemId)
  | marker (value : Option Bool) (id : ItemId) (deleted : Bool)
  deriving DecidableEq

/-- The rendering walk, starting from a current value. -/
def renderFrom : Option Bool → List Entry → List (Char × Bool)
  | _, [] => []
  | cur, .char ch _ :: rest => (ch, cur == some true) :: renderFrom cur rest
  | cur, .marker _ _ true :: rest => renderFrom cur rest
  | _, .marker v _ false :: rest => renderFrom v rest

/-- Yjs's rendering of an item list: each character with its `bold` value. -/
def render (items : List Entry) : List (Char × Bool) := renderFrom none items

/-! ## The item lists -/

/-- After request 1: bold opener, `a`, clear closer. -/
def v1 : List Entry :=
  [.marker (some true) (1, 0) false, .char 'a' (1, 1), .marker none (1, 2) false]

/-- After requests 1 and 2: `b` follows the clear closer. -/
def v2 : List Entry :=
  [.marker (some true) (1, 0) false, .char 'a' (1, 1), .marker none (1, 2) false,
   .char 'b' (1, 3)]

/-- After requests 1, 2 and 3: both markers deleted. -/
def v3 : List Entry :=
  [.marker (some true) (1, 0) true, .char 'a' (1, 1), .marker none (1, 2) true,
   .char 'b' (1, 3)]

/-- Replica 2 after updates 1 and 3: both markers deleted, no `b`. -/
def gap : List Entry :=
  [.marker (some true) (1, 0) true, .char 'a' (1, 1), .marker none (1, 2) true]

/-! ## Renderings of the closed versions -/

/-- PASS+FAIL: request 1 shows `a` bold, not plain. -/
theorem v1_render :
    render v1 = [('a', true)] ∧ render v1 ≠ [('a', false)] := by decide

/-- PASS+FAIL: `b` lies after the closer, so it is plain while `a` stays bold. -/
theorem v2_render :
    render v2 = [('a', true), ('b', false)] ∧
    render v2 ≠ [('a', true), ('b', true)] := by decide

/-- PASS+FAIL: the unbold clears `a`; the rendering is not that of `v2`. -/
theorem v3_render :
    render v3 = [('a', false), ('b', false)] ∧
    render v3 ≠ [('a', true), ('b', false)] := by decide

/-! ## Replica 2's view -/

/-- Replica 2 shows `a` plain, which is the rendering of none of the closed
versions. -/
theorem gap_render :
    render gap = [('a', false)] ∧
    render gap ≠ render v1 ∧ render gap ≠ render v2 ∧ render gap ≠ render v3 := by
  decide

/-! ## Delivery condition -/

/-- An update: the ids of its structs, the dependencies of those structs
(clock predecessors and origins), and its delete set. -/
structure Update where
  structIds : List ItemId
  structDeps : List ItemId
  deleteSet : List ItemId
  deriving DecidableEq

/-- Update 1: three structs with no dependency outside the update; the first
is client 1's first clock and has no origin, and each later struct depends only
on the struct before it. -/
def update1 : Update :=
  { structIds := [(1, 0), (1, 1), (1, 2)], structDeps := [], deleteSet := [] }

/-- Update 2: `b` (1:3), whose clock predecessor is 1:2 and whose origin is
1:1. -/
def update2 : Update :=
  { structIds := [(1, 3)], structDeps := [(1, 2), (1, 1)], deleteSet := [] }

/-- Update 3: no structs, and the delete set naming both markers. -/
def update3 : Update :=
  { structIds := [], structDeps := [], deleteSet := [(1, 0), (1, 2)] }

/-- Yjs integrates an update's structs when every struct dependency is held;
an update without structs is vacuously integrable. -/
def applicable (held : List ItemId) (u : Update) : Bool :=
  u.structDeps.all (· ∈ held)

/-- A delete set takes effect when every id it names is held. -/
def deletable (held : List ItemId) (u : Update) : Bool :=
  u.deleteSet.all (· ∈ held)

/-- The ids replica 2 holds after update 1. -/
def heldAfter1 : List ItemId := update1.structIds

/-- PASS+FAIL: at replica 2, update 3 is integrated at once and its delete set
takes effect; update 2 would not be integrable at a replica holding nothing,
and update 3 would not delete anything at such a replica. -/
theorem delivery :
    applicable heldAfter1 update3 = true ∧
    deletable heldAfter1 update3 = true ∧
    applicable [] update2 = false ∧
    applicable [] update3 = true ∧
    deletable [] update3 = false ∧
    applicable heldAfter1 update2 = true := by decide

/-- PASS+FAIL: replica 2 does not hold `b`, whose insertion is the causal
predecessor of update 3. -/
theorem b_not_held :
    (1, 3) ∉ heldAfter1 ++ update3.structIds ∧
    (1, 1) ∈ heldAfter1 ++ update3.structIds := by decide

/-- Client 1's requests in issue order. -/
def issueOrder : List Nat := [1, 2, 3]

/-- A set of requests is down-closed under the issue order when each member's
predecessors in the issue order are members too. -/
def downClosed (s : List Nat) : Bool :=
  s.all fun i => (issueOrder.takeWhile (· ≠ i)).all (· ∈ s)

/-- PASS+FAIL: replica 2's integrated set `{1, 3}` is not down-closed, since
it lacks request 2; the three closed versions are down-closed. -/
theorem integrated_not_closed :
    downClosed [1, 3] = false ∧
    2 ∉ [1, 3] ∧
    downClosed [1] = true ∧ downClosed [1, 2] = true ∧ downClosed [1, 2, 3] = true ∧
    downClosed [3] = false := by decide

/-! ## Sequential specification -/

/-- The characters present in the specification state after applying the
insert requests among `reqs` (request 1 inserts `a`, request 2 inserts `b`). -/
def charsOf (reqs : List Nat) : List Char :=
  (if 1 ∈ reqs then ['a'] else []) ++ (if 2 ∈ reqs then ['b'] else [])

/-- The unbold over the interval from `a` to `b` is defined only when both
endpoints exist. -/
def unboldEnabled (chars : List Char) : Bool := 'a' ∈ chars && 'b' ∈ chars

/-- PASS+FAIL: in neither order of requests 1 and 3 is the unbold enabled
(before request 1 nothing exists; after it only `a` does), so the version made
of requests 1 and 3 has no admitted view. Once request 2 is included, the
unbold is enabled. -/
theorem no_admitted_view :
    unboldEnabled (charsOf []) = false ∧
    unboldEnabled (charsOf [1]) = false ∧
    unboldEnabled (charsOf [1, 2]) = true := by decide

/-! ## Control -/

/-- Replica 2 after update 2 finally arrives: `b` (1:3) placed after its
clock predecessor, the deleted closer 1:2. -/
def lateArrival : List Entry := gap ++ [.char 'b' (1, 3)]

/-- PASS+FAIL: once update 2 arrives it is integrable, and the view is the
closed version's (`a b`), neither the gap view nor the bold `a* b`. -/
theorem arrival_control :
    applicable (heldAfter1 ++ update3.structIds) update2 = true ∧
    render lateArrival = render v3 ∧
    render lateArrival = [('a', false), ('b', false)] ∧
    render lateArrival ≠ render gap ∧
    render lateArrival ≠ render v2 := by decide

#print axioms gap_render
#print axioms delivery
#print axioms integrated_not_closed
#print axioms no_admitted_view
#print axioms arrival_control
end Sal.MRDTs.Instances.YjsDeleteSetCounterexample
