import Sal.Interfaces.Map_Extended
import Sal.CRDTs.Peritext_with_tombstones.Peritext_CRDT
import Sal.CRDTs.Peritext_with_tombstones.Peritext_ReadSide

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 800000

open Classical

/-! # Peritext Test DSL

A scenario builder for writing Peritext SPOT tests in human-readable
form. Each `Scenario` wraps a `concrete_st` plus a position-indexed
character list, so callers refer to ranges by character sequence
rather than raw `OpId` literals.

```lean
let sc :=
  Scenario.empty
    |>.insertChars 0 ['T', 'h', 'e']    -- alice (rid = 0) types
    |>.bold        0 ['T', 'h', 'e']    -- alice bolds the word
```

The API uses `List Char` throughout (rather than `String`) so that
`simp +decide` reduces DSL-built scenarios down to the underlying
`do_` chain in a single step. All builder functions are `@[simp]`.

Conventions:
* `rid` is the originating replica id; distinct rids are the
  state-based stand-in for "concurrent from different replicas".
* `markType = 0` is bold by convention; ranges use closed-left,
  bold-expand-right (`startSide = false`, `endSide = true`).
* `findRange` returns the `(firstId, lastId)` of the first
  occurrence of the target character sequence. -/

namespace Peritext_DSL

structure Scenario where
  state : concrete_st
  /-- `(opId, char)` for each inserted character, in insertion order. -/
  positions : List (OpId × Char)
  /-- Next available timestamp; globally unique across all ops. -/
  next_ts : Nat

@[simp]
noncomputable def Scenario.empty : Scenario := ⟨init_st, [], 1⟩

/-- The OpId of the most recently inserted char, or sentinel `(0, 0)`. -/
@[simp]
def lastOpId : List (OpId × Char) → OpId
  | [] => (0, 0)
  | [(oid, _)] => oid
  | _ :: rest => lastOpId rest

/-- Insert one character from replica `rid`, chained from the
last existing position. -/
@[simp]
noncomputable def Scenario.insertChar (sc : Scenario) (rid : Nat) (c : Char) :
    Scenario :=
  let after := lastOpId sc.positions
  let opId : OpId := (sc.next_ts, rid)
  let op : op_t := (sc.next_ts, rid, app_op_t.Insert c.toNat after)
  { state := do_ sc.state op
    positions := sc.positions ++ [(opId, c)]
    next_ts := sc.next_ts + 1 }

/-- Insert a list of characters sequentially from replica `rid`. -/
@[simp]
noncomputable def Scenario.insertChars (sc : Scenario) (rid : Nat)
    (cs : List Char) : Scenario :=
  cs.foldl (fun acc c => acc.insertChar rid c) sc

/-- Insert a single character with an explicit `afterId`. Use this
for sibling inserts (multiple chars sharing a common parent), where
`insertChar` (which always chains from the previous-last) doesn't
fit. Pass `(0, 0)` to insert as a child of the sentinel root. -/
@[simp]
noncomputable def Scenario.insertCharAfter (sc : Scenario) (rid : Nat)
    (afterId : OpId) (c : Char) : Scenario :=
  let opId : OpId := (sc.next_ts, rid)
  let op : op_t := (sc.next_ts, rid, app_op_t.Insert c.toNat afterId)
  { state := do_ sc.state op
    positions := sc.positions ++ [(opId, c)]
    next_ts := sc.next_ts + 1 }

/-- Does `chars` start with `target`? -/
@[simp]
def matchPrefix : List Char → List Char → Bool
  | _, [] => true
  | [], _ :: _ => false
  | c :: cs, t :: ts => decide (c = t) && matchPrefix cs ts

/-- The OpId of the n-th inserted char if it exists, else `(0, 0)`. -/
@[simp]
def nthOpId : List (OpId × Char) → Nat → OpId
  | [], _ => (0, 0)
  | (oid, _) :: _, 0 => oid
  | _ :: rest, n + 1 => nthOpId rest n

/-- Find first occurrence of `target` in `positions`. Returns
(firstOpId, lastOpId) of the matched run, or `none`. -/
@[simp]
def findRangeAux : List (OpId × Char) → List Char → Option (OpId × OpId)
  | _, [] => none
  | [], _ :: _ => none
  | (oid, c) :: rest, t :: ts =>
    if matchPrefix (c :: rest.map Prod.snd) (t :: ts) then
      let len := ts.length
      some (oid, nthOpId ((oid, c) :: rest) len)
    else findRangeAux rest (t :: ts)

/-- Find first occurrence of `target` (as a `List Char`) in
`sc.positions`. -/
@[simp]
def Scenario.findRange (sc : Scenario) (target : List Char) :
    Option (OpId × OpId) :=
  findRangeAux sc.positions target

/-- Apply an `AddMark` for `target` from replica `rid` (closed-left,
bold-expand-right). No-op if `target` not found. -/
@[simp]
noncomputable def Scenario.addMark (sc : Scenario) (rid markType : Nat)
    (target : List Char) : Scenario :=
  match sc.findRange target with
  | none => sc
  | some (startId, endId) =>
    let op : op_t :=
      (sc.next_ts, rid, app_op_t.AddMark startId false endId true markType)
    { state := do_ sc.state op
      positions := sc.positions
      next_ts := sc.next_ts + 1 }

@[simp]
noncomputable def Scenario.removeMark (sc : Scenario) (rid markType : Nat)
    (target : List Char) : Scenario :=
  match sc.findRange target with
  | none => sc
  | some (startId, endId) =>
    let op : op_t :=
      (sc.next_ts, rid, app_op_t.RemoveMark startId false endId true markType)
    { state := do_ sc.state op
      positions := sc.positions
      next_ts := sc.next_ts + 1 }

@[simp]
noncomputable def Scenario.bold (sc : Scenario) (rid : Nat) (target : List Char) :
    Scenario := sc.addMark rid 0 target

@[simp]
noncomputable def Scenario.unbold (sc : Scenario) (rid : Nat) (target : List Char) :
    Scenario := sc.removeMark rid 0 target

/-- Tombstone the character at the OpId looked up by 0-based position. -/
@[simp]
noncomputable def Scenario.removeAt (sc : Scenario) (rid pos : Nat) : Scenario :=
  let target := nthOpId sc.positions pos
  let op : op_t := (sc.next_ts, rid, app_op_t.Remove target)
  { state := do_ sc.state op
    positions := sc.positions
    next_ts := sc.next_ts + 1 }

/-! ## Anchor positions and named mark constructors

A mark boundary lies *between* two characters: relative to its
anchor OpId, it can sit either `before` that character or `after`
it. The paper's "boundary anchor" diagrams come down to this binary
choice, but the boundary's *meaning* depends on which end of the
mark it sits on:

* On the **left** boundary: anchor `before startId` ⇒ closed-left
  (the mark covers `startId`); anchor `after startId` ⇒ open-left
  (the mark excludes `startId`).
* On the **right** boundary: anchor `before endId` ⇒ contract-right
  (the mark excludes `endId` and stays put under concurrent inserts —
  link / comment behaviour); anchor `after endId` ⇒ expand-right
  (the mark covers `endId` *and* grows to include concurrent post-
  `endId` inserts — bold / italic behaviour).

The underlying `MarkOp` tuple stores these as booleans (`Anchor.toBool`:
`before ↦ false`, `after ↦ true`) for compatibility with existing
read-side theorems; user-facing constructors take `Anchor` directly. -/

inductive Anchor where
  | before
  | after
deriving DecidableEq, Repr

@[simp] def Anchor.toBool : Anchor → Bool
  | .before => false
  | .after => true

namespace Mark

/-- Generic mark constructor.

`opId` is the mark op's own OpId (used for LWW tie-breaking).
`startId` / `endId` are the OpIds of the first and last characters
the mark anchors to. `startSide` / `endSide` are the boundary
positions (see `Anchor`). `markType` tags the formatting kind
(0 = bold, 1 = italic/link, …). `isAdd` is `true` for an AddMark
op and `false` for a RemoveMark op. -/
@[simp] noncomputable def mk
    (opId startId endId : OpId) (startSide endSide : Anchor)
    (markType : Nat) (isAdd : Bool) : MarkOp :=
  (opId, startId, startSide.toBool, endId, endSide.toBool, markType, isAdd)

/-- A bold mark (markType 0) covering `[startId, endId]`, closed-left,
expand-right. -/
@[simp] noncomputable def bold (opId startId endId : OpId) : MarkOp :=
  mk opId startId endId .before .after 0 true

/-- A non-bold mark — paper's RemoveMark of bold, same boundary
shape as `bold`. -/
@[simp] noncomputable def unbold (opId startId endId : OpId) : MarkOp :=
  mk opId startId endId .before .after 0 false

/-- An italic mark (markType 1), closed-left, expand-right. -/
@[simp] noncomputable def italic (opId startId endId : OpId) : MarkOp :=
  mk opId startId endId .before .after 1 true

/-- A link mark (markType 1), closed-left, **contract-right**. The
end boundary sits `before` `endId`, so concurrent inserts at the
end are excluded — matching the paper's link / comment behaviour. -/
@[simp] noncomputable def link (opId startId endId : OpId) : MarkOp :=
  mk opId startId endId .before .before 1 true

end Mark

/-! ## Scenario-level read-side queries

These wrap the underlying read-side projections in DSL-flavoured
form so SPOT assertions can be written in scenario terms. -/

/-- The OpId of the character at 0-based position `pos`. -/
@[simp]
def Scenario.opIdAt (sc : Scenario) (pos : Nat) : OpId :=
  nthOpId sc.positions pos

/-- Is the character at position `pos` formatted with `markType = mt`? -/
@[simp]
noncomputable def Scenario.formattedAt (sc : Scenario) (pos mt : Nat) : Bool :=
  formatted_visible sc.state (sc.opIdAt pos) mt

/-- Convenience: is the character at position `pos` bold (markType 0)? -/
@[simp]
noncomputable def Scenario.boldAt (sc : Scenario) (pos : Nat) : Bool :=
  sc.formattedAt pos 0

/-- Is the character at position `pos` visible (inserted, not tombstoned)? -/
@[simp]
noncomputable def Scenario.visibleAt (sc : Scenario) (pos : Nat) : Bool :=
  visible sc.state (sc.opIdAt pos)

/-! ## Chain-reach helper for SPOTs over chained scenarios

For a state `s` in which consecutive opIds `(k, 0)` and `(k+1, 0)`
are chained (the `(k+1)`-th `Insert` op had `afterId = (k, 0)`),
`chain_reach` builds `afters_reach s (j, 0) (i, 0)` from the
consecutive `after_of` facts. SPOTs typically discharge the
`h_after` premise via `intro k h1 h2; interval_cases k <;> simp +decide`. -/

theorem chain_reach (s : concrete_st) (i j : Nat) (h_i_le_j : i ≤ j)
    (h_after : ∀ k, i ≤ k → k < j → after_of s (k + 1, 0) (k, 0) = true) :
    afters_reach s (j, 0) (i, 0) := by
  induction j with
  | zero =>
    have : i = 0 := Nat.le_zero.mp h_i_le_j
    subst this
    exact afters_reach.refl _
  | succ k ih =>
    by_cases h_eq : i = k + 1
    · subst h_eq; exact afters_reach.refl _
    · have h_i_le_k : i ≤ k := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne h_i_le_j h_eq)
      exact afters_reach.step
        (h_after k h_i_le_k (Nat.lt_succ_self k))
        (ih h_i_le_k (fun n h1 h2 => h_after n h1 (Nat.lt_succ_of_lt h2)))

/-- `afters_reach` implies `visible_lt` (Peritext analogue of the
RGA `causal_order_visible_lt` theorem). -/
theorem afters_reach_to_visible_lt (s : concrete_st) (c anc : OpId) :
    afters_reach s c anc → c ≠ anc → visible_lt s anc c := by
  intro h_reach h_ne
  induction h_reach with
  | refl c => exact absurd rfl h_ne
  | @step c mid anc h_after _ ih =>
    by_cases h_eq : mid = anc
    · subst h_eq
      exact visible_lt.parent_child h_after
    · exact visible_lt.trans (ih h_eq) (visible_lt.parent_child h_after)

end Peritext_DSL
