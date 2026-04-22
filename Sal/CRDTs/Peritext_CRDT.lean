
import Std.Tactic.BVDecide
import Sal.Interfaces.Set_Extended
import Sal.Interfaces.Map_Extended
import Sal.Tactic.Sal

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Classical

/-!
# Peritext — state-based CRDT for rich text (characters + formatting spans)

## What this is

A state-based port of the Peritext CRDT

  Geoffrey Litt, Sarah Gentle, Martin Kleppmann, Peter van Hardenberg.
  *Peritext: A CRDT for Rich-Text Collaboration.* CSCW 2022.
  <https://www.inkandswitch.com/peritext/static/cscw-publication.pdf>

Peritext is published as an **operation-based** CRDT built atop an RGA
sequence with "anchor"-attached formatting-span operations. The state-
based version encoded here uses the same per-replica snapshot shape as
[`RGA_CRDT.lean`](RGA_CRDT.lean) and extends it with one additional
grow-only component for the per-anchor sets of mark operations. The
24 RA-linearizability VCs verify state convergence; the rich-text
semantics (which characters are in which mark at read time) is a
read-side projection not captured by the VCs.

## Design

**Characters and tombstones (inherited from RGA):**

* `chars   : Map OpId ℕ`    — char codepoint of the Insert with that opId.
* `afters  : Map OpId OpId` — `afterId` predecessor of that Insert.
* `deleted : Map OpId Bool` — monotonic tombstone flag.

**Formatting spans (Peritext-specific):**

A Peritext formatting operation (an `AddMark` or `RemoveMark`) carries
a `start` anchor and an `end` anchor. Each anchor is an `(OpId, Side)`
pair where `Side` encodes whether the anchor attaches *before* or
*after* the referenced character. The paper's key innovation — that a
mark can "expand" or "contract" under concurrent inserts at its
boundary, depending on anchor side — lives entirely in this anchor
data.

We represent this in state by a single map:

* `marks : Map (OpId × Bool) (set MarkOp)`
       keyed by `(anchorCharId, side)`, holding the set of mark ops
       attached at that anchor point. `side = false` means "before",
       `side = true` means "after".

A single mark op (an `AddMark` or `RemoveMark`) is stored at *two*
keys in this map — at its start anchor and at its end anchor — so
its lookup from either boundary is direct.

**`MarkOp` payload.** Each mark op records:

    (opId, startId, startSide, endId, endSide, markType, isAdd)

where `opId = (ts, rid)` is the mark op's own identity (making
repeated "bold this range" ops by the same user at different times
*distinct* elements of the set, per the paper), `start*/end*` are
the two anchors, `markType : ℕ` tags the formatting kind (0 = bold,
1 = italic, etc., the specific numbering is an application
concern), and `isAdd : Bool` distinguishes `AddMark` from
`RemoveMark`.

**Merge.** Componentwise per-key join on all four components:

* `chars`, `afters`, `deleted`: same as RGA_CRDT (max, opid_max,
  boolean max).
* `marks`: per-key pointwise set union. Set union is commutative /
  associative / idempotent, so this component is a join-semilattice.

**`rc`.** `Either` for every pair. Every op is a per-key write to
map slots that either don't collide across distinct replicas (Insert's
opId is fresh via `distinct_ops`) or collide on an idempotent join
(Remove's `true` flip; Mark ops' set-union addition). `do_` composition
commutes at the state level for all op pairs.

## What the 24 VCs verify

Pure state convergence, as with `RGA_CRDT`. The rich-text semantics —
the character sequence with formatting applied, and specifically the
expand/contract behavior of marks under concurrent boundary edits —
is a read-side projection of the combined `(chars, afters, deleted,
marks)` state. A downstream `readRichText : concrete_st → …` function
(not in this file) would compute the rich-text document; a
corresponding convergence theorem

    eq s₁ s₂ → readRichText s₁ = readRichText s₂

follows by functional extensionality from the pointwise definition of
`eq` and the purity of `readRichText`.

Conspicuously *not* verified here: that the rich-text projection
actually implements the paper's expand/contract semantics correctly.
That is a per-mark, per-anchor argument over the anchor sides, and
would be its own formalization effort.

## Relationship to existing CRDTs

Extends `RGA_CRDT` by exactly one additional grow-only component
(`marks`). Verification effort is comparable — the 24 VCs split into
the same pattern buckets (`rc_non_comm` + `base_*` via rcases+simp+
grind+ring; `ind_*` and `lem_0op` via rcases+simp+grind; the rest via
`by sal`). The main extra work is the 4-way rcases on the op family
(`_ | _ | _ | _` instead of `_ | _`) because `app_op_t` now has
4 constructors.
-/

/-- Op identifier, as in RGA. -/
@[simp] abbrev OpId := ℕ × ℕ

/-- Lexicographic max on `OpId`. -/
@[simp, grind]
def opid_max (a b : OpId) : OpId :=
  if a.1 > b.1 then a
  else if b.1 > a.1 then b
  else if a.2 ≥ b.2 then a
  else b

/-- A mark operation payload.

  `(opId, startId, startSide, endId, endSide, markType, isAdd)`

  * `opId = (ts, rid)` is the mark op's own identity.
  * `startId / endId` are the anchor character opIds.
  * `startSide / endSide` are `false = before`, `true = after`.
  * `markType` tags the formatting kind (bold / italic / link / ...).
  * `isAdd` distinguishes `AddMark` (true) from `RemoveMark` (false).
-/
abbrev MarkOp :=
  OpId × OpId × Bool × OpId × Bool × ℕ × Bool

/-- An "anchor attachment": a single mark op attached at a specific
`(anchor_charId, anchor_side)` position. A single mark op typically
appears as two `AnchorAttachment`s in state — one for its start
anchor, one for its end anchor.

Flattening the paper's `Map anchor (Set MarkOp)` layout into a
single top-level `set AnchorAttachment` keeps the state as a
product of simple `map`s and `set`s (Sal's `a → Bool` predicate
type) — which the 24 VCs' automation handles natively — instead of
nesting a `set` inside a `map` value, which would defeat `grind`'s
pointwise reasoning (function-valued map entries need `funext`). -/
abbrev AnchorAttachment :=
  OpId × Bool × MarkOp
  -- (anchor_charId, anchor_side, markOp)

/-- State: `(chars, afters, deleted, marks)`.

First three are the RGA grow-only character components. The fourth
is a flat grow-only set of anchor attachments: each element says
"mark op M is attached at the `side` anchor of character with opId
`charId`". -/
@[simp] abbrev concrete_st :=
  map OpId ℕ ×
  map OpId OpId ×
  map OpId Bool ×
  set AnchorAttachment

/-- Zero-default lookup on `chars`. -/
@[simp]
def mysel_c (s : map OpId ℕ) (k : OpId) : ℕ :=
  if (contains s k) then (sel s k) else 0

/-- `(0, 0)`-default lookup on `afters`. -/
@[simp]
def mysel_a (s : map OpId OpId) (k : OpId) : OpId :=
  if (contains s k) then (sel s k) else (0, 0)

/-- `false`-default lookup on `deleted`. -/
@[simp]
def mysel_d (s : map OpId Bool) (k : OpId) : Bool :=
  if (contains s k) then (sel s k) else false

/-- Initial state: no chars, no afters, no tombstones, no marks. -/
@[simp]
noncomputable def init_st : concrete_st :=
  (const_on empty 0,
   const_on empty (0, 0),
   const_on empty false,
   empty)

/-- Pointwise state equality: three ∀-conjuncts over map keys, one
per map component, plus one ∀-conjunct over the flat marks set. -/
@[simp]
def eq (a b : concrete_st) :=
  (forall k, (contains (Prod.fst a) k = contains (Prod.fst b) k) ∧
             (mysel_c (Prod.fst a) k = mysel_c (Prod.fst b) k)) ∧
  (forall k, (contains (Prod.fst (Prod.snd a)) k = contains (Prod.fst (Prod.snd b)) k) ∧
             (mysel_a (Prod.fst (Prod.snd a)) k = mysel_a (Prod.fst (Prod.snd b)) k)) ∧
  (forall k, (contains (Prod.fst (Prod.snd (Prod.snd a))) k =
               contains (Prod.fst (Prod.snd (Prod.snd b))) k) ∧
             (mysel_d (Prod.fst (Prod.snd (Prod.snd a))) k =
               mysel_d (Prod.fst (Prod.snd (Prod.snd b))) k)) ∧
  (forall x, (Prod.snd (Prod.snd (Prod.snd a))) x = (Prod.snd (Prod.snd (Prod.snd b))) x)

/-- User-level operations. `Insert`/`Remove` are inherited from the
RGA substrate; `AddMark`/`RemoveMark` are Peritext-specific. -/
inductive app_op_t : Type where
| Insert (ch : ℕ) (after : OpId)
| Remove (target : OpId)
| AddMark (startId : OpId) (startSide : Bool) (endId : OpId) (endSide : Bool) (markType : ℕ)
| RemoveMark (startId : OpId) (startSide : Bool) (endId : OpId) (endSide : Bool) (markType : ℕ)

/-- `(timestamp, replica id, app operation)`. -/
abbrev op_t := ℕ × ℕ × app_op_t

/-- Two ops are "distinct" iff their timestamps differ. -/
@[simp]
def distinct_ops (op1 op2 : op_t) := Prod.fst op1 != Prod.fst op2

/-- Extract the replica id of an op. -/
@[simp]
def get_rid (o : op_t) :=
match o with
| (_, (rid, _)) => rid

/-- Effect function.

* `Insert ch after` at `(ts, rid)`: creates `chars`/`afters` entries
  at fresh opId `(ts, rid)`. Matches RGA.
* `Remove target`: flips `deleted[target] = true`. Matches RGA.
* `AddMark startId startSide endId endSide markType` at `(ts, rid)`:
  constructs a MarkOp with `isAdd = true` and inserts it into the
  `marks` set at BOTH anchor keys `(startId, startSide)` and
  `(endId, endSide)`.
* `RemoveMark …`: same as `AddMark` but with `isAdd = false`. The
  set addition is at the same two anchor points.

Every mark op is therefore stored at two keys; the mark op's own
`opId = (ts, rid)` appears as the first field of the MarkOp tuple so
that repeated issuances of "the same" mark by the same or different
replicas at distinct timestamps are distinct elements of the set. -/
@[simp]
noncomputable def do_ (s : concrete_st) (o : op_t) : concrete_st :=
match o with
| (ts, (rid, app_op_t.Insert ch after)) =>
    (upd (Prod.fst s) (ts, rid) ch,
     upd (Prod.fst (Prod.snd s)) (ts, rid) after,
     Prod.fst (Prod.snd (Prod.snd s)),
     Prod.snd (Prod.snd (Prod.snd s)))
| (_, (_, app_op_t.Remove target)) =>
    (Prod.fst s,
     Prod.fst (Prod.snd s),
     upd (Prod.fst (Prod.snd (Prod.snd s))) target true,
     Prod.snd (Prod.snd (Prod.snd s)))
| (ts, (rid, app_op_t.AddMark sId sSd eId eSd mt)) =>
    let mark : MarkOp := ((ts, rid), sId, sSd, eId, eSd, mt, true)
    let m := Prod.snd (Prod.snd (Prod.snd s))
    -- Add two anchor attachments: start and end.
    let m1 := add ((sId, sSd, mark) : AnchorAttachment) m
    let m2 := add ((eId, eSd, mark) : AnchorAttachment) m1
    (Prod.fst s,
     Prod.fst (Prod.snd s),
     Prod.fst (Prod.snd (Prod.snd s)),
     m2)
| (ts, (rid, app_op_t.RemoveMark sId sSd eId eSd mt)) =>
    let mark : MarkOp := ((ts, rid), sId, sSd, eId, eSd, mt, false)
    let m := Prod.snd (Prod.snd (Prod.snd s))
    let m1 := add ((sId, sSd, mark) : AnchorAttachment) m
    let m2 := add ((eId, eSd, mark) : AnchorAttachment) m1
    (Prod.fst s,
     Prod.fst (Prod.snd s),
     Prod.fst (Prod.snd (Prod.snd s)),
     m2)

inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

/-- Conflict resolution: `Either` everywhere. Every op is a lattice-
merging write; ordering is irrelevant at the state level. -/
@[simp]
def rc (_o1 _o2 : op_t) := rc_res.Either

/-- Commutativity predicate used in `rc_non_comm`. -/
@[simp]
def commutes_with (o1 o2 : op_t) :=
    forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)

/-- Merge: componentwise per-key join on all four components. -/
@[simp]
noncomputable def merge (a b : concrete_st) : concrete_st :=
  let keys_c := union (domain (Prod.fst a)) (domain (Prod.fst b))
  let u_c := const_on keys_c 0
  let c := iter_upd (fun k _ => max (mysel_c (Prod.fst a) k) (mysel_c (Prod.fst b) k)) u_c
  let keys_af := union (domain (Prod.fst (Prod.snd a))) (domain (Prod.fst (Prod.snd b)))
  let u_af := const_on keys_af (0, 0)
  let af := iter_upd (fun k _ => opid_max (mysel_a (Prod.fst (Prod.snd a)) k)
                                           (mysel_a (Prod.fst (Prod.snd b)) k)) u_af
  let keys_d := union (domain (Prod.fst (Prod.snd (Prod.snd a))))
                      (domain (Prod.fst (Prod.snd (Prod.snd b))))
  let u_d := const_on keys_d false
  let d := iter_upd (fun k _ => max (mysel_d (Prod.fst (Prod.snd (Prod.snd a))) k)
                                     (mysel_d (Prod.fst (Prod.snd (Prod.snd b))) k)) u_d
  let m := union (Prod.snd (Prod.snd (Prod.snd a))) (Prod.snd (Prod.snd (Prod.snd b)))
  (c, af, d, m)

set_option maxHeartbeats 0


theorem rc_non_comm (o1: op_t) (o2: op_t):
distinct_ops o1 o2 ∧ get_rid o1 != get_rid o2
→
(rc o1 o2 = rc_res.Either ↔ commutes_with o1 o2) := by
  intro h
  refine ⟨fun _ s => ?_, fun _ => rfl⟩
  rcases o1 with ⟨_, _, _ | _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _ | _⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind


theorem no_rc_chain (o1 : op_t) (o2 : op_t) (o3 : op_t) :
(distinct_ops o1 o2 ∧ distinct_ops o2 o3)
→ (¬(rc o1 o2 = rc_res.Fst_then_snd ∧ rc o2 o3 = rc_res.Fst_then_snd))
:= by sal


theorem cond_comm_base (s: concrete_st) (o1: op_t) (o2: op_t) (o3: op_t) :
(distinct_ops o1 o2 ∧ distinct_ops o2 o3 ∧ distinct_ops o1 o3
    ∧ rc o1 o2 = rc_res.Fst_then_snd ∧ ¬(rc o2 o3 = rc_res.Either))
→
eq (do_ (do_ (do_ s o1) o2) o3) (do_ (do_ (do_ s o2) o1) o3) := by sal


theorem merge_comm (a b: concrete_st) :
eq (merge a b) (merge b a) := by sal


theorem merge_idem (s: concrete_st) :
eq (merge s s) s := by sal


theorem base_2op (o1 o2: op_t) :
 ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧
                    distinct_ops o1 o2
→
 eq (merge (do_ init_st o1) (do_ init_st o2)) (do_ (merge init_st (do_ init_st o2)) o1)
 := by
  intro h
  rcases h with ⟨_, h_rid, _⟩
  rcases o1 with ⟨_, _, _ | _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _ | _⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h_rid ⊢
  all_goals grind


theorem ind_lca_2op (l: concrete_st) (o1 o2 ol: op_t) :
 ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ol ∧ distinct_ops o2 ol ∧
                    eq (merge (do_ l o1) (do_ l o2)) (do_ (merge l (do_ l o2)) o1)
→
 eq (merge (do_ (do_ l ol) o1) (do_ (do_ l ol) o2)) (do_ (merge (do_ l ol) (do_ (do_ l ol) o2)) o1)
:= by
  intro h
  rcases o1 with ⟨_, _, _ | _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _ | _⟩ <;>
    rcases ol with ⟨_, _, _ | _ | _ | _⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind


theorem inter_right_base_2op (a b: concrete_st) (o1 o2 ob ol:op_t) :
 ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o2 ob ∧ distinct_ops o2 ol ∧ distinct_ops ob ol ∧
                    eq (merge (do_ a o1) (do_ b o2)) (do_ (merge a (do_ b o2)) o1) ∧
                    eq (merge (do_ a o1) (do_ (do_ b ob) o2)) (do_ (merge a (do_ (do_ b ob) o2)) o1) ∧
                    eq (merge (do_ (do_ a ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ a ol) (do_ (do_ b ol) o2)) o1)
→
 eq (merge (do_ (do_ a ol) o1) (do_ (do_ (do_ b ob) ol) o2)) (do_ (merge (do_ a ol) (do_ (do_ (do_ b ob) ol) o2)) o1)
 := by sal


theorem inter_left_base_2op (a b : concrete_st) (o1 o2 ob ol:op_t) :
 (rc o2 o1) = rc_res.Fst_then_snd ∧ (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid o2 != get_rid o1 ∧ get_rid ob != get_rid ol ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o2 ob ∧ distinct_ops o2 ol ∧ distinct_ops ob ol ∧
                    eq (merge (do_ (do_ a ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ a ol) (do_ (do_ b ol) o2)) o1)
→
 eq (merge (do_ (do_ (do_ a ob) ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ (do_ a ob) ol) (do_ (do_ b ol) o2)) o1)
:= by sal


theorem inter_right_2op (a b: concrete_st) (o1 o2 ob ol o:op_t) :
 ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    (¬ ((rc o ob) = rc_res.Either) ∨ (rc o ol) = rc_res.Fst_then_snd) ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops o2 ob ∧ distinct_ops o2 ol ∧ distinct_ops o2 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧
                    get_rid o != get_rid ol ∧
                    eq (merge (do_ (do_ a ol) o1) (do_ (do_ (do_ b ob) ol) o2)) (do_ (merge (do_ a ol) (do_ (do_ (do_ b ob) ol) o2)) o1)
→
 eq (merge (do_ (do_ a ol) o1) (do_ (do_ (do_ (do_ b o) ob) ol) o2)) (do_ (merge (do_ a ol) (do_ (do_ (do_ (do_ b o) ob) ol) o2)) o1)
:= by sal


theorem inter_left_2op (a b:concrete_st) (o1 o2 ob ol o:op_t) :
 (rc o2 o1) = rc_res.Fst_then_snd ∧ (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid o2 != get_rid o1 ∧ get_rid ob != get_rid ol ∧
                    (¬ ((rc o ob) = rc_res.Either) ∨ (rc o ol) = rc_res.Fst_then_snd) ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops o2 ob ∧ distinct_ops o2 ol ∧ distinct_ops o2 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧
                    get_rid o != get_rid ol ∧
                    eq (merge (do_ (do_ (do_ a ob) ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ (do_ a ob) ol) (do_ (do_ b ol) o2)) o1)
→
 eq (merge (do_ (do_ (do_ (do_ a o) ob) ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ (do_ (do_ a o) ob) ol) (do_ (do_ b ol) o2)) o1)
 := by sal


theorem inter_lca_2op (a b:concrete_st) (o1 o2 ol:op_t):
 ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ol ∧ distinct_ops o2 ol ∧
                    (exists o, (rc o ol) = rc_res.Fst_then_snd) ∧
                    eq (merge (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ a ol) (do_ b ol)) o1) ∧
                    eq (merge (do_ a o1) (do_ b o2)) (do_ (merge a (do_ b o2)) o1)
→
 eq (merge (do_ (do_ a ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ a ol) (do_ (do_ b ol) o2)) o1)
:= by sal


theorem ind_right_2op (a b: concrete_st) (o1 o2 o2':op_t) :
 (rc o2 o1) = rc_res.Fst_then_snd ∧ get_rid o1 != get_rid o2 ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 o2' ∧ distinct_ops o2 o2' ∧
                    eq (merge (do_ a o1) (do_ b o2)) (do_ (merge a (do_ b o2)) o1)
→
 eq (merge (do_ a o1) (do_ (do_ b o2') o2)) (do_ (merge a (do_ (do_ b o2') o2)) o1)
:= by sal


theorem ind_left_2op (a b:concrete_st) (o1 o2 o1':op_t) :
 ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 o1' ∧ distinct_ops o2 o1' ∧
                    eq (merge (do_ a o1) (do_ b o2)) (do_ (merge a (do_ b o2)) o1)
→
 eq (merge (do_ (do_ a o1') o1) (do_ b o2)) (do_ (merge (do_ a o1') (do_ b o2)) o1)
:= by
  intro h
  rcases o1 with ⟨_, _, _ | _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _ | _⟩ <;>
    rcases o1' with ⟨_, _, _ | _ | _ | _⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind


theorem base_1op (o1:op_t) :
eq (merge (do_ init_st o1) init_st) (do_ (merge init_st init_st) o1) := by
  rcases o1 with ⟨_, _, _ | _ | _ | _⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at *
  all_goals grind


theorem ind_lca_1op (l:concrete_st) (o1 ol:op_t) :
distinct_ops o1 ol ∧
                    eq (merge (do_ l o1) l) (do_ (merge l l) o1)
→
 eq (merge (do_ (do_ l ol) o1) (do_ l ol)) (do_ (merge (do_ l ol) (do_ l ol)) o1)
:= by
  intro h
  rcases o1 with ⟨_, _, _ | _ | _ | _⟩ <;> rcases ol with ⟨_, _, _ | _ | _ | _⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind


theorem inter_right_base_1op (a b :concrete_st) (o1 ob ol:op_t) :
 (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops ob ol ∧
                    ((rc ob o1) = rc_res.Fst_then_snd → eq (merge (do_ a o1) (do_ b ob)) (do_ (merge a (do_ b ob)) o1)) ∧
                    eq (merge (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ a ol) (do_ b ol)) o1)
→  eq (merge (do_ (do_ a ol) o1) (do_ (do_ b ob) ol)) (do_ (merge (do_ a ol) (do_ (do_ b ob) ol)) o1)
:= by sal


theorem inter_left_base_1op (a b:concrete_st) (o1 ob ol:op_t) :
 (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops ob ol ∧
                    eq (merge (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ a ol) (do_ b ol)) o1)
→
eq (merge (do_ (do_ (do_ a ob) ol) o1) (do_ b ol)) (do_ (merge (do_ (do_ a ob) ol) (do_ b ol)) o1)
:= by sal


theorem inter_right_1op (a b:concrete_st) (o1 ob ol o:op_t) :
 (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    (¬ ((rc o ob) = rc_res.Either) ∨ (rc o ol) = rc_res.Fst_then_snd) ∧
                    distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧
                    get_rid o != get_rid ol ∧
                    eq (merge (do_ (do_ a ol) o1) (do_ (do_ b ob) ol)) (do_ (merge (do_ a ol) (do_ (do_ b ob) ol)) o1)
→
 eq (merge (do_ (do_ a ol) o1) (do_ (do_ (do_ b o) ob) ol)) (do_ (merge (do_ a ol) (do_ (do_ (do_ b o) ob) ol)) o1)
:= by sal


theorem inter_left_1op (a b:concrete_st) (o1 ob ol o:op_t) :
 (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    (¬ ((rc o ob) = rc_res.Either) ∨ (rc o ol) = rc_res.Fst_then_snd) ∧
                    distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧
                    get_rid o != get_rid ol ∧
                    eq (merge (do_ (do_ (do_ a ob) ol) o1) (do_ b ol)) (do_ (merge (do_ (do_ a ob) ol) (do_ b ol)) o1)
→
 eq (merge (do_ (do_ (do_ (do_ a o) ob) ol) o1) (do_ b ol)) (do_ (merge (do_ (do_ (do_ a o) ob) ol) (do_ b ol)) o1)
:= by sal


theorem inter_lca_1op (a b:concrete_st) (o1 ol oi:op_t) :
 distinct_ops o1 ol ∧ distinct_ops o1 oi ∧ distinct_ops ol oi ∧
                    (exists o, (rc o ol) = rc_res.Fst_then_snd) ∧
                    (exists o, (rc o oi) = rc_res.Fst_then_snd) ∧
                    eq (merge (do_ (do_ a oi) o1) (do_ b oi)) (do_ (merge (do_ a oi) (do_ b oi)) o1) ∧
                    eq (merge (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ a ol) (do_ b ol)) o1)
→
eq (merge (do_ (do_ (do_ a oi) ol) o1) (do_ (do_ b oi) ol))
                      (do_ (merge (do_ (do_ a oi) ol) (do_ (do_ b oi) ol)) o1)
:= by sal


theorem ind_left_1op (a b:concrete_st) (o1 o1' ol:op_t) :
 distinct_ops o1 o1' ∧ distinct_ops o1 ol ∧ distinct_ops o1' ol ∧
                    eq (merge (do_ a o1) (do_ b ol)) (do_ (merge a (do_ b ol)) o1)
→
 eq (merge (do_ (do_ a o1') o1) (do_ b ol)) (do_ (merge (do_ a o1') (do_ b ol)) o1)
:= by
  intro h
  rcases o1 with ⟨_, _, _ | _ | _ | _⟩ <;> rcases o1' with ⟨_, _, _ | _ | _ | _⟩ <;>
    rcases ol with ⟨_, _, _ | _ | _ | _⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind


theorem ind_right_1op (a b: concrete_st) (o2 o2' ol:op_t) :
 distinct_ops o2 o2' ∧ distinct_ops o2 ol ∧ distinct_ops o2' ol ∧
                    eq (merge (do_ a ol) (do_ b o2)) (do_ (merge (do_ a ol) b) o2)
→
 eq (merge (do_ a ol) (do_ (do_ b o2') o2)) (do_ (merge (do_ a ol) (do_ b o2')) o2)
:= by
  intro h
  rcases o2 with ⟨_, _, _ | _ | _ | _⟩ <;> rcases o2' with ⟨_, _, _ | _ | _ | _⟩ <;>
    rcases ol with ⟨_, _, _ | _ | _ | _⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind


theorem lem_0op (a b:concrete_st) (ol:op_t) :
eq (merge (do_ a ol) (do_ b ol)) (do_ (merge a b) ol) := by
  rcases ol with ⟨_, _, _ | _ | _ | _⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at *
  all_goals grind
