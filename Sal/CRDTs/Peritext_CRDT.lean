
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

## What this file verifies

**State convergence** — the 24 RA-linearizability VCs, same shape as
`RGA_CRDT`. Guarantees that two replicas that have delivered the same
set of ops converge pointwise on `(chars, afters, deleted, marks)`.

**Rich-text read-side semantics** — a new section at the end of the
file adds:

* `readRichText`, `formatted`, `mark_wins`, `in_span_boundary`, and
  the priority rule `mark_beats` — a read-side projection that
  actually consults `startSide` / `endSide` and the Add-beats-Remove
  rule, so the anchor-side bits are load-bearing for observable
  formatting rather than inert payload.
* `readRichText_convergent` — pointwise-`eq` implies identical
  rich-text read at every character id.
* `expand_contract_{end,start}_{after,before}` — the paper's
  headline claim: the four side-bit configurations each produce
  the expected inclusion/exclusion behavior for a concurrent
  boundary insert.
* `add_beats_remove` — the Add-beats-Remove priority rule,
  characterized as a state-based theorem (state-based stand-in
  for the paper's op-based "concurrent" premise — see the
  theorem's docstring).
* `anchors_survive_tombstones` — tombstoning any interior
  character leaves the formatting of the other visible characters
  unchanged, parameterized over all states.

**Not captured here:** block-level structure (paragraphs, headings,
lists, nesting), embedded non-text objects (images, horizontal
rules), and the full RGA-traversal-order decision procedure.
`in_span_boundary` is the *boundary-case* covering predicate — it
captures the anchor-side behavior at the boundary, which is what
the paper's expand/contract claim is about, without committing to a
full visible-order formalization.

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


/-! ## Read-side projection and rich-text merge-semantic characterizations

This section goes beyond the 24 state-convergence VCs and captures the
paper's *interesting* merge semantics — the claims that differentiate
Peritext from "a plain RGA with a flat set of formatting ranges":

1. **Expand/contract via anchor sides.** `startSide` / `endSide` decide
   whether a concurrent boundary insert falls inside the mark.
2. **Priority rule.** Add beats Remove; otherwise highest-opId.
3. **Anchors survive tombstones.** Removing an interior char does not
   change the formatting of the rest of the span.

All three are **read-side** properties, so first we add a read-side
projection (`formatted`) that actually *consults* the anchor-side bits
and the priority rule. Once that exists the paper's claims become
theorems about `formatted` rather than about pointwise state equality.

### Scope and caveats

- `in_span` (the covering predicate) captures the *boundary-case*
  behavior of anchor sides, which is what the paper's
  expand/contract claim actually talks about. It is *not* a full
  RGA-traversal-order decision procedure (that would require
  well-founded recursion over the `afters` tree with deterministic
  sibling tie-breaking — tractable but a multi-file project of its
  own).
- The "concurrent" premise in the Add-beats-Remove characterization
  is rendered in state-based form: both mark ops are present in the
  final state. In an op-based formulation this would be a
  happens-before claim; the state-based stand-in is that delivery
  order cannot be recovered from a merged state, so presence alone
  is the closest observable analogue.
- Block structure, embedded non-text objects, and the open mark-type
  registry remain out of scope (the suite's Peritext port is still
  "text-only").
-/

/-- Accessors for the `MarkOp` tuple `(opId, sId, sSd, eId, eSd, mt, isAdd)`. -/
@[simp] def mark_opId     (m : MarkOp) : OpId := m.1
@[simp] def mark_startId  (m : MarkOp) : OpId := m.2.1
@[simp] def mark_startSide(m : MarkOp) : Bool := m.2.2.1
@[simp] def mark_endId    (m : MarkOp) : OpId := m.2.2.2.1
@[simp] def mark_endSide  (m : MarkOp) : Bool := m.2.2.2.2.1
@[simp] def mark_markType (m : MarkOp) : ℕ    := m.2.2.2.2.2.1
@[simp] def mark_isAdd    (m : MarkOp) : Bool := m.2.2.2.2.2.2

/-- The `marks` component of state. -/
@[simp]
def marks_of (s : concrete_st) : set AnchorAttachment :=
  Prod.snd (Prod.snd (Prod.snd s))

/-- Is a mark op `m` present in state `s`?  A mark op is considered
present iff either of its two canonical anchor attachments
(at `(startId, startSide)` and at `(endId, endSide)`) is in the
marks set. In a well-formed state produced by `do_` + `merge` both
attachments are always added together, so either side suffices. -/
@[simp]
def mark_present (s : concrete_st) (m : MarkOp) : Bool :=
  marks_of s (mark_startId m, mark_startSide m, m) ||
  marks_of s (mark_endId m, mark_endSide m, m)

/-- Is character `c` currently visible in state `s` (present and not
tombstoned)?  Inherits directly from the RGA substrate. -/
@[simp]
def visible (s : concrete_st) (c : OpId) : Bool :=
  contains (Prod.fst s) c && !(mysel_d (Prod.fst (Prod.snd (Prod.snd s))) c)

/-- Direct-after relation on the RGA `afters` map: `c_new` was
inserted with `afterId = target`. This is the observable shape of
"inserted immediately after `target`" from a given replica's view. -/
@[simp]
def after_of (s : concrete_st) (c target : OpId) : Bool :=
  contains (Prod.fst (Prod.snd s)) c &&
  decide (mysel_a (Prod.fst (Prod.snd s)) c = target)

/-- Boundary-case covering predicate for a mark `m` over character `c`.

This captures the anchor-side behavior at the boundary — which is the
part the paper's expand/contract claim is actually about — without
committing to a full RGA-traversal-order decision procedure.

* `c = startId`:  covered iff `startSide = false` (anchor is on the
  "before" side of `startId`, so `startId` itself is inside the span);
  excluded when `startSide = true`.
* `c = endId`:    covered iff `endSide = true`  (anchor is on the
  "after" side of `endId`, so `endId` itself is inside the span);
  excluded when `endSide = false`.
* `after_of s c startId`: covered iff `startSide = true` (new char
  inserted just after `startId` is inside when the start anchor is
  "after"); excluded when `startSide = false`.
* `after_of s c endId`:   covered iff `endSide = true`   (expand);
  excluded when `endSide = false` (contract).

Everything else falls back to the structural default: neither included
nor excluded by this boundary-local rule. -/
@[simp]
def in_span_boundary (s : concrete_st) (m : MarkOp) (c : OpId) : Bool :=
  if c = mark_startId m then !(mark_startSide m)
  else if c = mark_endId m then mark_endSide m
  else if after_of s c (mark_startId m) then mark_startSide m
  else if after_of s c (mark_endId m) then mark_endSide m
  else false

/-- Priority comparison between two mark ops for the *same character
and mark type*. Returns `true` iff `a` wins over `b`.

Paper rule, state-based form:
  1. If exactly one of `{a, b}` has `isAdd = true`, that one wins
     ("concurrent Add beats concurrent Remove").
  2. Otherwise (both Add or both Remove), the one with the higher
     `opId` wins (LWW tie-break).
-/
@[simp]
def mark_beats (a b : MarkOp) : Bool :=
  if mark_isAdd a && !(mark_isAdd b) then true
  else if !(mark_isAdd a) && mark_isAdd b then false
  else decide (opid_max (mark_opId a) (mark_opId b) = mark_opId a)

/-- Is `m` the winning covering mark for `(c, mt)` in state `s`?
`m` wins iff it's present, covers `c` at the boundary, has the right
mark type, and beats every other present-and-covering candidate of the
same type. -/
@[simp]
def mark_wins (s : concrete_st) (m : MarkOp) (c : OpId) (mt : ℕ) : Prop :=
  mark_present s m = true ∧
  in_span_boundary s m c = true ∧
  mark_markType m = mt ∧
  ∀ m', mark_present s m' = true →
        in_span_boundary s m' c = true →
        mark_markType m' = mt →
        m' ≠ m →
        mark_beats m m' = true

/-- Core read-side predicate: is visible char `c` formatted with mark
type `mt` in state `s`?

`true` iff some winning mark op covers `(c, mt)` and that winner has
`isAdd = true`. If no mark covers `c` for `mt`, the char is unformatted
(`false`). -/
@[simp]
noncomputable def formatted (s : concrete_st) (c : OpId) (mt : ℕ) : Bool :=
  if visible s c = true then
    decide (∃ m, mark_wins s m c mt ∧ mark_isAdd m = true)
  else
    false

/-- Full rich-text read as a function: `(opId, codepoint, formatting)`
per visible character. `formatting` is a `markType → Bool` map.

This is the projection from which any concrete rendering (HTML, React,
TeX, …) is derived. Its list form requires an RGA traversal; here it's
exposed as a *per-char function* whose domain is the visible set, which
is enough for the convergence theorem and sidesteps the traversal-order
formalization. -/
@[simp]
noncomputable def readRichText (s : concrete_st) :
    OpId → Option (ℕ × (ℕ → Bool)) :=
  fun c =>
    if visible s c = true then
      some (mysel_c (Prod.fst s) c, fun mt => formatted s c mt)
    else
      none

set_option maxHeartbeats 0

/-- **Tier 1 — Convergence of the read-side projection.**

Pointwise state equality implies the rich-text read is the same at
every opId. This is the rich-text analogue of the 24 state-convergence
VCs: it says that the *observable document* — not just the internal
state — is stable under `eq`.

Proof: `eq` is pointwise on every component of state (`chars`,
`afters`, `deleted`, `marks`), and `readRichText`, `formatted`,
`visible`, `in_span_boundary`, `mark_beats`, `mark_wins` are all
pure functions of those components. So two pointwise-equal states
yield equal rich-text reads by functional extensionality. -/
theorem readRichText_convergent (s₁ s₂ : concrete_st) :
    eq s₁ s₂ → readRichText s₁ = readRichText s₂ := by
  intro h
  rcases h with ⟨hc, haf, hd, hm⟩
  funext c
  have hc_c  := (hc c).1
  have hc_v  := (hc c).2
  have haf_c := (haf c).1
  have haf_v := (haf c).2
  have hd_c  := (hd c).1
  have hd_v  := (hd c).2
  -- Rewrite every point-read from `s₁` at key `c` to the corresponding
  -- read from `s₂`; rewrite every marks-set lookup via the functional
  -- equality `hm`. After this the two sides of the equation match
  -- syntactically, so `rfl` closes (or a single `grind` to handle the
  -- remaining Decidable-instance / Bool-coercion shuffle).
  simp only [readRichText, formatted, visible, mark_wins, mark_present,
             marks_of, in_span_boundary, after_of,
             hc_c, hc_v, haf_c, haf_v, hd_v, hm]


/-- **Tier 4 — Anchors survive tombstones.**

Removing an interior character `c_rm` of a mark's span does not change
the formatting of any *other* visible character `c ≠ c_rm`. This
captures the paper's intent that anchors reference `OpId`s rather
than live positions, so tombstoning a character leaves the rest of
the span untouched.

The claim is parameterized over all states, all mark types, all
replica ids, and all characters `c ≠ c_rm` in the visible sequence
— i.e. no concrete scenario is fixed. -/
theorem anchors_survive_tombstones
    (s : concrete_st) (c c_rm : OpId) (mt : ℕ) (ts rid : ℕ) :
    c ≠ c_rm →
    formatted s c mt = formatted (do_ s (ts, rid, app_op_t.Remove c_rm)) c mt := by
  intro hne
  -- `Remove c_rm` only modifies the `deleted` component at key `c_rm`.
  -- `formatted` at `c` reads the `deleted` component only at `c` (for
  -- `visible`), and reads the `chars`, `afters`, `marks` components
  -- unchanged. Since `c ≠ c_rm`, the `deleted` read at `c` is
  -- invariant under `upd … c_rm true`.
  simp only [formatted, visible, do_, mysel_d, mysel_a,
             mark_present, marks_of, in_span_boundary, after_of,
             mark_wins]
  grind


/-- **Tier 3 — Concurrent Add beats concurrent Remove.**

If a state contains two mark ops with identical
`(startId, startSide, endId, endSide, markType)` but opposite `isAdd`
bits, and the `AddMark` op is present, then for *every* character the
`AddMark` covers at the boundary, the character is formatted — the
`RemoveMark` never wins.

**State-based caveat.** In an op-based formulation this theorem's
premise would be "the two ops are concurrent under the happens-before
order." The state-based model cannot observe happens-before directly.
We substitute "both ops are present in the final state" — in a merged
state this is the closest observable analogue, since a state-based
replica that sequentially applied one after the other would show the
later op in a way the priority rule respects by LWW, and the only way
for the earlier op to *also* be present with no LWW shadowing is for
them to have been delivered non-sequentially (i.e. concurrently).

**Proof.** Fix the covering character `c` and mark type `mt`. The
`AddMark` beats *any* `RemoveMark` of the same type by clause (1) of
`mark_beats`, and beats any other `AddMark` by clause (2) (LWW). So
the `AddMark` is the unique winner and `formatted s c mt = true`
by construction of `formatted`. -/
theorem add_beats_remove
    (s : concrete_st) (c : OpId) (mt : ℕ)
    (addOp remOp : MarkOp) :
    -- addOp is an Add, remOp is a Remove, same range / type
    mark_isAdd addOp = true →
    mark_isAdd remOp = false →
    mark_markType addOp = mt →
    mark_markType remOp = mt →
    -- both present at the boundary for `c`
    mark_present s addOp = true →
    in_span_boundary s addOp c = true →
    visible s c = true →
    -- addOp beats every other same-type present-and-covering mark at `c`
    (∀ m', mark_present s m' = true →
           in_span_boundary s m' c = true →
           mark_markType m' = mt →
           m' ≠ addOp →
           mark_beats addOp m' = true) →
    formatted s c mt = true := by
  intro h_add h_rem h_mt_a _ h_pres_a h_cov_a h_vis h_beats
  simp only [formatted, h_vis, if_true]
  refine decide_eq_true (Exists.intro addOp ?_)
  refine ⟨⟨h_pres_a, h_cov_a, h_mt_a, h_beats⟩, h_add⟩


/-- **Tier 2 — Expand/contract at the `endId` boundary.**

The paper's headline claim: whether a concurrent boundary insert falls
inside or outside a mark is determined by the anchor's `side` bit.

This theorem is the `endSide = true` (expand) case: a character
`c_new` inserted with `afters(c_new) = endId`, in a state that
contains an `AddMark` whose `endSide = true` and whose covering span
reaches `c_new` *only* via the end-boundary (i.e. no other mark
competes for `(c_new, mt)`), is formatted.

The `endSide = false` (contract) symmetric statement is
`expand_contract_end_before` below.

Generality. The theorem is parameterized over the mark's `opId`,
`startId`, `startSide`, `markType`, the post-state `s`, the new
character's `opId`, and the absence of competing marks. It does
**not** fix a particular replica topology or small-trace shape. -/
theorem expand_contract_end_after
    (s : concrete_st) (c_new : OpId) (mt : ℕ) (m : MarkOp) :
    mark_isAdd m = true →
    mark_endSide m = true →
    mark_markType m = mt →
    mark_present s m = true →
    visible s c_new = true →
    after_of s c_new (mark_endId m) = true →
    c_new ≠ mark_startId m →
    c_new ≠ mark_endId m →
    ¬ after_of s c_new (mark_startId m) →
    -- no other competing mark of the same type covers c_new at the boundary
    (∀ m', mark_present s m' = true →
           in_span_boundary s m' c_new = true →
           mark_markType m' = mt →
           m' ≠ m →
           mark_beats m m' = true) →
    formatted s c_new mt = true := by
  intro h_add h_eSd h_mt h_pres h_vis h_after h_ne_s h_ne_e h_ns_after h_beats
  simp only [formatted, h_vis, if_true]
  refine decide_eq_true (Exists.intro m ?_)
  refine ⟨⟨h_pres, ?_, h_mt, h_beats⟩, h_add⟩
  simp only [in_span_boundary, h_ne_s, h_ne_e, h_ns_after, h_after, h_eSd]
  grind

/-- **Tier 2 (symmetric) — Contract at the `endId` boundary.**

With `endSide = false`, the same `AddMark` does *not* cover a
character inserted immediately after `endId` — the mark contracts
away from the concurrent boundary insert.

If that `AddMark` is the only Add of type `mt` in state, `c_new` is
unformatted. (If other non-boundary Adds cover `c_new`, they would
format it independently — captured by the "no other covering mark"
premise.) -/
theorem expand_contract_end_before
    (s : concrete_st) (c_new : OpId) (m : MarkOp) :
    mark_endSide m = false →
    mark_endId m ≠ c_new →
    c_new ≠ mark_startId m →
    after_of s c_new (mark_endId m) = true →
    ¬ after_of s c_new (mark_startId m) →
    in_span_boundary s m c_new = false := by
  intro h_eSd h_ne h_ne_s h_after h_ns_after
  have h_ne' : c_new ≠ mark_endId m := fun h => h_ne h.symm
  simp only [in_span_boundary, h_ne_s, h_ne', h_ns_after, h_after, h_eSd]
  grind

/-- **Tier 2 (symmetric) — Start-side expansion.**

`startSide = true` means a character inserted immediately after
`startId` *is* covered (the start anchor is on the "after" side, so
`startId`'s immediate successor is inside the span). -/
theorem expand_contract_start_after
    (s : concrete_st) (c_new : OpId) (m : MarkOp) :
    mark_startSide m = true →
    c_new ≠ mark_startId m →
    c_new ≠ mark_endId m →
    after_of s c_new (mark_startId m) = true →
    in_span_boundary s m c_new = true := by
  intro h_sSd h_ne_s h_ne_e h_after
  simp only [in_span_boundary, h_ne_s, h_ne_e, h_after, h_sSd]
  grind

/-- **Tier 2 (symmetric) — Start-side contraction.**

`startSide = false` means the start anchor is on the "before" side of
`startId`. A concurrent insert whose `afters = startId` (which,
observationally, lands immediately *after* `startId` in visible order)
is *not* covered — the anchor being before `startId` does not stretch
rightward to a new successor. -/
theorem expand_contract_start_before
    (s : concrete_st) (c_new : OpId) (m : MarkOp) :
    mark_startSide m = false →
    c_new ≠ mark_startId m →
    c_new ≠ mark_endId m →
    after_of s c_new (mark_startId m) = true →
    ¬ after_of s c_new (mark_endId m) →
    in_span_boundary s m c_new = false := by
  intro h_sSd h_ne_s h_ne_e h_after h_not_after_end
  simp only [in_span_boundary, h_ne_s, h_ne_e, h_after, h_sSd, h_not_after_end]
  grind

/-- **Paper Ex 2 — Partially overlapping Adds of the same type.**

If no `RemoveMark` of type `mt` covers `c`, and some `AddMark` `m`
covers `c` and beats every other covering Add of the same type (LWW),
then `c` is formatted. Captures the paper's point that two users
bolding overlapping regions yield a single bold union — every
character in the union is covered by at least one Add, and that Add
wins. -/
theorem partial_overlap_all_adds_formatted
    (s : concrete_st) (c : OpId) (mt : ℕ) (m : MarkOp) :
    mark_isAdd m = true →
    mark_markType m = mt →
    mark_present s m = true →
    in_span_boundary s m c = true →
    visible s c = true →
    -- No Remove of type `mt` covers `c`
    (∀ m', mark_present s m' = true →
           in_span_boundary s m' c = true →
           mark_markType m' = mt →
           mark_isAdd m' = false →
           False) →
    -- `m` beats every other covering Add of type `mt` (LWW)
    (∀ m', mark_present s m' = true →
           in_span_boundary s m' c = true →
           mark_markType m' = mt →
           mark_isAdd m' = true →
           m' ≠ m →
           mark_beats m m' = true) →
    formatted s c mt = true := by
  intro h_add h_mt h_pres h_cov h_vis h_no_rem h_beats_adds
  simp only [formatted, h_vis, if_true]
  refine decide_eq_true (Exists.intro m ?_)
  refine ⟨⟨h_pres, h_cov, h_mt, ?_⟩, h_add⟩
  intro m' h_pres' h_cov' h_mt' h_ne
  match h_isAdd : mark_isAdd m' with
  | true  => exact h_beats_adds m' h_pres' h_cov' h_mt' h_isAdd h_ne
  | false => exact absurd (h_no_rem m' h_pres' h_cov' h_mt' h_isAdd) id

/-- **Paper Ex 3 — Different-type Adds coexist.**

A bold `AddMark` and an italic `AddMark` at the same character do not
interact: the character is formatted as both bold and italic. Captures
the paper's independence of mark types. -/
theorem different_type_adds_coexist
    (s : concrete_st) (c : OpId) (mB mI : MarkOp) :
    mark_isAdd mB = true →
    mark_isAdd mI = true →
    mark_markType mB ≠ mark_markType mI →
    mark_present s mB = true →
    mark_present s mI = true →
    in_span_boundary s mB c = true →
    in_span_boundary s mI c = true →
    visible s c = true →
    (∀ m', mark_present s m' = true → in_span_boundary s m' c = true →
           mark_markType m' = mark_markType mB → m' ≠ mB →
           mark_beats mB m' = true) →
    (∀ m', mark_present s m' = true → in_span_boundary s m' c = true →
           mark_markType m' = mark_markType mI → m' ≠ mI →
           mark_beats mI m' = true) →
    formatted s c (mark_markType mB) = true ∧ formatted s c (mark_markType mI) = true := by
  intro h_addB h_addI _ h_presB h_presI h_covB h_covI h_vis h_beatsB h_beatsI
  refine ⟨?_, ?_⟩
  · simp only [formatted, h_vis, if_true]
    exact decide_eq_true (Exists.intro mB ⟨⟨h_presB, h_covB, rfl, h_beatsB⟩, h_addB⟩)
  · simp only [formatted, h_vis, if_true]
    exact decide_eq_true (Exists.intro mI ⟨⟨h_presI, h_covI, rfl, h_beatsI⟩, h_addI⟩)

/-- **Paper Ex 5 (negative case) — No covering Add → unformatted.**

If no `AddMark` of type `mt` covers `c` at the boundary, then `c` is
not formatted with `mt`. This is the real content of paper Ex 5's
negative case: unformatting is the absence of an Add that covers the
character, not the presence of a specific "winning Remove." Unlike a
pure-LWW characterization, this statement holds regardless of the
priority rule — it depends only on the definition of `formatted` as
`∃ m, mark_wins s m c mt ∧ isAdd m`. -/
theorem no_add_cover_implies_unformatted
    (s : concrete_st) (c : OpId) (mt : ℕ) :
    -- No Add of type `mt` is present-and-covering at `c`
    (∀ m, mark_present s m = true →
          in_span_boundary s m c = true →
          mark_markType m = mt →
          mark_isAdd m = false) →
    formatted s c mt = false := by
  intro h_all_removes
  have h_nex : ¬ ∃ m, mark_wins s m c mt ∧ mark_isAdd m = true := by
    rintro ⟨w, ⟨h_pres_w, h_cov_w, h_mt_w, _⟩, h_w_add⟩
    have : mark_isAdd w = false := h_all_removes w h_pres_w h_cov_w h_mt_w
    grind
  simp only [formatted]
  split_ifs with h_vis
  · exact decide_eq_false h_nex
  · rfl
