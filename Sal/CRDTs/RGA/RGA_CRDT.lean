
import Std.Tactic.BVDecide
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
# Replicated Growable Array (RGA) — state-based CRDT

## What this is

A state-based port of the classical RGA sequence CRDT
(Roh, Jeon, Kim, Lee, *Replicated Abstract Data Types: Building Blocks for
Collaborative Applications*, JPDC 2011). RGA is the canonical op-based
replicated sequence that underlies Automerge, Yjs, Peritext, and many
other collaborative-editing systems.

Most treatments of RGA in the literature are **operation-based**: each
`insert(char, afterId)` and `remove(targetId)` is broadcast as a
causally-delivered op, and replicas buffer ops until their `afterId`
predecessor has arrived. The state-based reformulation used here stores
the op log directly as a grow-only state, which makes the convergence
proof structure align naturally with SAL's `⟨Σ, σ₀, do, merge, rc⟩`
framework.

## Design

**Identities.** Each inserted character has a unique identifier
`OpId = ℕ × ℕ` = `(timestamp, replica id)`. Timestamps are globally
unique per the paper's `distinct_ops` assumption, so different
characters always have different `OpId`s. The sentinel `(0, 0)` is
reserved as the "start of document" anchor — no real op has it.

**State.** Three grow-only maps, all keyed by `OpId`:

* `chars : Map OpId ℕ` — the character codepoint of the insert op
  with that `OpId`. Set once (by the Insert that created the opId),
  never updated.
* `afters : Map OpId OpId` — the `afterId` predecessor of the insert
  op with that `OpId`. Also set-once.
* `deleted : Map OpId Bool` — monotonic tombstone flag. Starts false
  (implicit, via the zero-default lookup), flips true on `Remove`,
  never flips back.

The state is a pure snapshot of all ops this replica has
(directly or transitively) seen. The *canonical RGA sequence* — the
text as a user would read it — is a **read-side projection** of this
state, computed by a deterministic traversal that linearises the
`afterId` DAG into a total order. That traversal is not part of the
CRDT state or the convergence proof; it lives in a separate
`readSeq : concrete_st → List (ℕ × ℕ × ℕ)` function (TODO, not in
this file) and produces the same list for any two `eq`-equivalent
states.

**Operations.**

* `Insert ch after` at replica `rid` with timestamp `ts`:
  writes `chars[(ts, rid)] := ch`, `afters[(ts, rid)] := after`,
  leaves `deleted` unchanged.
* `Remove target`: writes `deleted[target] := true`. Idempotent; the
  target's `chars`/`afters` entries are untouched (tombstones, not
  deletions, because later ops may reference this opId as their
  `afterId` even after removal).

**Merge.** Componentwise per-key `max` on all three maps:

* `chars`: `max` on `ℕ`. Under the well-formedness invariant that a
  given `OpId` carries a unique char (enforced by `distinct_ops`),
  both sides agree and `max = either`.
* `afters`: `lex_max` on `ℕ × ℕ`, again agreeing under the
  well-formedness invariant.
* `deleted`: `max` on `Bool` = logical OR. Once any replica has
  observed the remove, the tombstone propagates.

**`rc`.** `Either` for every pair. Every op is a per-key write to a
disjoint `OpId` slot (Insert's opId is unique by `distinct_ops`;
Remove's target is the same across replicas that remove the same
char, but the write is idempotent `true`). So `do_` composition
commutes at the state level.

## What the 24 VCs verify

Pure state-convergence: associativity, commutativity, and idempotence
of `merge` lifted through `do_` composition, for every ordering of
up to 4 ops. These VCs follow from the fact that each of the three
map components is a grow-only join-semilattice under the chosen
`max`.

The RGA *ordering* semantics (that the canonical sequence respects
the `afterId` DAG with opId-descending tiebreak) is **not** among the
24 VCs. It is a downstream theorem over the read-side `readSeq`
function and would be stated as:

    eq s₁ s₂ → readSeq s₁ = readSeq s₂

which is a trivial functional extensionality given the pointwise
definition of `eq`. Any serious RGA-correctness claim (e.g. "the
sequence reflects the op causal order") would also be a separate
read-side theorem, outside SAL's 24 VCs.

## Relationship to existing CRDTs

* Structurally a 3-component generalisation of `PN_Counter_CRDT`
  (two grow-only `Map ℕ Int`) and `Shopping_Cart_CRDT` (two grow-only
  `Map (ℕ × ℕ) Int`). Here the components are grow-only
  `Map OpId _`, and one of them (`deleted`) tracks a monotonic flag.
* `Replicated_Growable_Array_MRDT.lean` (in `Sal/MRDTs/`) is the
  paper's three-way-merge version, which takes an LCA state. The
  present file is a *state-based* (two-way-merge) CRDT formulation;
  they are distinct CRDTs with different merge signatures.
-/

/-- An op identifier: `(timestamp, replica id)`. Globally unique
across all ops under `distinct_ops`. The sentinel `(0, 0)` is used as
the "start of document" anchor and carries no real payload. -/
@[simp] abbrev OpId := ℕ × ℕ

/-- Lexicographic max on `OpId`. Used as the join on the `afters`
map. Commutative / associative / idempotent. -/
@[simp, grind]
def opid_max (a b : OpId) : OpId :=
  if a.1 > b.1 then a
  else if b.1 > a.1 then b
  else if a.2 ≥ b.2 then a
  else b

/-- State: `(chars, afters, deleted)`. Three grow-only maps keyed by
`OpId`. The first two are immutable per key (set by Insert, never
updated); the third is a monotonic bool (flips false → true on
Remove). -/
@[simp] abbrev concrete_st :=
  map OpId ℕ × map OpId OpId × map OpId Bool

/-- Zero-default lookup on the character map. Returns the char at
`k` if present, else `0`. -/
@[simp]
def mysel_c (s : map OpId ℕ) (k : OpId) : ℕ :=
  if (contains s k) then (sel s k) else 0

/-- `(0, 0)`-default lookup on the afterId map. Used in merge to
join two maps where either side may be missing the key. -/
@[simp]
def mysel_a (s : map OpId OpId) (k : OpId) : OpId :=
  if (contains s k) then (sel s k) else (0, 0)

/-- `false`-default lookup on the deleted map. Consistent with
treating missing entries as "not tombstoned". -/
@[simp]
def mysel_d (s : map OpId Bool) (k : OpId) : Bool :=
  if (contains s k) then (sel s k) else false

/-- Initial state: all three maps empty. No inserts, no tombstones. -/
@[simp]
def init_st : concrete_st :=
  (const_on empty 0, const_on empty (0, 0), const_on empty false)

/-- Pointwise state equality: three ∀-conjuncts, one per component,
each asserting membership and value agreement. -/
@[simp]
def eq (a b : concrete_st) :=
  (forall k, (contains (Prod.fst a) k = contains (Prod.fst b) k) ∧
             (mysel_c (Prod.fst a) k = mysel_c (Prod.fst b) k)) ∧
  (forall k, (contains (Prod.fst (Prod.snd a)) k = contains (Prod.fst (Prod.snd b)) k) ∧
             (mysel_a (Prod.fst (Prod.snd a)) k = mysel_a (Prod.fst (Prod.snd b)) k)) ∧
  (forall k, (contains (Prod.snd (Prod.snd a)) k = contains (Prod.snd (Prod.snd b)) k) ∧
             (mysel_d (Prod.snd (Prod.snd a)) k = mysel_d (Prod.snd (Prod.snd b)) k))

/-- User-level operations. `Insert` carries the char codepoint and
the `afterId` predecessor; `Remove` carries the target opId being
tombstoned. -/
inductive app_op_t : Type where
| Insert (ch : ℕ) (after : OpId)
| Remove (target : OpId)

/-- `(timestamp, replica id, app operation)`. The outer `(ts, rid)`
pair is the *new* opId being created by an Insert, or the replica
issuing the Remove. -/
abbrev op_t := ℕ × ℕ × app_op_t

/-- Two ops are "distinct" iff their timestamps differ. -/
@[simp]
def distinct_ops (op1 op2 : op_t) := Prod.fst op1 != Prod.fst op2

/-- Extract the replica id (the originator) of an op. -/
@[simp]
def get_rid (o : op_t) :=
match o with
| (_, (rid, _)) => rid

/-- Effect function.

* `Insert ch after` at `(ts, rid)`: writes three fresh per-opId
  entries to the maps. The new opId is `(ts, rid)`, the character is
  `ch`, the predecessor is `after`.
* `Remove target`: flips `deleted[target]` to `true`. The op's own
  `(ts, rid)` identifies the issuer but does not appear in state —
  each distinct replica that removes the same `target` writes the
  same `true` to the same slot (idempotent join).

Each case writes to exactly one key per component, and `Insert`'s
write is to a fresh opId (unique by `distinct_ops`), so ops from
distinct timestamps never write to the same `chars`/`afters` slot.
`Remove` writes are always to the same slot if they share a target,
but the value is idempotent. Convergence of `do_` follows. -/
@[simp]
def do_ (s : concrete_st) (o : op_t) : concrete_st :=
match o with
| (ts, (rid, app_op_t.Insert ch after)) =>
    (upd (Prod.fst s) (ts, rid) ch,
     upd (Prod.fst (Prod.snd s)) (ts, rid) after,
     Prod.snd (Prod.snd s))
| (_, (_, app_op_t.Remove target)) =>
    (Prod.fst s,
     Prod.fst (Prod.snd s),
     upd (Prod.snd (Prod.snd s)) target true)

inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

/-- Conflict resolution: `Either` for every pair. All ops are
lattice-merging writes; ordering is irrelevant at the `do_` level. -/
@[simp]
def rc (_o1 _o2 : op_t) := rc_res.Either

/-- Commutativity predicate used in `rc_non_comm`. -/
@[simp]
def commutes_with (o1 o2 : op_t) :=
    forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)

/-- Merge: componentwise per-key join on each of the three maps.

For each component:
  - union the two domains (covers every opId present in either side),
  - initialise that domain at the component's default,
  - replace each entry with the componentwise max of the two sides.

All three joins are commutative / associative / idempotent:
  - `max` on `ℕ` for char codes
  - `opid_max` (lexicographic) on `ℕ × ℕ` for afterIds
  - `max` on `Bool` (logical OR) for tombstones

so merge inherits the three lattice laws. -/
@[simp]
def merge (a b : concrete_st) : concrete_st :=
  let keys_c := union (domain (Prod.fst a)) (domain (Prod.fst b))
  let u_c := const_on keys_c 0
  let c := iter_upd (fun k _ => max (mysel_c (Prod.fst a) k) (mysel_c (Prod.fst b) k)) u_c
  let keys_a := union (domain (Prod.fst (Prod.snd a))) (domain (Prod.fst (Prod.snd b)))
  let u_a := const_on keys_a (0, 0)
  let af := iter_upd (fun k _ => opid_max (mysel_a (Prod.fst (Prod.snd a)) k)
                                           (mysel_a (Prod.fst (Prod.snd b)) k)) u_a
  let keys_d := union (domain (Prod.snd (Prod.snd a))) (domain (Prod.snd (Prod.snd b)))
  let u_d := const_on keys_d false
  let d := iter_upd (fun k _ => max (mysel_d (Prod.snd (Prod.snd a)) k)
                                     (mysel_d (Prod.snd (Prod.snd b)) k)) u_d
  (c, af, d)

set_option maxHeartbeats 0


theorem rc_non_comm (o1: op_t) (o2: op_t):
distinct_ops o1 o2 ∧ get_rid o1 != get_rid o2
→
(rc o1 o2 = rc_res.Either ↔ commutes_with o1 o2) := by
  intro h_distinct
  simp [commutes_with]
  rcases o1 with ⟨_, _, _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _⟩ <;>
    simp +decide [*] at h_distinct ⊢
  all_goals generalize_proofs at *
  all_goals grind +ring


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
  rcases o1 with ⟨_, _, _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _⟩ <;>
    simp +decide [*] at h_rid ⊢
  all_goals generalize_proofs at *
  all_goals grind +ring


theorem ind_lca_2op (l: concrete_st) (o1 o2 ol: op_t) :
 ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ol ∧ distinct_ops o2 ol ∧
                    eq (merge (do_ l o1) (do_ l o2)) (do_ (merge l (do_ l o2)) o1)
→
 eq (merge (do_ (do_ l ol) o1) (do_ (do_ l ol) o2)) (do_ (merge (do_ l ol) (do_ (do_ l ol) o2)) o1)
:= by
  rcases o1 with ⟨_, _, _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _⟩ <;>
    rcases ol with ⟨_, _, _ | _⟩ <;> simp +decide [*] at *
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
  rcases o1 with ⟨_, _, _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _⟩ <;>
    rcases o1' with ⟨_, _, _ | _⟩ <;> simp +decide [*] at *
  all_goals grind


theorem base_1op (o1:op_t) :
eq (merge (do_ init_st o1) init_st) (do_ (merge init_st init_st) o1) := by
  rcases o1 with ⟨_, _, _ | _⟩ <;> simp +decide [*] at *
  all_goals generalize_proofs at *
  all_goals grind +ring


theorem ind_lca_1op (l:concrete_st) (o1 ol:op_t) :
distinct_ops o1 ol ∧
                    eq (merge (do_ l o1) l) (do_ (merge l l) o1)
→
 eq (merge (do_ (do_ l ol) o1) (do_ l ol)) (do_ (merge (do_ l ol) (do_ l ol)) o1)
:= by
  rcases o1 with ⟨_, _, _ | _⟩ <;> rcases ol with ⟨_, _, _ | _⟩ <;>
    simp +decide [*] at *
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
  rcases o1 with ⟨_, _, _ | _⟩ <;> rcases o1' with ⟨_, _, _ | _⟩ <;>
    rcases ol with ⟨_, _, _ | _⟩ <;> simp +decide [*] at *
  all_goals grind


theorem ind_right_1op (a b: concrete_st) (o2 o2' ol:op_t) :
 distinct_ops o2 o2' ∧ distinct_ops o2 ol ∧ distinct_ops o2' ol ∧
                    eq (merge (do_ a ol) (do_ b o2)) (do_ (merge (do_ a ol) b) o2)
→
 eq (merge (do_ a ol) (do_ (do_ b o2') o2)) (do_ (merge (do_ a ol) (do_ b o2')) o2)
:= by
  rcases o2 with ⟨_, _, _ | _⟩ <;> rcases o2' with ⟨_, _, _ | _⟩ <;>
    rcases ol with ⟨_, _, _ | _⟩ <;> simp +decide [*] at *
  all_goals grind


theorem lem_0op (a b:concrete_st) (ol:op_t) :
eq (merge (do_ a ol) (do_ b ol)) (do_ (merge a b) ol) := by
  rcases ol with ⟨_, _, _ | _⟩ <;> simp +decide [*] at *
  all_goals grind
