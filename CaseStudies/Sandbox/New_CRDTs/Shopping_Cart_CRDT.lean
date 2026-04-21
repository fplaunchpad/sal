
import Std.Tactic.BVDecide
import CaseStudies.Interfaces.Map_Extended
import CaseStudies.Tactics.Sal

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
# Shopping Cart CRDT (composite-key PN-counter)

## What this is

A state-based CRDT modelling a shared shopping cart: multiple replicas
concurrently `Add` and `Remove` products from a single cart, merges are
associative / commutative / idempotent, and the observable "quantity of
product p" converges once all replicas see all updates.

## Provenance

This implementation is **original**: a direct generalisation of
`PN_Counter_CRDT.lean` (whose state is `map ℕ Int × map ℕ Int` — per-
replica increments and decrements of a single scalar counter) to the
multi-product setting, by widening the key from `ℕ` (replica id) to
`ℕ × ℕ` (replica id paired with product id).

Shopping carts are a standard CRDT motivating example (e.g. Shapiro,
Preguiça, Baquero, Zawirski, "A Comprehensive Study of CRDTs", 2011),
but published treatments usually sketch them as "a map from product to
PN-counter" without giving a concrete state-based
`⟨Σ, σ₀, do, merge, rc⟩` formulation. This file commits to one such
formulation. A more literal name would be "Composite-Key PN-Counter";
"Shopping Cart" is kept because the semantics match how shopping carts
are usually described informally.

## Design

State: `concrete_st = map (ℕ × ℕ) Int × map (ℕ × ℕ) Int`, where a key
`(rid, pid)` is `(replica id, product id)`. The first map stores
**per-replica add counts** — `adds[(rid, pid)]` = how many times
replica `rid` has added product `pid`. The second map stores
**per-replica remove counts** symmetrically. Both start empty.

Operations (`app_op_t`):
  * `Add pid`      at replica `rid`: increments `adds[(rid, pid)]`.
  * `Remove pid`   at replica `rid`: increments `removes[(rid, pid)]`.

Each replica only ever writes to slots whose first component equals its
own `rid`. So two operations with distinct replica ids ALWAYS touch
disjoint keys in whichever map they modify — that is the invariant
that makes `do_` commutative under `distinct_ops ∧ get_rid distinct`.

Merge takes the componentwise per-key max of both maps. Since each
replica's slot at `(rid, pid)` is monotonically increasing (only that
replica ever increments it, and never decrements it), max picks the
more up-to-date value. `max` is commutative / associative / idempotent
on `Int`, so merge is too.

## How to read the state

The total quantity of product `pid` is a **client-side projection**:
```
  quantity(pid) = Σ over all rid of (adds[(rid, pid)] - removes[(rid, pid)])
```
The projection is not part of the CRDT definition or the 24 VCs — the
CRDT just has to converge on the underlying `(adds, removes)` state.

## Deliberate omissions

* **No tombstones / causal remove.** A `Remove pid` at a replica that
  has seen no `Add pid` still records "replica rid has removed pid once"
  and reduces the eventual quantity by 1 once concurrent adds arrive.
  This matches PN-counter's behaviour and diverges from OR-Set-flavoured
  shopping carts that would require an add to be observed before it can
  be cancelled.
* **No negative-quantity guard.** `quantity(pid)` can go negative. A
  real cart UI would clamp at 0 client-side; we do not clamp here
  because that would break commutativity of `do_`.
* **No per-item attributes** (price, name, metadata). Just the count.

## Relationship to the paper's 13 benchmarks

The paper (Table 2) reports PN-Counter CRDT as 16 DG + 2 LB + 6 ITP.
Shopping_Cart has the same verification profile structurally — 18/24
VCs close via `sal` (including a PN-style direct proof on
`rc_non_comm`), and the same 6 `ind_*` / `lem_0op` VCs that need
Harmonic-style intermediate lemmas in PN-Counter are sorried here.
-/

/-- `concrete_st` is a pair of integer-valued maps, both keyed by
`(replica id, product id)` pairs. The left map holds per-`(rid, pid)`
add counts; the right map holds per-`(rid, pid)` remove counts. See
the file-level docstring for the design rationale. -/
@[simp] abbrev concrete_st := map (ℕ × ℕ) Int × map (ℕ × ℕ) Int

/-- Total lookup: value at key `k`, or `0` if `k` is not in the
domain. Used in `eq`, `do_`, and `merge` so that comparisons and
updates over "missing" keys behave as if they held `0` — matches the
PN-counter convention that an uninitialised replica slot contributes
nothing to the total. -/
@[simp]
def mysel (s: map (ℕ × ℕ) Int) (k: ℕ × ℕ) : Int :=
if (contains s k) then (sel s k) else 0

/-- Initial state: both maps empty. No replica has added or removed
any product yet. -/
@[simp]
def init_st : concrete_st := (const_on empty 0, const_on empty 0)

/-- State equality is pointwise: two states are equal iff, for every
possible `(rid, pid)` key, both maps agree on membership AND on value.
Written as a conjunction of two ∀ rather than a single one over the
product so that each map's pointwise equality can be reasoned about
independently. -/
@[simp]
def eq (a b: concrete_st) :=
(forall id, (contains (Prod.fst a) id = contains (Prod.fst b) id) ∧ (mysel (Prod.fst a) id = mysel (Prod.fst b) id)) ∧
(forall id, (contains (Prod.snd a) id = contains (Prod.snd b) id) ∧ (mysel (Prod.snd a) id = mysel (Prod.snd b) id))


/-- The two user-level operations. Both take a product id; the
replica id is carried in the surrounding `op_t` wrapper and attached
at `do_` time. -/
inductive app_op_t : Type where
| Add (pid : ℕ)
| Remove (pid : ℕ)

/-- `(timestamp, replica id, app operation)`. Timestamp is globally
unique under the paper's `distinct_ops` assumption. -/
abbrev op_t := ℕ × ℕ × app_op_t

/-- Two ops are "distinct" iff their timestamps differ — the paper's
global-uniqueness assumption on op ids. -/
@[simp]
def distinct_ops (op1 op2 : op_t) := Prod.fst op1 != Prod.fst op2

/-- Extract the replica id of an op. The `rid` is what partitions
writes in `do_` so that two ops from different replicas write to
disjoint `(rid, pid)` slots. -/
@[simp]
def get_rid (o : op_t) :=
match o with
| (_, (rid, _)) => rid

/-- The effect function.

* `Add pid` at replica `rid`: read the current add-count at
  `(rid, pid)` (zero if absent), add 1, store it back. The remove
  map is untouched.
* `Remove pid` at replica `rid`: symmetric — increment the remove
  count at `(rid, pid)`, leave the add map untouched.

Both cases are pure increments at exactly one `(rid, pid)` slot. This
is what makes `do_` commute: two ops at different replicas write to
different keys (different first component), and `Add` vs `Remove`
touch different maps. -/
@[simp]
def do_ (s: concrete_st) (o: op_t) : concrete_st :=
match o with
| (_, (rid, app_op_t.Add pid))    => (upd (Prod.fst s) (rid, pid) (mysel (Prod.fst s) (rid, pid) + 1), Prod.snd s)
| (_, (rid, app_op_t.Remove pid)) => (Prod.fst s, upd (Prod.snd s) (rid, pid) (mysel (Prod.snd s) (rid, pid) + 1))

/-- Conflict resolution result, per the paper's framework. For this
CRDT all op pairs reduce to `Either` — see `rc` below. -/
inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

/-- Conflict resolution: always `Either`.

Increments at distinct replica slots commute, as do `Add` vs `Remove`
(they touch different maps entirely). Under `distinct_ops ∧ get_rid
distinct` every pair of operations modifies disjoint `(rid, pid)` slots
and therefore commutes without any imposed ordering. -/
@[simp]
def rc (_o1 _o2 : op_t) := rc_res.Either

/-- The RA-linearizability VC framework's notion of commutativity: two
ops commute iff applying them in either order yields equal states, for
every starting state. -/
@[simp]
def commutes_with (o1 o2 : op_t) :=
    forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)

/-- Merge: componentwise, per-key max on both maps.

Union the two domains so that every key present in either input is
covered, then take the max at each key. For each `(rid, pid)`:
  - If only one side has the key, that side's value wins (the other
    reads as `0` via `mysel`).
  - If both sides have it, the later-seen value wins (since the slot
    is monotonically increasing under `do_`, the larger is newer).

`max` is commutative, associative, and idempotent on `Int`, so merge
inherits all three properties — which is exactly what the lattice
proof of convergence needs. -/
@[simp]
def merge (a b: concrete_st) : concrete_st :=
let keys_f := union (domain (Prod.fst a)) (domain (Prod.fst b))
let u_f := const_on keys_f 0
let f := iter_upd (fun k v => max (mysel (Prod.fst a) k) (mysel (Prod.fst b) k)) u_f
let keys_s := union (domain (Prod.snd a)) (domain (Prod.snd b))
let u_s := const_on keys_s 0
let s := iter_upd (fun k v => max (mysel (Prod.snd a) k) (mysel (Prod.snd b) k)) u_s
(f,s)

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
  -- Proof produced by Aristotle (Harmonic), 2026-04-21.
  unfold rc distinct_ops eq
  rintro ⟨ h1, h2, h3, h4, h5, h6, h7 ⟩
  constructor
  · unfold do_
    rcases o1 with ⟨ _, _, _ | _ ⟩ <;> rcases o2 with ⟨ _, _, _ | _ ⟩ <;>
      rcases ol with ⟨ _, _, _ | _ ⟩ <;> simp +decide [ * ] at *
    · grind
    · grind
    · grind
    · exact h6
  · intro id
    unfold do_ at *
    rcases o1 with ⟨ _, _, _ | _ ⟩ <;> rcases o2 with ⟨ _, _, _ | _ ⟩ <;>
      rcases ol with ⟨ _, _, _ | _ ⟩ <;> simp +decide at h2 h3 h4 h5 ⊢
    · grind
    · grind
    · grind
    · grind




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
 eq (merge (do_ (do_ (do_ a ob) ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ (do_ a ob) ol) (do_ (do_ b ol) o2)) o1) :=
 by sal

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
  -- Proof produced by Aristotle (Harmonic), 2026-04-21.
  unfold rc distinct_ops get_rid
  unfold eq
  intro h
  constructor <;> intro id
  · unfold do_ merge
    rcases o1 with ⟨ _, _, _ | _ ⟩ <;> rcases o2 with ⟨ _, _, _ | _ ⟩ <;>
      rcases o1' with ⟨ _, _, _ | _ ⟩ <;> simp +decide [ * ] at h ⊢
    · grind
    · grind
    · grind
    · grind
  · unfold do_ merge
    rcases o1 with ⟨ _, _, _ | _ ⟩ <;> rcases o2 with ⟨ _, _, _ | _ ⟩ <;>
      rcases o1' with ⟨ _, _, _ | _ ⟩ <;> simp +decide [ * ] at h ⊢
    · grind
    · grind
    · grind
    · grind



theorem base_1op (o1:op_t) :
eq (merge (do_ init_st o1) init_st) (do_ (merge init_st init_st) o1) :=
by sal


theorem ind_lca_1op (l:concrete_st) (o1 ol:op_t) :
distinct_ops o1 ol ∧
                    eq (merge (do_ l o1) l) (do_ (merge l l) o1)
→
 eq (merge (do_ (do_ l ol) o1) (do_ l ol)) (do_ (merge (do_ l ol) (do_ l ol)) o1)
:= by
  -- Proof produced by Aristotle (Harmonic), 2026-04-21.
  intro h
  rcases o1 with ⟨ _, _, _ | _ ⟩ <;> rcases ol with ⟨ _, _, _ | _ ⟩ <;>
    simp +decide [ *, eq ] at *
  · grind +ring
  · grind +ring
  · grind
  · grind



theorem inter_right_base_1op (a b :concrete_st) (o1 ob ol:op_t) :
 (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops ob ol ∧
                    ((rc ob o1) = rc_res.Fst_then_snd → eq (merge (do_ a o1) (do_ b ob)) (do_ (merge a (do_ b ob)) o1)) ∧
                    eq (merge (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ a ol) (do_ b ol)) o1)
→  eq (merge (do_ (do_ a ol) o1) (do_ (do_ b ob) ol)) (do_ (merge (do_ a ol) (do_ (do_ b ob) ol)) o1) :=
by sal

theorem inter_left_base_1op (a b:concrete_st) (o1 ob ol:op_t) :
 (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops ob ol ∧
                    eq (merge (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ a ol) (do_ b ol)) o1)
→
eq (merge (do_ (do_ (do_ a ob) ol) o1) (do_ b ol)) (do_ (merge (do_ (do_ a ob) ol) (do_ b ol)) o1)
:=
by sal

theorem inter_right_1op (a b:concrete_st) (o1 ob ol o:op_t) :
 (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    (¬ ((rc o ob) = rc_res.Either) ∨ (rc o ol) = rc_res.Fst_then_snd) ∧
                    distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧
                    get_rid o != get_rid ol ∧
                    eq (merge (do_ (do_ a ol) o1) (do_ (do_ b ob) ol)) (do_ (merge (do_ a ol) (do_ (do_ b ob) ol)) o1)
→
 eq (merge (do_ (do_ a ol) o1) (do_ (do_ (do_ b o) ob) ol)) (do_ (merge (do_ a ol) (do_ (do_ (do_ b o) ob) ol)) o1) :=
 by sal


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
  -- Proof produced by Aristotle (Harmonic), 2026-04-21.
  rcases o1 with ⟨ _, _, _ | _ ⟩ <;> rcases o1' with ⟨ _, _, _ | _ ⟩ <;>
    rcases ol with ⟨ _, _, _ | _ ⟩ <;> simp +decide [ * ] at *
  · grind
  · grind
  · grind +ring
  · grind



theorem ind_right_1op (a b: concrete_st) (o2 o2' ol:op_t) :
 distinct_ops o2 o2' ∧ distinct_ops o2 ol ∧ distinct_ops o2' ol ∧
                    eq (merge (do_ a ol) (do_ b o2)) (do_ (merge (do_ a ol) b) o2)
→
 eq (merge (do_ a ol) (do_ (do_ b o2') o2)) (do_ (merge (do_ a ol) (do_ b o2')) o2)
:= by
  rcases o2 with ⟨ _, _, _ | _ ⟩ <;> rcases o2' with ⟨ _, _, _ | _ ⟩ <;>
    rcases ol with ⟨ _, _, _ | _ ⟩ <;> simp +decide [ * ] at *
  · grind
  · grind
  · grind +ring
  · grind



theorem lem_0op (a b:concrete_st) (ol:op_t) :
eq (merge (do_ a ol) (do_ b ol)) (do_ (merge a b) ol) := by
  -- Proof produced by Aristotle (Harmonic), 2026-04-21.
  rcases ol with ⟨ _, _, ol ⟩
  cases ol <;> simp +decide [ eq, do_, merge ]
  · grind
  · grind
