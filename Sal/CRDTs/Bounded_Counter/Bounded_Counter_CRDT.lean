
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
# Bounded Counter CRDT (Sypytkowski 2019)

## What this is

A state-based CRDT for a counter whose value is constrained never to
drop below zero (or, symmetrically, above a maximum). The counter is
distributed across a set of replicas; each replica has a local
"quota" (its share of the counter's current value) and may freely
`Inc` (increment) or `Dec` (decrement) within its quota. To avoid
exhaustion, replicas can **transfer** quota between themselves without
waiting for any coordination.

## Provenance

This is a Lean formalisation of the state-based Bounded Counter CRDT
described by Bartosz Sypytkowski at
<https://www.bartoszsypytkowski.com/state-based-crdts-bounded-counter/>.
The underlying design appears in the CRDTs-for-distributed-counters
line of work, most concretely in:

  Balegas, Duarte, Ferreira, Rodrigues, Preguiça, Najafzadeh,
  Shapiro. *Putting Consistency back into Eventual Consistency*,
  EuroSys 2015.

## Design

State: `concrete_st = map ℕ Int × map ℕ Int × map (ℕ × ℕ) Int`.

Three components, each grow-only per-key:

* `incs : map ℕ Int`, per-replica increment counts, keyed by replica id.
* `decs : map ℕ Int`, per-replica decrement counts, keyed by replica id.
* `transfers : map (ℕ × ℕ) Int`, cumulative quota transferred between
  pairs of replicas, keyed by `(sender_rid, receiver_rid)`.

Each replica only ever writes to its own `incs[rid]` / `decs[rid]`
slot, and to `transfers[(rid, _)]` slots whose *first* coordinate is
its own rid. That per-replica locality is what makes `do_` commute.

`quota(rid) = Σ_k incs[k] − Σ_k decs[k]
              + Σ_{(s,rid) ∈ dom} transfers[(s,rid)]
              − Σ_{(rid,r) ∈ dom} transfers[(rid,r)]`

i.e. the counter's net value plus net transfers into `rid`. The
"bounded" semantics is a **client-side predicate**, a replica
refuses to emit `Dec` or `Transfer` if its `quota < amount`. The
client check is **not** encoded in `do_` (which must be total for the
SAL framework); it is a separate safety property not verified by the
24 RA-linearizability VCs. The VCs verify convergence; the bound is
enforced operationally by well-behaved clients.

Operations (`app_op_t`):

* `Inc`                         increments `incs[rid]` by 1.
* `Dec`                         increments `decs[rid]` by 1.
* `Transfer (receiver : ℕ)`     increments `transfers[(rid, receiver)]` by 1.

All three write to a single, per-replica-addressed map slot. Ops
from distinct replicas therefore never touch the same slot, so
`do_` composition commutes under `distinct_ops ∧ get_rid ≠`.

Merge: componentwise, per-key max on each of the three maps. `max`
is commutative / associative / idempotent on `Int`; each component
is a join-semilattice; merge inherits those three properties.

## Relationship to existing CRDTs

* Extends `PN_Counter_CRDT` (pair of per-replica maps) by a third
  per-replica-pair map for transfers.
* Structurally identical to `Shopping_Cart_CRDT`'s two-map
  componentwise-max merge, just with three components and an extra
  `Transfer` op.

## Deliberate omissions

* **No quota check in `do_`.** As explained above, the bound is a
  client-side invariant.
* **No receipts.** A `Transfer` op from `A` to `B` increments
  `transfers[(A, B)]`; there is no corresponding "acknowledged by B"
  state. B's quota *automatically* reflects the transfer after merge.
* **Amount payloads are unit.** Each `Inc` / `Dec` / `Transfer` moves
  one unit; issuing N operations moves N units. Matches the
  convention used by `PN_Counter_CRDT` in this repo.
-/

/-- State: `(incs, decs, transfers)`. First two map replica-id to
per-replica increment/decrement counts; the third maps
`(sender, receiver)` replica pairs to cumulative transferred quota. -/
@[simp] abbrev concrete_st := map ℕ Int × map ℕ Int × map (ℕ × ℕ) Int

/-- Zero-default lookup on the scalar-keyed counter maps. -/
@[simp]
def mysel (s: map ℕ Int) (k: ℕ) : Int :=
if (contains s k) then (sel s k) else 0

/-- Zero-default lookup on the pair-keyed transfers map. -/
@[simp]
def mysel_t (s: map (ℕ × ℕ) Int) (k: ℕ × ℕ) : Int :=
if (contains s k) then (sel s k) else 0

/-- Initial state: all three maps empty. No replica has issued any op. -/
@[simp]
def init_st : concrete_st :=
  (const_on empty 0, const_on empty 0, const_on empty 0)

/-- Pointwise state equality: three ∀-conjuncts, one per component,
each asserting membership and value agreement. -/
@[simp]
def eq (a b: concrete_st) :=
  (forall id, (contains (Prod.fst a) id = contains (Prod.fst b) id) ∧
              (mysel (Prod.fst a) id = mysel (Prod.fst b) id)) ∧
  (forall id, (contains (Prod.fst (Prod.snd a)) id = contains (Prod.fst (Prod.snd b)) id) ∧
              (mysel (Prod.fst (Prod.snd a)) id = mysel (Prod.fst (Prod.snd b)) id)) ∧
  (forall p, (contains (Prod.snd (Prod.snd a)) p = contains (Prod.snd (Prod.snd b)) p) ∧
             (mysel_t (Prod.snd (Prod.snd a)) p = mysel_t (Prod.snd (Prod.snd b)) p))

/-- User-level operations: unit-increment PN counter ops plus a
`Transfer` carrying its receiver's replica id. The sender is the op's
outer `rid`. -/
inductive app_op_t : Type where
| Inc
| Dec
| Transfer (receiver : ℕ)

/-- `(timestamp, replica id, app operation)`. Timestamps are globally
unique under `distinct_ops`. -/
abbrev op_t := ℕ × ℕ × app_op_t

/-- Two ops are "distinct" iff their timestamps differ. -/
@[simp]
def distinct_ops (op1 op2 : op_t) := Prod.fst op1 != Prod.fst op2

/-- Extract the replica id (the sender) of an op. -/
@[simp]
def get_rid (o : op_t) :=
match o with
| (_, (rid, _)) => rid

/-- Effect function.

* `Inc` at replica `rid`: increments `incs[rid]` by 1.
* `Dec` at replica `rid`: increments `decs[rid]` by 1.
* `Transfer receiver` at replica `rid`: increments
  `transfers[(rid, receiver)]` by 1.

Each case touches exactly one slot in exactly one of the three maps.
The slot is partitioned by `rid` in the first two cases and by
`(rid, _)` in the third, so ops from distinct replicas (different
first coordinate) never collide. -/
@[simp]
def do_ (s: concrete_st) (o: op_t) : concrete_st :=
match o with
| (_, (rid, app_op_t.Inc))            =>
    (upd (Prod.fst s) rid (mysel (Prod.fst s) rid + 1),
     Prod.fst (Prod.snd s),
     Prod.snd (Prod.snd s))
| (_, (rid, app_op_t.Dec))            =>
    (Prod.fst s,
     upd (Prod.fst (Prod.snd s)) rid (mysel (Prod.fst (Prod.snd s)) rid + 1),
     Prod.snd (Prod.snd s))
| (_, (rid, app_op_t.Transfer recv))  =>
    (Prod.fst s,
     Prod.fst (Prod.snd s),
     upd (Prod.snd (Prod.snd s)) (rid, recv)
         (mysel_t (Prod.snd (Prod.snd s)) (rid, recv) + 1))

inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

/-- Conflict resolution: `Either` for every pair. All ops are
per-replica writes to disjoint slots; any two ops from distinct
replicas commute at the `do_` level. -/
@[simp]
def rc (_o1 _o2 : op_t) := rc_res.Either

/-- Commutativity predicate used in `rc_non_comm`. -/
@[simp]
def commutes_with (o1 o2 : op_t) :=
    forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)

/-- Merge: componentwise per-key `max` on each of the three maps.

For each component:
  - union the two domains (covers every key present in either side),
  - initialise that domain at `0`,
  - replace each entry with `max(mysel a k, mysel b k)`.

`max` is commutative / associative / idempotent on `Int`, so each
component is a join-semilattice and merge inherits the three
properties. -/
@[simp]
def merge (a b: concrete_st) : concrete_st :=
  let keys_i := union (domain (Prod.fst a)) (domain (Prod.fst b))
  let u_i := const_on keys_i 0
  let i := iter_upd (fun k _ => max (mysel (Prod.fst a) k) (mysel (Prod.fst b) k)) u_i
  let keys_d := union (domain (Prod.fst (Prod.snd a))) (domain (Prod.fst (Prod.snd b)))
  let u_d := const_on keys_d 0
  let d := iter_upd (fun k _ => max (mysel (Prod.fst (Prod.snd a)) k)
                                     (mysel (Prod.fst (Prod.snd b)) k)) u_d
  let keys_t := union (domain (Prod.snd (Prod.snd a))) (domain (Prod.snd (Prod.snd b)))
  let u_t := const_on keys_t 0
  let t := iter_upd (fun p _ => max (mysel_t (Prod.snd (Prod.snd a)) p)
                                     (mysel_t (Prod.snd (Prod.snd b)) p)) u_t
  (i, d, t)

set_option maxHeartbeats 0


theorem rc_non_comm (o1: op_t) (o2: op_t):
distinct_ops o1 o2 ∧ get_rid o1 != get_rid o2
→
(rc o1 o2 = rc_res.Either ↔ commutes_with o1 o2) := by
  intro h_distinct
  simp [commutes_with]
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _⟩ <;>
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
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _⟩ <;>
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
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _⟩ <;>
    rcases ol with ⟨_, _, _ | _ | _⟩ <;> simp +decide [*] at *
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
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _⟩ <;>
    rcases o1' with ⟨_, _, _ | _ | _⟩ <;> simp +decide [*] at *
  all_goals grind


theorem base_1op (o1:op_t) :
eq (merge (do_ init_st o1) init_st) (do_ (merge init_st init_st) o1) := by
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;> simp +decide [*] at *
  all_goals generalize_proofs at *
  all_goals grind +ring


theorem ind_lca_1op (l:concrete_st) (o1 ol:op_t) :
distinct_ops o1 ol ∧
                    eq (merge (do_ l o1) l) (do_ (merge l l) o1)
→
 eq (merge (do_ (do_ l ol) o1) (do_ l ol)) (do_ (merge (do_ l ol) (do_ l ol)) o1)
:= by
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;> rcases ol with ⟨_, _, _ | _ | _⟩ <;>
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
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;> rcases o1' with ⟨_, _, _ | _ | _⟩ <;>
    rcases ol with ⟨_, _, _ | _ | _⟩ <;> simp +decide [*] at *
  all_goals grind


theorem ind_right_1op (a b: concrete_st) (o2 o2' ol:op_t) :
 distinct_ops o2 o2' ∧ distinct_ops o2 ol ∧ distinct_ops o2' ol ∧
                    eq (merge (do_ a ol) (do_ b o2)) (do_ (merge (do_ a ol) b) o2)
→
 eq (merge (do_ a ol) (do_ (do_ b o2') o2)) (do_ (merge (do_ a ol) (do_ b o2')) o2)
:= by
  rcases o2 with ⟨_, _, _ | _ | _⟩ <;> rcases o2' with ⟨_, _, _ | _ | _⟩ <;>
    rcases ol with ⟨_, _, _ | _ | _⟩ <;> simp +decide [*] at *
  all_goals grind


theorem lem_0op (a b:concrete_st) (ol:op_t) :
eq (merge (do_ a ol) (do_ b ol)) (do_ (merge a b) ol) := by
  rcases ol with ⟨_, _, _ | _ | _⟩ <;> simp +decide [*] at *
  all_goals grind
