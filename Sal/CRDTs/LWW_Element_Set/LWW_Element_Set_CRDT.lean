
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
# LWW-Element-Set: state-based CRDT

Last-Writer-Wins set using two timestamp maps: per-element "latest add
timestamp" and per-element "latest remove timestamp". An element is
live iff its max add-ts strictly exceeds its max remove-ts; ties favour
the remove (a conservative choice, the classical LWW-Set lets this
convention vary).

Merge is per-element max on each of the two maps (grow-only on both).
All ops commute (`rc := Either`) because `max` is idempotent-
commutative regardless of key, value, or which replica wrote.

Contrast with `OR_Set_CRDT`: LWW-Element-Set uses timestamps to decide
visibility, while OR-Set uses per-add tags and tombstones. LWW is
simpler but requires some reasonable clock, concurrent writes at the
same timestamp are resolved by the add-vs-remove tiebreak policy
encoded above.
-/

/-- Σ = (addTs, remTs): per-element latest-add / latest-remove timestamps. -/
@[simp] abbrev concrete_st := map ℕ ℕ × map ℕ ℕ

/-- Zero-default lookup. `0` means "never written". -/
@[simp]
def mysel (s: map ℕ ℕ) (k: ℕ) : ℕ :=
if (contains s k) then (sel s k) else 0

/-- Initial state: both maps empty. -/
@[simp]
def init_st : concrete_st:= (const_on empty 0, const_on empty 0)

/-- Pointwise equality on both components. -/
@[simp]
def eq (a b: concrete_st) :=
(forall id, (contains (Prod.fst a) id = contains (Prod.fst b) id) ∧ (mysel (Prod.fst a) id = mysel (Prod.fst b) id)) ∧
(forall id, (contains (Prod.snd a) id = contains (Prod.snd b) id) ∧ (mysel (Prod.snd a) id = mysel (Prod.snd b) id))


/-- `Add id` and `Remove id` each stamp the current `ts` into the
element's slot on the appropriate map. -/
inductive app_op_t : Type where
| Add (id : ℕ)
| Remove (id : ℕ)

abbrev op_t:= ℕ × ℕ × app_op_t

@[simp]
def distinct_ops (op1 op2 : op_t) := Prod.fst op1 != Prod.fst op2

@[simp]
def get_rid (o : op_t) :=
match o with
| (_, (rid, _)) => rid

/-- Effect: update the per-element latest-add or latest-remove ts by
taking `max` with the incoming `ts`. `ts` is globally unique (via
`distinct_ops`) but we still take max to stay commutative under
re-delivery. -/
@[simp]
def do_ (s: concrete_st) (o: op_t) : concrete_st :=
match o with
| (ts, (_, app_op_t.Add id))    => (upd (Prod.fst s) id (max (mysel (Prod.fst s) id) ts), Prod.snd s)
| (ts, (_, app_op_t.Remove id)) => (Prod.fst s, upd (Prod.snd s) id (max (mysel (Prod.snd s) id) ts))

inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

/-- `rc := Either`: `max` is idempotent-commutative so any two ops
commute at the state level regardless of kind or element. -/
@[simp]
def rc (_o1 _o2 : op_t) := rc_res.Either

@[simp]
def commutes_with (o1 o2 : op_t) :=
    forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)

/-- Merge: per-key max on each of the two maps. -/
@[simp]
def merge (a b: concrete_st) : concrete_st :=
let keys1 := union (domain (Prod.fst a)) (domain (Prod.fst b))
let u1 := const_on keys1 0
let m1 := iter_upd (fun k _ => max (mysel (Prod.fst a) k) (mysel (Prod.fst b) k)) u1
let keys2 := union (domain (Prod.snd a)) (domain (Prod.snd b))
let u2 := const_on keys2 0
let m2 := iter_upd (fun k _ => max (mysel (Prod.snd a) k) (mysel (Prod.snd b) k)) u2
(m1, m2)

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
  -- Direct proof (PN-Counter idiom).
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
  rcases o1 with ⟨_, _, _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _⟩ <;>
    rcases o1' with ⟨_, _, _ | _⟩ <;> simp +decide [*] at *
  all_goals grind



theorem base_1op (o1:op_t) :
eq (merge (do_ init_st o1) init_st) (do_ (merge init_st init_st) o1) := by
  rcases o1 with ⟨_, _, _ | _⟩ <;>
    refine ⟨?_, ?_⟩ <;> intro k <;>
    simp +decide [*]
  all_goals grind


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
