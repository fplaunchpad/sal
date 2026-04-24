
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
# PN-Counter — state-based CRDT

A counter that supports both `Inc` and `Dec`. Implemented as two
G-counters glued together — one tracking per-replica increments, one
tracking per-replica decrements — because a single `max`-merged map
can't unambiguously distinguish "R0 did 3 incs" from "R0 did 2 incs
then 1 dec" once merges fold the state.

State is `(incs, decs)` where both components are `map ℕ Int`
(replica id → count). The observable value is `Σ incs − Σ decs`.
Merge takes per-key max on each component (grow-only on both sides,
just like `Increment_Only_Counter_CRDT`).

All ops commute (`rc := Either`) because every effect writes to the
sender's own slot in one of the two maps.
-/

/-- Σ = (incs, decs), each a map from replica id to per-replica count. -/
@[simp] abbrev concrete_st := map ℕ Int × map ℕ Int

/-- Zero-default lookup. -/
@[simp]
def mysel (s: map ℕ Int) (k: ℕ) : Int :=
if (contains s k) then (sel s k) else 0

/-- Initial state: both maps empty. -/
@[simp]
def init_st : concrete_st:= (const_on empty 0, const_on empty 0)

/-- Pointwise equality on both components. -/
@[simp]
def eq (a b: concrete_st) :=
(forall id, (contains (Prod.fst a) id = contains (Prod.fst b) id) ∧ (mysel (Prod.fst a) id = mysel (Prod.fst b) id)) ∧
(forall id, (contains (Prod.snd a) id = contains (Prod.snd b) id) ∧ (mysel (Prod.snd a) id = mysel (Prod.snd b) id))


/-- `Inc` and `Dec` each bump the sender's slot by 1 in the appropriate
map. No payload; amount is always +1 (matches `Increment_Only_Counter`
convention — N ops move N units). -/
inductive app_op_t : Type where
| Inc
| Dec

abbrev op_t:= ℕ × ℕ × app_op_t

@[simp]
def distinct_ops (op1 op2 : op_t) := Prod.fst op1 != Prod.fst op2

@[simp]
def get_rid (o : op_t) :=
match o with
| (_, (rid, _)) => rid

/-- Effect: `Inc` at `rid` bumps `incs[rid]`; `Dec` bumps `decs[rid]`.
Each op touches one slot in one map; slots are partitioned by `rid`. -/
@[simp]
def do_ (s: concrete_st) (o: op_t) : concrete_st :=
match (Prod.snd o) with
| (r, app_op_t.Inc) => (upd (Prod.fst s) r (mysel (Prod.fst s) r + 1), Prod.snd s)
| (r, app_op_t.Dec) => (Prod.fst s, upd (Prod.snd s) r (mysel (Prod.snd s) r + 1))

inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

/-- `rc := Either`: ops from distinct replicas always touch disjoint
slots (partitioned by `rid` in one of the two maps), so state-level
ordering is irrelevant. -/
@[simp]
def rc (o1 o2 : op_t) := rc_res.Either

@[simp]
def commutes_with (o1 o2 : op_t) :=
    forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)

/-- Merge: per-slot max on each of the two component maps. Each is a
grow-only join-semilattice, so the product state is too. -/
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
 -- By definition of `commutes_with`, we need to show that for any state `s`, `do_ (do_ s o1) o2 = do_ (do_ s o2) o1`.
  intro h_distinct
  simp [commutes_with];
  rcases o1 with ⟨ _, _, _ | _ ⟩ <;> rcases o2 with ⟨ _, _, _ | _ ⟩ <;> simp +decide [ * ] at h_distinct ⊢
  all_goals generalize_proofs at *;
  · grind +ring;
  · grind +ring


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
  rcases o1 with ⟨_, _, _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _⟩ <;>
    refine ⟨?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind



/- Intermediate lemma proved by Harmonic-/

theorem lemma_merge_do_comm (s: concrete_st) (o1 o2: op_t) :
  get_rid o1 != get_rid o2 →
  eq (merge (do_ s o1) (do_ s o2)) (do_ (merge s (do_ s o2)) o1) := by
    -- By definition of merge and do_, we can show that the merge of the two states after applying o1 and o2 is equal to the merge of the states after applying o1 and o2 in a different order. This follows from the commutativity of the max function used in the merge.
    intros h_distinct
    simp [merge, do_, h_distinct];
    rcases o1 with ⟨ _, _, _ | _ ⟩ <;> rcases o2 with ⟨ _, _, _ | _ ⟩ <;> simp +decide [ * ] at h_distinct ⊢;
    · aesop;
    · aesop;
    · aesop;
    · intro id; by_cases hi : id = ‹ℕ› <;> by_cases hj : id = ‹ℕ› <;> simp +decide [ hi, hj, h_distinct ] ;
      · split_ifs <;> simp_all +decide [ max_comm ];
      · contradiction;
      · tauto;
      · tauto



@[simp]
def val_at (s: concrete_st) (o: op_t) : Int :=
  match o.2 with
  | (k, app_op_t.Inc) => mysel s.1 k
  | (k, app_op_t.Dec) => mysel s.2 k

lemma val_at_mono (s: concrete_st) (o o': op_t) :
  val_at s o ≤ val_at (do_ s o') o := by
    -- By definition of val_at, we know that val_at s o is either mysel s.1 (Prod.snd (Prod.snd o)) or mysel s.2 (Prod.snd (Prod.snd o)) depending on the type of o.
    cases' o with id rid op_type;
    -- By definition of do_, applying an operation that does not modify the value at the rid of o will not change the value.
    cases' o' with id' rid' op_type';
    -- By definition of val_at, we know that val_at s (id, rid) is either mysel s.1 rid (if op_type is Inc) or mysel s.2 rid (if op_type is Dec).
    cases' rid with rid op_type
    cases' rid' with rid' op_type';
    cases op_type <;> cases op_type' <;> simp +decide [ *, val_at ];
    · grind;
    · grind +ring

lemma merge_do_condition (a b: concrete_st) (o: op_t) :
  eq (merge (do_ a o) b) (do_ (merge a b) o) ↔ val_at a o ≥ val_at b o := by
    rcases o with ⟨ k, r, op ⟩;
    rcases op with ( _ | _ ) <;> simp +decide [ contains, sel, iter_upd, const_on, union, map.mk ];
    · grind;
    · grind

lemma val_at_do_self (s: concrete_st) (o: op_t) :
  val_at (do_ s o) o = val_at s o + 1 := by
    -- By definition of val_at, we know that val_at (do_ s o) o is the value of the operation o in the state after applying o.
    cases' o with op1 op2 k op;
    -- By definition of val_at, we know that val_at (do_ s o) o is the value of the operation o in the state after applying o. Since o is either Inc or Dec, we can split into these cases.
    cases' op2 with k op2;
    cases op2 <;> unfold val_at <;> simp +decide [ * ]


/- End Intermediate lemma proved by Harmonic-/


theorem ind_lca_2op (l: concrete_st) (o1 o2 ol: op_t) :
 ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ol ∧ distinct_ops o2 ol ∧
                    eq (merge (do_ l o1) (do_ l o2)) (do_ (merge l (do_ l o2)) o1)
→
 eq (merge (do_ (do_ l ol) o1) (do_ (do_ l ol) o2)) (do_ (merge (do_ l ol) (do_ (do_ l ol) o2)) o1)
:= by
intros h
apply lemma_merge_do_comm
exact h.2.1



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
 by simp

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
:=
by
  intro h
  rcases h with ⟨_, _, _, _, _, h_eq⟩
  rw [merge_do_condition] at h_eq
  rw [merge_do_condition]
  apply le_trans h_eq
  apply val_at_mono


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
:=
by
  -- By definition of merge, we can expand both sides of the equation.
  simp [eq, merge, do_] at *;
  -- By simplifying the match expressions and using the fact that addition is commutative, we can show that the two sides of the equation are equal. We'll handle each case separately.
  cases' o1.2 with r1 r2 hr1 hr2;
  -- By simplifying the match expressions and using the fact that addition is commutative, we can show that the two sides of the equation are equal. We'll handle each case separately and use the definitions of `do_` and `merge`.
  cases' r2 with r2 hr2;
  · -- Since addition is commutative, the order of the terms in the if statements doesn't matter. Therefore, the two expressions are equal.
    intros h1 h2 h3
    simp [add_comm, add_left_comm] at *;
    cases' ol.2 with r2 hr2;
    intro id; by_cases h4 : id = r1 <;> by_cases h5 : id = r2 <;> simp +decide [ h4, h5 ] ;
    · grind;
    · grind;
    · grind;
  · cases' ol.2 with r2 hr2 ; simp +decide [ * ] at *;
    intro h1 h2 id; specialize h2 id; split_ifs at h2 <;> simp_all +decide ;


theorem inter_right_base_1op (a b :concrete_st) (o1 ob ol:op_t) :
 (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops ob ol ∧
                    ((rc ob o1) = rc_res.Fst_then_snd → eq (merge (do_ a o1) (do_ b ob)) (do_ (merge a (do_ b ob)) o1)) ∧
                    eq (merge (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ a ol) (do_ b ol)) o1)
→  eq (merge (do_ (do_ a ol) o1) (do_ (do_ b ob) ol)) (do_ (merge (do_ a ol) (do_ (do_ b ob) ol)) o1) :=
by simp

theorem inter_left_base_1op (a b:concrete_st) (o1 ob ol:op_t) :
 (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops ob ol ∧
                    eq (merge (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ a ol) (do_ b ol)) o1)
→
eq (merge (do_ (do_ (do_ a ob) ol) o1) (do_ b ol)) (do_ (merge (do_ (do_ a ob) ol) (do_ b ol)) o1)
:=
by simp

theorem inter_right_1op (a b:concrete_st) (o1 ob ol o:op_t) :
 (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    (¬ ((rc o ob) = rc_res.Either) ∨ (rc o ol) = rc_res.Fst_then_snd) ∧
                    distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧
                    get_rid o != get_rid ol ∧
                    eq (merge (do_ (do_ a ol) o1) (do_ (do_ b ob) ol)) (do_ (merge (do_ a ol) (do_ (do_ b ob) ol)) o1)
→
 eq (merge (do_ (do_ a ol) o1) (do_ (do_ (do_ b o) ob) ol)) (do_ (merge (do_ a ol) (do_ (do_ (do_ b o) ob) ol)) o1) :=
 by simp


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
rcases h with ⟨_, _, _, h_eq⟩
rw [merge_do_condition] at h_eq
rw [merge_do_condition]
apply le_trans h_eq
apply val_at_mono


lemma merge_do_condition_right (a b: concrete_st) (o: op_t) :
  eq (merge a (do_ b o)) (do_ (merge a b) o) ↔ val_at b o ≥ val_at a o := by
    convert merge_do_condition b a o using 1;
    unfold merge do_;
    cases o.2;
    cases ‹app_op_t› <;> simp +decide [ *, union ];
    · grind;
    · grind


theorem ind_right_1op (a b: concrete_st) (o2 o2' ol:op_t) :
 distinct_ops o2 o2' ∧ distinct_ops o2 ol ∧ distinct_ops o2' ol ∧
                    eq (merge (do_ a ol) (do_ b o2)) (do_ (merge (do_ a ol) b) o2)
→
 eq (merge (do_ a ol) (do_ (do_ b o2') o2)) (do_ (merge (do_ a ol) (do_ b o2')) o2)
:= by
  intro h
  rcases h with ⟨_, _, _, h_eq⟩
  rw [merge_do_condition_right] at h_eq
  rw [merge_do_condition_right]
  apply le_trans h_eq
  apply val_at_mono



theorem lem_0op (a b:concrete_st) (ol:op_t) :
eq (merge (do_ a ol) (do_ b ol)) (do_ (merge a b) ol) := by sal
