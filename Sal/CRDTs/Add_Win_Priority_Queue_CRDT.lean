import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Std.Tactic.BVDecide

import Sal.Interfaces.Set_Extended
import Sal.Interfaces.Map_Extended
import Sal.Tactic.Sal


open Classical

/-!
# Add-Win Conflict-free Replicated Priority Queue (state-based adaptation)

State-based port of the Add-Win CRPQ from

    Yuqi Zhang, Lingzhi Ouyang, Yu Huang, Xiaoxing Ma.
    "Conflict-free Replicated Priority Queue: Design, Verification and
    Evaluation." Internetware 2023.  ACM 10.1145/3609437.3609452.

The paper is op-based (Algorithm 2, "payload A: set of (e, t, x, inc,
count) tuples; R: set of (e, t)"). We adapt it to Sal's state-based
`⟨Σ, σ₀, do, merge, rc⟩` model:

  concrete_st = A : map (ℕ × ℕ) ℕ        -- (elem, add_ts) → innate_value
                × I : set (ℕ × ℕ × ℤ)     -- (elem, inc_ts, amount)
                × R : set (ℕ × ℕ)         -- tombstoned (elem, add_ts)

and three operations: `Add elem value`, `Inc elem amount`, `Rmv elem`.

**Faithful translation of op-based prepare/effect.** The paper separates
`prepare` (at the originating replica, reads local A) from `effect`
(applied at every replica, a pure function of the effect payload). To
encode that in SAL's state-based `⟨Σ, σ₀, do, merge, rc⟩` model — which
has no separate prepare — we push prepare-time data INTO the op payload:
`Rmv` carries the tombstone snapshot `D ⊆ (ℕ × ℕ)` as a constructor
parameter. `do_` for Rmv then only unions `D` into `R` — a pure
pointwise-∨ that does not read the current A. This is what preserves
Add/Rmv commutativity at the `do_` level (and thereby `rc_non_comm` /
`base_2op`); an earlier version of this file computed the snapshot
inside `do_` and failed those VCs as a result.

The paper's `inc` similarly iterates `A \ R` at prepare-time. We
simplify: record each `inc` as a standalone `(elem, inc_ts, amount)`
tuple keyed by element only, not by specific `add_ts`. This changes
the per-record accumulation behaviour vs the paper, but preserves:
  - Add-Win resolution of add vs concurrent rmv (the prepare-time
    snapshot in Rmv's payload only tombstones records visible at the
    originating replica; adds at later timestamps or other replicas
    are preserved on merge).
  - Commutativity / associativity / idempotence of merge (all three
    components are grow-only sets/maps merged pointwise).
  - LWW semantics for the innate value (via the `(elem, add_ts)` keys
    on A, with `add_ts` globally unique per paper's distinct_ops).

**Read-side queries (not part of the 24 VCs).**
  - `lookup(e)` := ∃ (at : ℕ), contains A (e, at) ∧ ¬ R (e, at)
  - `innate(e)` := max over live add records' values (LWW by `add_ts`)
  - `acquired(e)` := Σ over inc records of `amount` (tied by elem)
  - `priority(e)` := innate(e) + acquired(e)

`rc o1 o2 := Either` — all operations commute under `distinct_ops`
(globally-unique ts makes add-record and inc-record keys unique;
Rmv's effect is a pointwise ∨ over R, which is idempotent-commutative).
-/

@[simp] abbrev concrete_st :=
  map (ℕ × ℕ) ℕ × set (ℕ × ℕ × ℤ) × set (ℕ × ℕ)

@[simp]
def mysel (s : map (ℕ × ℕ) ℕ) (k : ℕ × ℕ) : ℕ :=
  if (contains s k) then (sel s k) else 0

@[simp]
def init_st : concrete_st := (const_on empty 0, empty, empty)

@[simp]
def eq (a b : concrete_st) :=
  (forall k : ℕ × ℕ, (contains (Prod.fst a) k = contains (Prod.fst b) k) ∧
                     (mysel (Prod.fst a) k = mysel (Prod.fst b) k)) ∧
  (forall x : ℕ × ℕ × ℤ, (Prod.fst (Prod.snd a)) x = (Prod.fst (Prod.snd b)) x) ∧
  (forall x : ℕ × ℕ, (Prod.snd (Prod.snd a)) x = (Prod.snd (Prod.snd b)) x)

inductive app_op_t : Type where
| Add (elem : ℕ) (value : ℕ)
| Inc (elem : ℕ) (amount : ℤ)
| Rmv (elem : ℕ) (tombstones : set (ℕ × ℕ))

abbrev op_t := ℕ × ℕ × app_op_t

@[simp]
def distinct_ops (op1 op2 : op_t) := Prod.fst op1 != Prod.fst op2

@[simp]
def get_rid (o : op_t) :=
match o with
| (_, (rid, _)) => rid

@[simp]
def do_ (s : concrete_st) (o : op_t) : concrete_st :=
match o with
| (ts, (_, .Add elem value)) =>
    (upd (Prod.fst s) (elem, ts) value, Prod.fst (Prod.snd s), Prod.snd (Prod.snd s))
| (ts, (_, .Inc elem amount)) =>
    (Prod.fst s,
     (fun p =>
       (Prod.fst (Prod.snd s)) p ||
       (decide (p.1 = elem) && decide (p.2.1 = ts) && decide (p.2.2 = amount))),
     Prod.snd (Prod.snd s))
| (_, (_, .Rmv _ D)) =>
    (Prod.fst s,
     Prod.fst (Prod.snd s),
     (fun p => (Prod.snd (Prod.snd s)) p || D p))

inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

@[simp]
def rc (_o1 _o2 : op_t) := rc_res.Either

@[simp]
def commutes_with (o1 o2 : op_t) :=
    forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)

@[simp]
def merge (a b : concrete_st) : concrete_st :=
  let keys_A := union (domain (Prod.fst a)) (domain (Prod.fst b))
  let u_A := const_on keys_A 0
  let A' := iter_upd (fun k _ => max (mysel (Prod.fst a) k) (mysel (Prod.fst b) k)) u_A
  let I' := union (Prod.fst (Prod.snd a)) (Prod.fst (Prod.snd b))
  let R' := union (Prod.snd (Prod.snd a)) (Prod.snd (Prod.snd b))
  (A', I', R')

set_option maxHeartbeats 0

theorem rc_non_comm (o1: op_t) (o2: op_t):
distinct_ops o1 o2 ∧ get_rid o1 != get_rid o2
→
(rc o1 o2 = rc_res.Either ↔ commutes_with o1 o2) := by
  intro h
  simp [commutes_with]
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _⟩ <;>
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
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _⟩ <;>
    simp +decide [*] at *
  all_goals grind



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
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _⟩ <;>
    rcases o1' with ⟨_, _, _ | _ | _⟩ <;> simp +decide [*] at *
  all_goals grind



theorem base_1op (o1:op_t) :
eq (merge (do_ init_st o1) init_st) (do_ (merge init_st init_st) o1) :=
by sal


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
eq (merge (do_ a ol) (do_ b ol)) (do_ (merge a b) ol) := by sal
