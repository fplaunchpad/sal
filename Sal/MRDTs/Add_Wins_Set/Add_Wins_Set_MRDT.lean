import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Std.Tactic.BVDecide

import Sal.Interfaces.Set_Extended
import Sal.Tactic.Sal

open Classical

/-!
# Add-Wins Set (AWSet): state-based MRDT

Two-set encoding of Σ = `(adds, tombstones)`. `Add` stakes a fresh
tag `ts` into `adds`; `Rem` carries no element payload at all — it
sweeps *every* tag currently visible in `adds` into `tombstones`
(a global clear of whatever is present at that moment, not a
per-element retraction).

`rc` orders every `Add`/`Rem` pair so the reconciled sequential order
always runs the `Rem` before the `Add`, regardless of which is `o1`
and which is `o2`: a `Rem` can only sweep tags that already existed
before it ran, so a concurrently-issued `Add`'s tag survives the
sweep and is present after reconciliation (add-wins). Because the
ordering already does the work, `merge` needs no LCA-based
arithmetic: it's a plain per-component union of `adds` and of
`tombstones`, with `l` unused.

Ported from the F* `App_mrdt` reference implementation (`concrete_st`,
`do`, `rc`, `merge` as given there).
-/

/-- Σ = (adds, tombstones), both sets of tags. -/
abbrev concrete_st := set ℕ × set ℕ

/-- Initial state: both components empty. -/
@[simp]
def init_st: concrete_st := (empty, empty)

/-- Pointwise extensional equality on both set components (as in
`Sal/CRDTs/OR_Set/OR_Set_CRDT.lean`, minus the element component: an
AWSet tag carries no element, so where that file's `adds`/`tombstones`
are `set (elem × ts)`, ours are just `set ts`). -/
@[simp]
def eq (a b: concrete_st) :=
(forall e, mem e (Prod.fst a) ↔ mem e (Prod.fst b)) ∧
(forall e, mem e (Prod.snd a) ↔ mem e (Prod.snd b))

/-- Two unit-payload ops: `Rem` targets no specific element. -/
inductive app_op_t : Type where
| Add
| Rem

abbrev op_t:= ℕ × ℕ × app_op_t

@[simp]
def distinct_ops (op1 op2: op_t) := Prod.fst op1 != Prod.fst op2

@[simp]
def get_rid (o: op_t) :=
match o with
| (_, (rid, _)) => rid

/-- Effect:
  * `Add` at `ts`: stake `ts` into `adds`.
  * `Rem`: sweep every currently-live `adds` tag into `tombstones`. -/
@[simp]
def do_ (s: concrete_st) (o: op_t) : concrete_st :=
match o with
| (ts, (_, app_op_t.Add)) => (add ts s.1, s.2)
| (_, (_, app_op_t.Rem)) => (s.1, union s.1 s.2)

inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

/-- `rc` orders every `Add`/`Rem` pair so `Rem` always precedes `Add`
in the reconciled order, whichever argument position it's in. Every
other pair is `Either`. -/
@[simp, grind]
def rc (o1 o2: op_t) :=
match (Prod.snd (Prod.snd o1)), (Prod.snd (Prod.snd o2)) with
| app_op_t.Add, app_op_t.Rem => rc_res.Snd_then_fst
| app_op_t.Rem, app_op_t.Add => rc_res.Fst_then_snd
| _, _ => rc_res.Either

/-- Three-way merge: plain per-component union; `l` unused. -/
@[simp, grind]
def merge (_l: concrete_st) (a: concrete_st) (b: concrete_st) : concrete_st :=
  (union a.1 b.1, union a.2 b.2)

@[simp]
def commutes_with (o1 o2: op_t) :=
    forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)


set_option maxHeartbeats 2000000

theorem rc_non_comm (o1: op_t) (o2: op_t):
distinct_ops o1 o2 ∧ get_rid o1 != get_rid o2
→
(commutes_with o1 o2 → rc o1 o2 = rc_res.Either) := by
  intros h_distinct h_comm
  rcases o1 with ⟨ts1, rid1, c1⟩
  rcases o2 with ⟨ts2, rid2, c2⟩
  cases c1 <;> cases c2 <;> simp only [rc]
  all_goals
    (exfalso
     have h2 := h_comm (empty, empty)
     simp +decide [do_, eq] at h2)


theorem no_rc_chain (o1 : op_t) (o2 : op_t) (o3 : op_t) :
(distinct_ops o1 o2 ∧ distinct_ops o2 o3)
→ (¬(rc o1 o2 = rc_res.Fst_then_snd ∧ rc o2 o3 = rc_res.Fst_then_snd))
:= by
  rcases o1 with ⟨_, _, _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _⟩ <;>
    rcases o3 with ⟨_, _, _ | _⟩ <;> simp +decide [*] at *

theorem cond_comm_base (s: concrete_st) (o1: op_t) (o2: op_t) (o3: op_t) :
(distinct_ops o1 o2 ∧ distinct_ops o2 o3 ∧ distinct_ops o1 o3
    ∧ rc o1 o2 = rc_res.Fst_then_snd ∧ ¬(rc o2 o3 = rc_res.Either))
→
eq (do_ (do_ (do_ s o1) o2) o3) (do_ (do_ (do_ s o2) o1) o3) := by
  intro h
  rcases o1 with ⟨_, _, _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _⟩ <;>
    rcases o3 with ⟨_, _, _ | _⟩ <;>
    refine ⟨?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind

theorem  merge_comm (l: concrete_st) (a: concrete_st) (b: concrete_st) :
eq (merge l a b) (merge l b a) := by
  refine ⟨?_, ?_⟩ <;> intro k <;> simp +decide
  all_goals grind

theorem merge_idem (s: concrete_st):
eq (merge s s s) s := by
  refine ⟨?_, ?_⟩ <;> intro k <;> simp +decide

theorem base_2op (o1: op_t) (o2: op_t):
(rc o2 o1 = rc_res.Fst_then_snd ∨ rc o2 o1 = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ distinct_ops o1 o2
→
eq (merge init_st (do_ init_st o1) (do_ init_st o2)) (do_ (merge init_st init_st (do_ init_st o2)) o1) := by
  intro h
  rcases o1 with ⟨_, _, _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _⟩ <;>
    refine ⟨?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind

theorem ind_lca_2op (l: concrete_st) (o1: op_t) (o2: op_t) (ol: op_t) :
(rc o2 o1 = rc_res.Fst_then_snd ∨ rc o2 o1 = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ distinct_ops o1 o2 ∧ distinct_ops o1 ol ∧ distinct_ops o2 ol ∧ eq (merge (do_ l ol) (do_ (do_ l ol) o1) (do_ l ol)) (do_ (merge (do_ l ol) (do_ l ol) (do_ l ol)) o1) ∧ eq (merge l (do_ l o1) (do_ l o2)) (do_ (merge l l (do_ l o2)) o1)
→
eq (merge (do_ l ol) (do_ (do_ l ol) o1) (do_ (do_ l ol) o2)) (do_ (merge (do_ l ol) (do_ l ol) (do_ (do_ l ol) o2)) o1) := by
  intro h
  rcases o1 with ⟨_, _, _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _⟩ <;>
    rcases ol with ⟨_, _, _ | _⟩ <;>
    refine ⟨?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind


theorem inter_right_base_2op  (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ob: op_t) (ol: op_t) :
(rc o2 o1 = rc_res.Fst_then_snd ∨ rc o2 o1 = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ rc ob o1 = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧ distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o2 ob ∧ distinct_ops o2 ol ∧ distinct_ops ob ol ∧
                    eq (merge l (do_ a o1) (do_ b o2)) (do_ (merge l a (do_ b o2)) o1) ∧
                    eq (merge l (do_ a o1) (do_ (do_ b ob) o2)) (do_ (merge l a (do_ (do_ b ob) o2)) o1) ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ol) o2)) o1)
                    →
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ b ob) ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ b ob) ol) o2)) o1)
                    := by
  intro h
  rcases o1 with ⟨_, _, _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _⟩ <;>
    rcases ob with ⟨_, _, _ | _⟩ <;> rcases ol with ⟨_, _, _ | _⟩ <;>
    refine ⟨?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind
theorem inter_left_base_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ob: op_t) (ol: op_t) :
 (rc o2 o1) = rc_res.Fst_then_snd ∧ (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid o2 != get_rid o1 ∧ get_rid ob != get_rid ol ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o2 ob ∧ distinct_ops o2 ol ∧ distinct_ops ob ol ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ol) o2)) o1)
                    →
                  eq (merge (do_ l ol) (do_ (do_ (do_ a ob) ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ (do_ a ob) ol) (do_ (do_ b ol) o2)) o1)
:= by
  intro h
  rcases o1 with ⟨_, _, _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _⟩ <;>
    rcases ob with ⟨_, _, _ | _⟩ <;> rcases ol with ⟨_, _, _ | _⟩ <;>
    refine ⟨?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind



theorem inter_right_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ob: op_t) (ol: op_t) (o: op_t) :
 ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    (¬ ((rc o ob) = rc_res.Either) ∨ (rc o ol) = rc_res.Fst_then_snd) ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops o2 ob ∧
                    distinct_ops o2 ol ∧ distinct_ops o2 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧
                    get_rid o != get_rid ol ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ b ob) ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ b ob) ol) o2)) o1)
                    →
 eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ (do_ b o) ob) ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ (do_ b o) ob) ol) o2)) o1)
:= by
  intro h
  rcases o1 with ⟨_, _, _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _⟩ <;>
    rcases ob with ⟨_, _, _ | _⟩ <;> rcases ol with ⟨_, _, _ | _⟩ <;>
    rcases o with ⟨_, _, _ | _⟩ <;>
    refine ⟨?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind



theorem inter_left_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ob: op_t) (ol: op_t) (o: op_t) :
 (rc o2 o1) = rc_res.Fst_then_snd ∧ (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid o2 != get_rid o1 ∧ get_rid ob != get_rid ol ∧
                    (¬ ((rc o ob) = rc_res.Either) ∨ (rc o ol) = rc_res.Fst_then_snd) ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops o2 ob ∧
                    distinct_ops o2 ol ∧ distinct_ops o2 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧
                    get_rid o != get_rid ol ∧
                    eq (merge (do_ l ol) (do_ (do_ (do_ a ob) ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ (do_ a ob) ol) (do_ (do_ b ol) o2)) o1)
                    →
   eq (merge (do_ l ol) (do_ (do_ (do_ (do_ a o) ob) ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ (do_ (do_ a o) ob) ol) (do_ (do_ b ol) o2)) o1)
   := by
  intro h
  rcases o1 with ⟨_, _, _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _⟩ <;>
    rcases ob with ⟨_, _, _ | _⟩ <;> rcases ol with ⟨_, _, _ | _⟩ <;>
    rcases o with ⟨_, _, _ | _⟩ <;>
    refine ⟨?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind

theorem inter_lca_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ol: op_t) :
((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ol ∧ distinct_ops o2 ol ∧
                    (exists o, (rc o ol) = rc_res.Fst_then_snd) ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b ol)) o1) ∧
                    eq (merge l (do_ a o1) (do_ b o2)) (do_ (merge l a (do_ b o2)) o1)
  →
  eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ol) o2)) o1) := by sal

theorem ind_right_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (o2': op_t) :
(rc o2 o1) = rc_res.Fst_then_snd ∧ get_rid o1 != get_rid o2 ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 o2' ∧ distinct_ops o2 o2' ∧
                    eq (merge l (do_ a o1) (do_ b o2)) (do_ (merge l a (do_ b o2)) o1)
                    →  eq (merge l (do_ a o1) (do_ (do_ b o2') o2)) (do_ (merge l a (do_ (do_ b o2') o2)) o1) := by
  intro h
  rcases o1 with ⟨_, _, _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _⟩ <;>
    rcases o2' with ⟨_, _, _ | _⟩ <;>
    refine ⟨?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind
theorem ind_left_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (o1': op_t) :
 ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 o1' ∧ distinct_ops o2 o1' ∧
                    eq (merge l (do_ a o1) (do_ b o2)) (do_ (merge l a (do_ b o2)) o1)
                    →

 eq (merge l (do_ (do_ a o1') o1) (do_ b o2)) (do_ (merge l (do_ a o1') (do_ b o2)) o1)
 := by
  intro h
  rcases o1 with ⟨_, _, _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _⟩ <;>
    rcases o1' with ⟨_, _, _ | _⟩ <;>
    refine ⟨?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind

theorem base_1op (o1: op_t) :
eq (merge init_st (do_ init_st o1) init_st) (do_ (merge init_st init_st init_st) o1) := by
  rcases o1 with ⟨_, _, _ | _⟩ <;>
    refine ⟨?_, ?_⟩ <;> intro k <;>
    simp +decide [*]
theorem  ind_lca_1op (l: concrete_st) (o1: op_t) (ol: op_t) :
 distinct_ops o1 ol ∧
                    (get_rid o1 != get_rid ol ∨ Prod.fst ol < Prod.fst o1) ∧
                    eq (merge l (do_ l o1) l) (do_ (merge l l l) o1)
  → eq (merge (do_ l ol) (do_ (do_ l ol) o1) (do_ l ol)) (do_ (merge (do_ l ol) (do_ l ol) (do_ l ol)) o1) := by
  intro h
  rcases o1 with ⟨_, _, _ | _⟩ <;> rcases ol with ⟨_, _, _ | _⟩ <;>
    refine ⟨?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind
theorem inter_right_base_1op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ob: op_t) (ol: op_t)  :
 (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops ob ol ∧
                    ((rc ob o1) = rc_res.Fst_then_snd → eq (merge l (do_ a o1) (do_ b ob)) (do_ (merge l a (do_ b ob)) o1)) ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b ol)) o1)
                    →
  eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ob) ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ob) ol)) o1)
  := by
  intro h
  rcases o1 with ⟨_, _, _ | _⟩ <;>
    rcases ob with ⟨_, _, _ | _⟩ <;> rcases ol with ⟨_, _, _ | _⟩ <;>
    refine ⟨?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind


theorem inter_left_base_1op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ob: op_t) (ol: op_t) :
 (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops ob ol ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b ol)) o1)
                    →
  eq (merge (do_ l ol) (do_ (do_ (do_ a ob) ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ (do_ a ob) ol) (do_ b ol)) o1)
  := by
  intro h
  rcases o1 with ⟨_, _, _ | _⟩ <;>
    rcases ob with ⟨_, _, _ | _⟩ <;> rcases ol with ⟨_, _, _ | _⟩ <;>
    refine ⟨?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind

theorem inter_right_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ob: op_t) (ol: op_t) (o: op_t) :
rc ob ol =  rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧ (¬(rc o ob = rc_res.Either) ∨ (rc o ol = rc_res.Fst_then_snd)) ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧ get_rid o != get_rid ol ∧ eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ob) ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ob) ol)) o1)
→
eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ b o) ob) ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ b o) ob) ol)) o1)
:= by
  intro h
  rcases o1 with ⟨_, _, _ | _⟩ <;>
    rcases ob with ⟨_, _, _ | _⟩ <;> rcases ol with ⟨_, _, _ | _⟩ <;>
    rcases o with ⟨_, _, _ | _⟩ <;>
    refine ⟨?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind
theorem inter_left_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ob: op_t) (ol: op_t) (o: op_t) :
 (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    (¬ ((rc o ob) = rc_res.Either) ∨ (rc o ol) = rc_res.Fst_then_snd) ∧
                    distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧
                    get_rid o != get_rid ol ∧
                    eq (merge (do_ l ol) (do_ (do_ (do_ a ob) ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ (do_ a ob) ol) (do_ b ol)) o1)
                    →
                     eq (merge (do_ l ol) (do_ (do_ (do_ (do_ a o) ob) ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ (do_ (do_ a o) ob) ol) (do_ b ol)) o1)
        := by
  intro h
  rcases o1 with ⟨_, _, _ | _⟩ <;>
    rcases ob with ⟨_, _, _ | _⟩ <;> rcases ol with ⟨_, _, _ | _⟩ <;>
    rcases o with ⟨_, _, _ | _⟩ <;>
    refine ⟨?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind
theorem inter_lca_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ol: op_t) (oi: op_t) :
distinct_ops o1 ol ∧ distinct_ops o1 oi ∧ distinct_ops ol oi ∧
                    (exists o, (rc o ol) = rc_res.Fst_then_snd) ∧
                    (exists o, (rc o oi) = rc_res.Fst_then_snd) ∧
                    eq (merge (do_ l oi) (do_ (do_ a oi) o1) (do_ b oi)) (do_ (merge (do_ l oi) (do_ a oi) (do_ b oi)) o1) ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b ol)) o1)
                    →
                  eq (merge (do_ (do_ l oi) ol) (do_ (do_ (do_ a oi) ol) o1) (do_ (do_ b oi) ol))
                      (do_ (merge (do_ (do_ l oi) ol) (do_ (do_ a oi) ol) (do_ (do_ b oi) ol)) o1)
:= by sal

theorem ind_left_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o1': op_t) (ol: op_t) :
distinct_ops o1 o1' ∧ distinct_ops o1 ol ∧ distinct_ops o1' ol ∧
                    eq (merge (do_ l ol) (do_ a o1) (do_ b ol)) (do_ (merge (do_ l ol) a (do_ b ol)) o1)
→
eq (merge (do_ l ol) (do_ (do_ a o1') o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a o1') (do_ b ol)) o1)
:= by
  intro h
  rcases o1 with ⟨_, _, _ | _⟩ <;>
    rcases o1' with ⟨_, _, _ | _⟩ <;> rcases ol with ⟨_, _, _ | _⟩ <;>
    refine ⟨?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind

theorem ind_right_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o2: op_t) (o2': op_t) (ol: op_t)  :
distinct_ops o2 o2' ∧ distinct_ops o2 ol ∧ distinct_ops o2' ol ∧
                    eq (merge (do_ l ol) (do_ a ol) (do_ b o2)) (do_ (merge (do_ l ol) (do_ a ol) b) o2)
→
eq (merge (do_ l ol) (do_ a ol) (do_ (do_ b o2') o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b o2')) o2)
:= by
  intro h
  rcases o2 with ⟨_, _, _ | _⟩ <;>
    rcases o2' with ⟨_, _, _ | _⟩ <;> rcases ol with ⟨_, _, _ | _⟩ <;>
    refine ⟨?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind
theorem  lem_0op (l: concrete_st) (a: concrete_st) (b: concrete_st) (ol: op_t) :
eq (merge (do_ l ol) (do_ a ol) (do_ b ol)) (do_ (merge l a b) ol)
:= by
  rcases ol with ⟨_, _, _ | _⟩ <;>
    refine ⟨?_, ?_⟩ <;> intro k <;>
    simp +decide [*]
  all_goals grind
