import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Std.Tactic.BVDecide

import Sal.Interfaces.Set_Extended
import Sal.Tactic.Sal

open Classical

/-!
# Add-Win Conflict-free Replicated Priority Queue (state-based MRDT)

MRDT adaptation of the Add-Win CRPQ of

    Yuqi Zhang, Lingzhi Ouyang, Yu Huang, Xiaoxing Ma.
    "Conflict-free Replicated Priority Queue: Design, Verification and
    Evaluation." Internetware 2023.  ACM 10.1145/3609437.3609452.

The state-based CRDT lives at `Sal/CRDTs/Add_Win_Priority_Queue_CRDT.lean`.
That version keeps three grow-only components:

  A : map (elem, add_ts) → value    -- add records
  I : set (elem, inc_ts, amount)    -- inc records
  R : set (elem, add_ts)            -- tombstones (needed for Add-Wins)

and `Rmv` carries a prepare-time tombstone snapshot `D ⊆ (elem, add_ts)`
as part of its op payload, so `do_` is a pure pointwise ∨ that does not
read the current A. This is what preserves Add/Rmv commutativity at the
`do_` level for the CRDT (`rc := Either` everywhere).

The MRDT drops both R and the tombstone payload. The version-DAG's LCA
already tells merge which records were present in the shared past, so
the standard set three-way merge

    merge l a b = (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)

gives Add-Wins semantics directly: a Rmv on one branch drops records
present in l, while a concurrent Add on the other branch sits in `b \ l`
and survives. `Rmv` is a simple local `filter` on A.

Because `Rmv` is no longer a pure-payload op, Add-vs-Rmv on the same
element does not commute at the `do_` level, so `rc` arbitrates them
exactly as in `OR_Set_MRDT` (Add-Wins = apply Rmv first in the arbitrated
order). All other pairs commute (different components, or
commutative-associative on the same component) and stay `rc := Either`.

Faithful to the CRDT, `Rmv` does NOT touch `I`: `acquired(e)` sums over
all historical inc records for `e` regardless of Rmv. This matches the
CRDT where R only tombstones A records.

State (concrete_st):

  Prod.fst : set (add_ts, elem, innate_value)
  Prod.snd : set (inc_ts, elem, amount)

Read-side queries (not part of the 24 VCs):

  lookup(e)    := ∃ (_, e', _) ∈ A, e' = e
  innate(e)    := value with max add_ts among A records for e
  acquired(e)  := Σ over I records with elem = e, amount
  priority(e)  := innate(e) + acquired(e)
-/

/-- Σ = (A, I) where
  * A : set of `(add_ts, elem, innate_value)` add records,
  * I : set of `(inc_ts, elem, amount)` increment records.
No tombstone component, the LCA carries that information. -/
abbrev concrete_st := set (ℕ × ℕ × ℕ) × set (ℕ × ℕ × ℤ)

/-- Initial state: empty A and I. -/
@[simp]
def init_st : concrete_st := (empty, empty)

/-- Plain pair equality (Lean's `Set` type). -/
@[simp]
def eq (a b : concrete_st) := a = b

/-- Ops:
  * `Add e v`: stake an add record `(ts, e, v)` in A.
  * `Inc e a`: stake an increment record `(ts, e, a)` in I.
  * `Rmv e`: local filter on A (drop every record with elem `e`).
                 I is untouched. -/
inductive app_op_t : Type where
| Add : ℕ → ℕ → app_op_t    -- elem, innate value
| Inc : ℕ → ℤ → app_op_t    -- elem, amount
| Rmv : ℕ → app_op_t        -- elem

abbrev op_t := ℕ × ℕ × app_op_t

@[simp]
def distinct_ops (op1 op2 : op_t) := Prod.fst op1 != Prod.fst op2

@[simp]
def get_rid (o : op_t) :=
match o with
| (_, (rid, _)) => rid

/-- Effect: Add / Inc stake records (pointwise union); Rmv filters A
in-place. -/
@[simp]
def do_ (s : concrete_st) (o : op_t) : concrete_st :=
match o with
| (ts, (_, .Add e v)) => (add (ts, e, v) (Prod.fst s), Prod.snd s)
| (ts, (_, .Inc e a)) => (Prod.fst s, add (ts, e, a) (Prod.snd s))
| (_,  (_, .Rmv e))   =>
    (filter (Prod.fst s) (fun rec => Prod.fst (Prod.snd rec) != e), Prod.snd s)

inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

/-- `rc` arbitrates Add-vs-Rmv on the same element (same story as
`OR_Set_MRDT`): the Add must be applied first so its record is
available for the subsequent Rmv to filter. Other pairs (different
elements, same op kind, Add-vs-Inc, Rmv-vs-Inc, etc.) commute. -/
@[simp, grind]
def rc (o1 o2 : op_t) :=
match (Prod.snd (Prod.snd o1)), (Prod.snd (Prod.snd o2)) with
| app_op_t.Add e1 _, app_op_t.Rmv e2   => if e1 = e2 then rc_res.Snd_then_fst else rc_res.Either
| app_op_t.Rmv e1,   app_op_t.Add e2 _ => if e1 = e2 then rc_res.Fst_then_snd else rc_res.Either
| _, _ => rc_res.Either

/-- Three-way merge: standard `(l ∩ a ∩ b) ∪ (a ∖ l) ∪ (b ∖ l)` applied
independently to A and I. Gives Add-Wins on A directly via the LCA,
and simple accumulation on I (where no removal happens). -/
@[simp, grind]
def merge (l a b : concrete_st) : concrete_st :=
  let A_l := Prod.fst l
  let A_a := Prod.fst a
  let A_b := Prod.fst b
  let I_l := Prod.snd l
  let I_a := Prod.snd a
  let I_b := Prod.snd b
  (union (intersection A_l (intersection A_a A_b))
         (union (difference A_a A_l) (difference A_b A_l)),
   union (intersection I_l (intersection I_a I_b))
         (union (difference I_a I_l) (difference I_b I_l)))

@[simp]
def commutes_with (o1 o2 : op_t) :=
    forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)


set_option maxHeartbeats 2000000

theorem rc_non_comm (o1: op_t) (o2: op_t):
distinct_ops o1 o2 ∧ get_rid o1 != get_rid o2
→
(rc o1 o2 = rc_res.Either ↔ commutes_with o1 o2) := by sal


theorem no_rc_chain (o1 : op_t) (o2 : op_t) (o3 : op_t) :
(distinct_ops o1 o2 ∧ distinct_ops o2 o3)
→ (¬(rc o1 o2 = rc_res.Fst_then_snd ∧ rc o2 o3 = rc_res.Fst_then_snd))
:= by
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _⟩ <;>
    rcases o3 with ⟨_, _, _ | _ | _⟩ <;> simp +decide [*] at *
  all_goals grind

theorem cond_comm_base (s: concrete_st) (o1: op_t) (o2: op_t) (o3: op_t) :
(distinct_ops o1 o2 ∧ distinct_ops o2 o3 ∧ distinct_ops o1 o3
    ∧ rc o1 o2 = rc_res.Fst_then_snd ∧ ¬(rc o2 o3 = rc_res.Either))
→
eq (do_ (do_ (do_ s o1) o2) o3) (do_ (do_ (do_ s o2) o1) o3) := by
  intro h
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _⟩ <;>
    rcases o3 with ⟨_, _, _ | _ | _⟩ <;>
    unfold eq <;>
    (try ext1) <;> (try funext x) <;>
    simp +decide [*] at h ⊢
  all_goals grind

theorem  merge_comm (l: concrete_st) (a: concrete_st) (b: concrete_st) :
eq (merge l a b) (merge l b a) := by
  unfold eq
  ext1 <;> funext x <;> simp +decide <;> grind

theorem merge_idem (s: concrete_st):
eq (merge s s s) s := by
  unfold eq
  ext1 <;> funext x <;> simp +decide <;> grind

theorem base_2op (o1: op_t) (o2: op_t):
(rc o2 o1 = rc_res.Fst_then_snd ∨ rc o2 o1 = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ distinct_ops o1 o2
→
eq (merge init_st (do_ init_st o1) (do_ init_st o2)) (do_ (merge init_st init_st (do_ init_st o2)) o1) := by
  intro h
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _⟩ <;>
    unfold eq <;>
    (try ext1) <;> (try funext x) <;>
    simp +decide [*] at h ⊢
  all_goals grind

theorem ind_lca_2op (l: concrete_st) (o1: op_t) (o2: op_t) (ol: op_t) :
(rc o2 o1 = rc_res.Fst_then_snd ∨ rc o2 o1 = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ distinct_ops o1 o2 ∧ distinct_ops o1 ol ∧ distinct_ops o2 ol ∧ eq (merge (do_ l ol) (do_ (do_ l ol) o1) (do_ l ol)) (do_ (merge (do_ l ol) (do_ l ol) (do_ l ol)) o1) ∧ eq (merge l (do_ l o1) (do_ l o2)) (do_ (merge l l (do_ l o2)) o1)
→
eq (merge (do_ l ol) (do_ (do_ l ol) o1) (do_ (do_ l ol) o2)) (do_ (merge (do_ l ol) (do_ l ol) (do_ (do_ l ol) o2)) o1) := by
  intro h
  simp only [eq, Prod.ext_iff, funext_iff] at h
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _⟩ <;>
    rcases ol with ⟨_, _, _ | _ | _⟩ <;>
    unfold eq <;>
    (try ext1) <;> (try funext x) <;>
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
  simp only [eq, Prod.ext_iff, funext_iff] at h
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _⟩ <;>
    rcases ob with ⟨_, _, _ | _ | _⟩ <;> rcases ol with ⟨_, _, _ | _ | _⟩ <;>
    unfold eq <;>
    (try ext1) <;> (try funext x) <;>
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
  simp only [eq, Prod.ext_iff, funext_iff] at h
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _⟩ <;>
    rcases ob with ⟨_, _, _ | _ | _⟩ <;> rcases ol with ⟨_, _, _ | _ | _⟩ <;>
    unfold eq <;>
    (try ext1) <;> (try funext x) <;>
    simp +decide [*] at h ⊢
  all_goals grind


theorem inter_right_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ob: op_t) (ol: op_t) :
 ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    (¬ ((rc o ob) = rc_res.Either) ∨ (rc o ol) = rc_res.Fst_then_snd) ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops o2 ob ∧
                    distinct_ops o2 ol ∧ distinct_ops o2 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧
                    get_rid o != get_rid ol ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ b ob) ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ b ob) ol) o2)) o1)
                    →
 eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ (do_ b o) ob) ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ (do_ b o) ob) ol) o2)) o1)
:= by sal


theorem inter_left_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ob: op_t) (ol: op_t) :
 (rc o2 o1) = rc_res.Fst_then_snd ∧ (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid o2 != get_rid o1 ∧ get_rid ob != get_rid ol ∧
                    (¬ ((rc o ob) = rc_res.Either) ∨ (rc o ol) = rc_res.Fst_then_snd) ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops o2 ob ∧
                    distinct_ops o2 ol ∧ distinct_ops o2 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧
                    get_rid o != get_rid ol ∧
                    eq (merge (do_ l ol) (do_ (do_ (do_ a ob) ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ (do_ a ob) ol) (do_ (do_ b ol) o2)) o1)
                    →
   eq (merge (do_ l ol) (do_ (do_ (do_ (do_ a o) ob) ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ (do_ (do_ a o) ob) ol) (do_ (do_ b ol) o2)) o1)
   := by sal

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
  simp only [eq, Prod.ext_iff, funext_iff] at h
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _⟩ <;>
    rcases o2' with ⟨_, _, _ | _ | _⟩ <;>
    unfold eq <;>
    (try ext1) <;> (try funext x) <;>
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
  simp only [eq, Prod.ext_iff, funext_iff] at h
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _⟩ <;>
    rcases o1' with ⟨_, _, _ | _ | _⟩ <;>
    unfold eq <;>
    (try ext1) <;> (try funext x) <;>
    simp +decide [*] at h ⊢
  all_goals grind

theorem base_1op (o1: op_t) :
eq (merge init_st (do_ init_st o1) init_st) (do_ (merge init_st init_st init_st) o1) := by
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;>
    unfold eq <;>
    (try ext1) <;> (try funext x) <;>
    simp +decide
  all_goals grind

theorem  ind_lca_1op (l: concrete_st) (o1: op_t) (ol: op_t) :
 distinct_ops o1 ol ∧
                    (get_rid o1 != get_rid ol ∨ Prod.fst ol < Prod.fst o1) ∧
                    eq (merge l (do_ l o1) l) (do_ (merge l l l) o1)
  → eq (merge (do_ l ol) (do_ (do_ l ol) o1) (do_ l ol)) (do_ (merge (do_ l ol) (do_ l ol) (do_ l ol)) o1) := by
  intro h
  simp only [eq, Prod.ext_iff, funext_iff] at h
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;> rcases ol with ⟨_, _, _ | _ | _⟩ <;>
    unfold eq <;>
    (try ext1) <;> (try funext x) <;>
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
  simp only [eq, Prod.ext_iff, funext_iff] at h
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;>
    rcases ob with ⟨_, _, _ | _ | _⟩ <;> rcases ol with ⟨_, _, _ | _ | _⟩ <;>
    unfold eq <;>
    (try ext1) <;> (try funext x) <;>
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
  simp only [eq, Prod.ext_iff, funext_iff] at h
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;>
    rcases ob with ⟨_, _, _ | _ | _⟩ <;> rcases ol with ⟨_, _, _ | _ | _⟩ <;>
    unfold eq <;>
    (try ext1) <;> (try funext x) <;>
    simp +decide [*] at h ⊢
  all_goals grind

theorem inter_right_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ob: op_t) (ol: op_t) (o: op_t) :
rc ob ol =  rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧ (¬(rc o ob = rc_res.Either) ∨ (rc o ol = rc_res.Fst_then_snd)) ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧ get_rid o != get_rid ol ∧ eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ob) ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ob) ol)) o1)
→
eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ b o) ob) ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ b o) ob) ol)) o1)
:= by
  intro h
  simp only [eq, Prod.ext_iff, funext_iff] at h
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;>
    rcases ob with ⟨_, _, _ | _ | _⟩ <;> rcases ol with ⟨_, _, _ | _ | _⟩ <;>
    rcases o with ⟨_, _, _ | _ | _⟩ <;>
    unfold eq <;>
    (try ext1) <;> (try funext x) <;>
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
  simp only [eq, Prod.ext_iff, funext_iff] at h
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;>
    rcases ob with ⟨_, _, _ | _ | _⟩ <;> rcases ol with ⟨_, _, _ | _ | _⟩ <;>
    rcases o with ⟨_, _, _ | _ | _⟩ <;>
    unfold eq <;>
    (try ext1) <;> (try funext x) <;>
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
  simp only [eq, Prod.ext_iff, funext_iff] at h
  rcases o1 with ⟨_, _, _ | _ | _⟩ <;>
    rcases o1' with ⟨_, _, _ | _ | _⟩ <;> rcases ol with ⟨_, _, _ | _ | _⟩ <;>
    unfold eq <;>
    (try ext1) <;> (try funext x) <;>
    simp +decide [*] at h ⊢
  all_goals grind

theorem ind_right_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o2: op_t) (o2': op_t) (ol: op_t)  :
distinct_ops o2 o2' ∧ distinct_ops o2 ol ∧ distinct_ops o2' ol ∧
                    eq (merge (do_ l ol) (do_ a ol) (do_ b o2)) (do_ (merge (do_ l ol) (do_ a ol) b) o2)
→
eq (merge (do_ l ol) (do_ a ol) (do_ (do_ b o2') o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b o2')) o2)
:= by
  intro h
  simp only [eq, Prod.ext_iff, funext_iff] at h
  rcases o2 with ⟨_, _, _ | _ | _⟩ <;>
    rcases o2' with ⟨_, _, _ | _ | _⟩ <;> rcases ol with ⟨_, _, _ | _ | _⟩ <;>
    unfold eq <;>
    (try ext1) <;> (try funext x) <;>
    simp +decide [*] at h ⊢
  all_goals grind

theorem  lem_0op (l: concrete_st) (a: concrete_st) (b: concrete_st) (ol: op_t) :
eq (merge (do_ l ol) (do_ a ol) (do_ b ol)) (do_ (merge l a b) ol)
:= by
  rcases ol with ⟨_, _, _ | _ | _⟩ <;>
    unfold eq <;>
    (try ext1) <;> (try funext x) <;>
    simp +decide
  all_goals grind
