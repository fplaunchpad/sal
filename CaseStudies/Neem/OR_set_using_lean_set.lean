import Lean
import Aesop

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.Linarith

import Mathlib.Data.Set.Basic

import CaseStudies.Velvet.Std

import Blaster

open Lean.Elab.Term.DoNames

namespace myset

@[simp]
abbrev set (a:Type) [DecidableEq a] := Set a

def equal {a:Type} [DecidableEq a] (s1: set a) (s2: set a)
:= s1 = s2

def empty {a:Type} [DecidableEq a] : set a := {}

def singleton {a:Type} [DecidableEq a] (x: a): set a := {x}

def union {a:Type} [DecidableEq a] (s1 s2 : set a) : set a :=
Set.union s1 s2

def intersection {a:Type} [DecidableEq a] (s1 s2: set a) : set a :=
Set.inter s1 s2

def complement {a:Type} [DecidableEq a] (s : set a) : set a :=
sᶜ

def mem {a:Type} [DecidableEq a] (x: a) (s: set a) : Prop := x ∈ s

def difference {a:Type}  [DecidableEq a] (s1 s2: set a) : set a :=
Set.inter s1 (s2ᶜ)

def filter {a:Type}  [DecidableEq a] (s1: set a) (p: a → Bool) : set a :=
{x | x ∈ s1 ∧ p x}

def remove {a: Type} [DecidableEq a] (s1: set a) x :=
{y | y ∈ s1 ∧ x != y}

def subset {a: Type} [DecidableEq a] (s1 s2: set a) :=
forall x, mem x s1 → mem x s2

@[simp, grind]
def add {a: Type} [DecidableEq a] (x:a) (s: set a) : set a :=
union s (singleton x)


@[simp]
lemma mem_empty {a: Type} [DecidableEq a] (x: a) :
(mem x empty) → False := by
unfold empty
unfold mem
grind

@[simp]
lemma equal_intro {a: Type} [DecidableEq a] (s1 s2 : set a) :
(forall x:a, mem x s1 = mem x s2) → equal s1 s2 := by
simp
intros h
unfold mem at h
unfold equal
grind


grind_pattern equal_intro => (equal s1 s2)

@[simp, grind?]
lemma equal_intro' {a: Type} [DecidableEq a] (s1 s2 : set a) :
equal s1 s2 ↔ s1 = s2 := by
unfold equal
simp

lemma equal_elim  {a: Type} [DecidableEq a] (s1 s2 : set a) :
equal s1 s2 → s1 = s2 := by simp

grind_pattern equal_elim => equal s1 s2


@[simp, grind?]
lemma equal_refl  {a: Type} [DecidableEq a] (s1 s2 : set a) :
s1 = s2 → (forall x:a, mem x s1 = mem x s2) ∧ equal s1 s2 := by
simp
grind


lemma equal_refl' {a:Type} [DecidableEq a] (s1 s2: set a) :
equal s1 s2 ↔ (forall x:a, mem x s1 = mem x s2) := by
simp
unfold mem at *
aesop



@[simp, grind]
lemma equal_refl1 {a: Type} [DecidableEq a] (s: set a) :
equal s s := by simp


@[simp]
lemma mem_subset {a: Type} [DecidableEq a] (s1 s2: set a) :
(forall x, mem x s1 → mem x s2) → subset s1 s2 := by
unfold subset
simp

grind_pattern mem_subset => subset s1 s2

@[simp, grind?]
lemma subset_mem {a: Type} [DecidableEq a] (s1 s2: set a) :
subset s1 s2 → (forall x, mem x s1 → mem x s2) := by
unfold subset
simp



@[simp]
lemma mem_union {a: Type} [DecidableEq a] (s1 s2: set a) (x:a) :
mem x (union s1 s2) ↔ (mem x s1  ∨ mem x s2) := by
unfold mem at *
aesop


grind_pattern mem_union => mem x (union s1 s2)


@[simp]
lemma mem_singleton {a: Type} [DecidableEq a] (x y : a):
mem y (singleton x) = (x = y) := by
simp
unfold mem at *
unfold singleton
grind

grind_pattern mem_singleton => mem y (singleton x)

@[simp]
lemma mem_intersection {a: Type} [DecidableEq a] (s1 s2: set a) (x: a) :
mem x (intersection s1 s2) ↔ (mem x s1 ∧ mem x s2) := by
unfold mem at *
aesop

grind_pattern mem_intersection => mem x (intersection s1 s2)

@[simp]
lemma mem_complement {a: Type} [DecidableEq a] (s: set a) (x: a) :
mem x (complement s) ↔ ((mem x s) → False) := by
unfold mem at *
unfold complement
simp

grind_pattern mem_complement => mem x (complement s)

@[simp]
lemma mem_difference {a: Type} [DecidableEq a] (s1 s2: set a) (x: a) :
mem x (difference s1 s2) ↔ (mem x s1 ∧ ¬ (mem x s2)) := by
unfold mem
simp
aesop

grind_pattern mem_difference => mem x (difference s1 s2)

@[simp, grind?]
lemma mem_filter {a: Type} [DecidableEq a] (s: set a) (p: a → Bool) (x: a):
mem x (filter s p) ↔ (mem x s ∧ p x) := by
unfold filter
unfold mem
simp

@[simp, grind?]
lemma mem_remove_x {a: Type} [DecidableEq a] (s: set a) (x: a):
(mem x (remove s x)) → False:= by
unfold remove
unfold mem
simp

@[simp, grind?]
lemma mem_remove_y {a: Type} [DecidableEq a] (s: set a) (x: a) (y: a) :
x !=y → mem y (remove s x) = mem y s := by
simp
unfold mem
unfold remove
grind

abbrev concrete_st := set (ℕ × ℕ)

@[simp]
def init_st: concrete_st := empty

@[simp]
def mem_id_s (id:ℕ) (s: concrete_st) : Prop :=
exists e, mem e s ∧ Prod.fst e = id

@[simp]
def mem_ele_s (ele: ℕ) (s: concrete_st) : Prop :=
exists e, mem e s ∧ Prod.snd e = ele


@[simp]
def eq (a: concrete_st) (b: concrete_st) := a = b

inductive app_op_t : Type where
| Add: ℕ → app_op_t
| Rem: ℕ → app_op_t

abbrev op_t:= ℕ × ℕ × app_op_t

@[simp]
def distinct_ops (op1 op2: op_t) := Prod.fst op1 != Prod.fst op2

@[simp]
def get_rid (o: op_t) :=
match o with
| (_, (rid, _)) => rid

@[simp]
def get_ele (o: op_t) : ℕ :=
  match (Prod.snd (Prod.snd o)) with
  | app_op_t.Add e => e
  | app_op_t.Rem e => e

@[simp]
def do_ (s: concrete_st) (o: op_t) : concrete_st :=
match o with
| (ts, (rid, app_op_t.Add e)) => add (ts,e) s
| (_, (rid, app_op_t.Rem e)) => filter s (fun ele => Prod.snd ele != e)


inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

@[simp, grind]
def rc (o1: op_t) (o2: op_t) :=
match (Prod.snd (Prod.snd o1)), (Prod.snd (Prod.snd o2)) with
| app_op_t.Add e1, app_op_t.Rem e2 => if e1 = e2 then rc_res.Snd_then_fst else rc_res.Either
| app_op_t.Rem e1, app_op_t.Add e2 => if e1 = e2 then rc_res.Fst_then_snd else rc_res.Either
| _,_ => rc_res.Either


@[simp, grind]
def merge (l: concrete_st) (a: concrete_st) (b: concrete_st) : concrete_st :=
  let da := difference a l
  let db := difference b l
  let i_ab := intersection a b
  let i_lab := intersection l i_ab
  union i_lab (union da db)


@[simp]
def commutes_with (o1 o2: op_t) :=
    forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)


set_option maxHeartbeats 2000000

theorem rc_non_comm (o1: op_t) (o2: op_t):
distinct_ops o1 o2 ∧ get_rid o1 != get_rid o2
→
(rc o1 o2 = rc_res.Either ↔ commutes_with o1 o2) := by
dsimp
aesop
all_goals try grind
all_goals try
{
    rw [← equal_intro'] at *
    grind
}
{
    have h := a empty
    rw [← equal_intro'] at h
    rw [equal_refl'] at h
    unfold filter at h
    sorry
}
sorry

theorem inter_left_base_1op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ob: op_t) (ol: op_t) :
 (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops ob ol ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b ol)) o1)
                    →
  eq (merge (do_ l ol) (do_ (do_ (do_ a ob) ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ (do_ a ob) ol) (do_ b ol)) o1)
  := by
dsimp
aesop
all_goals try grind
all_goals try {
  rw [← equal_intro'] at *
  rw [equal_refl'] at *
  aesop
  try grind
}

























-- abbrev pos := ℕ

-- abbrev mytype := pos × ℕ
-- abbrev concrete_st := Set (mytype)



-- variable {mytype : Type}


-- -- @[grind, simp]
-- -- theorem mem_empty: forall (x:mytype) (s: Set mytype),  s = {} ∧ (x ∈ s) → False := by
-- -- intros
-- -- aesop


-- -- @[simp]
-- -- theorem equal_intro (s1 s2: Set mytype): (∀ (x:mytype), x ∈ s1 ↔ x ∈ s2) → s1 = s2  :=
-- -- by
-- -- rw [Set.ext_iff]
-- -- intros h
-- -- assumption


-- -- @[grind]
-- -- theorem mem_union (s1 s2: Set mytype) (x:mytype) :
-- -- x ∈ (s1 ∪ s2) ↔ (x ∈ s1 ∨ x ∈ s2) := by
-- -- rw [Set.mem_union]



-- -- @[grind]
-- -- theorem mem_singleton (x y: mytype) (s: Set mytype):
-- -- s = {x} → y ∈ s → y = x := by
-- -- intros h1 h2
-- -- rw [h1] at h2
-- -- rw [Set.mem_singleton_iff] at h2
-- -- assumption


-- -- @[grind]
-- -- theorem mem_intersection (s1 s2: Set mytype) (x:mytype) :
-- -- x ∈ (s1 ∩ s2) ↔ (x ∈ s1 ∧ x ∈ s2) := by
-- -- rw [Set.mem_inter_iff]



-- -- @[grind]
-- -- theorem mem_complement (s: Set mytype) (x: mytype) :
-- -- x ∈ sᶜ ↔ x ∉ s := by
-- -- rw [Set.mem_compl_iff]


-- @[simp]
-- def init_st: concrete_st := {}

-- @[simp]
-- def mem_id_s (id:pos) (s: concrete_st) : Prop :=
-- exists e, e ∈ s ∧ Prod.fst e = id

-- @[simp]
-- def mem_ele_s (ele: ℕ) (s: concrete_st) : Prop :=
-- exists e, e ∈ s ∧ Prod.snd e = ele

-- @[simp]
-- def eq (a: concrete_st) (b: concrete_st) := a=b

-- inductive app_op_t : Type where
-- | Add: ℕ → app_op_t
-- | Rem: ℕ → app_op_t

-- abbrev op_t:= ℕ × ℕ × app_op_t

-- @[simp]
-- def distinct_ops (op1 op2: op_t) := Prod.fst op1 != Prod.fst op2

-- @[simp]
-- def get_rid (o: op_t) :=
-- match o with
-- | (_, (rid, _)) => rid

-- @[simp]
-- def get_ele (o: op_t) : ℕ :=
--   match (Prod.snd (Prod.snd o)) with
--   | app_op_t.Add e => e
--   | app_op_t.Rem e => e

-- @[simp]
-- def do_ (s: concrete_st) (o: op_t) : concrete_st :=
-- match o with
-- | (ts, (rid, app_op_t.Add e)) => {(ts,e)} ∪ s
-- | (_, (rid, app_op_t.Rem e)) => {x | x ∈ s ∧ Prod.snd x != e}


-- inductive rc_res : Type where
-- | Fst_then_snd
-- | Snd_then_fst
-- | Either

-- @[simp]
-- def rc (o1: op_t) (o2: op_t) :=
-- match (Prod.snd (Prod.snd o1)), (Prod.snd (Prod.snd o2)) with
-- | app_op_t.Add e1, app_op_t.Rem e2 => if e1 = e2 then rc_res.Snd_then_fst else rc_res.Either
-- | app_op_t.Rem e1, app_op_t.Add e2 => if e1 = e2 then rc_res.Fst_then_snd else rc_res.Either
-- | _,_ => rc_res.Either


-- @[simp]
-- def merge (l: concrete_st) (a: concrete_st) (b: concrete_st) : concrete_st :=
--   (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)

-- @[simp]
-- def commutes_with (o1 o2: op_t) :=
--     forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)



-- set_option maxHeartbeats 0


-- declare_aesop_rule_sets [Set.insert_eq, Set.insert_idem, Set.union_assoc, Set.union_comm, Set.pairwise_insert_of_notMem] (default := true)

-- theorem my_theorem: ∀ (fst: ℕ) (e1: ℕ) (s : Set (pos × ℕ)) ,
--     {x | (x = (fst, e1) ∨ x ∈ s) ∧ ¬x.2 = e1} = insert (fst, e1) {x | x ∈ s ∧ ¬x.2 = e1} → False := by
--   intros fst e1 s H
--   have H0 : (fst, e1) ∉ {x | (x = (fst, e1) ∨ x ∈ s) ∧ ¬ x.2 = e1} := by
--     intros H1
--     simp at H1
--   have H1 : (fst, e1) ∈ insert (fst, e1) {x | x ∈ s ∧ ¬ x.2 = e1} := by
--     simp
--   aesop


-- method rc_non_comm (o1: op_t) (o2: op_t) return (u: Unit)
-- require distinct_ops o1 o2 ∧ get_rid o1 != get_rid o2
-- ensures (rc o1 o2 = rc_res.Either ↔ commutes_with o1 o2)
-- do
--     return ()


-- #check Set.insert_eq

-- prove_correct rc_non_comm by
--     dsimp [rc_non_comm]
--     loom_solve
--     {
--         have H := my_theorem
--         have H2 := H fst e1
--         unfold concrete_st at a_2
--         let s : Set (pos × ℕ) := ∅
--         have eq1 := a_2 s
--         exact H2 s eq1
--     }
--     {
--         have H := my_theorem
--         have H2 := H fst_1 e1
--         unfold concrete_st at a_2
--         let s : Set (pos × ℕ) := ∅
--         have eq1 := a_2 s
--         have eq2 : {x | (x = (fst_1, e1) ∨ x ∈ s) ∧ ¬x.2 = e1} = insert (fst_1, e1) {x | x ∈ s ∧ ¬x.2 = e1} := by rw [eq1]
--         exact H2 s eq2
--     }


-- method no_rc_chain (o1: op_t) (o2: op_t) (o3: op_t) return (u: Unit)
-- require distinct_ops o1 o2 ∧ distinct_ops o2 o3
-- ensures ¬(rc o1 o2 = rc_res.Fst_then_snd ∧ rc o2 o3 = rc_res.Fst_then_snd)
-- do
--     return ()

-- prove_correct no_rc_chain by
--     dsimp [no_rc_chain]
--     loom_solve

-- method cond_comm_base (s: concrete_st) (o1: op_t) (o2: op_t) (o3: op_t) return (u: Unit)
-- require (distinct_ops o1 o2 ∧ distinct_ops o2 o3 ∧ distinct_ops o1 o3
--     ∧ rc o1 o2 = rc_res.Fst_then_snd ∧ ¬(rc o2 o3 = rc_res.Either))
-- ensures eq (do_ (do_ (do_ s o1) o2) o3) (do_ (do_ (do_ s o2) o1) o3)
-- do
--     return ()

-- prove_correct cond_comm_base by
--     dsimp [cond_comm_base]
--     loom_solve



-- method merge_comm (l: concrete_st) (a: concrete_st) (b: concrete_st) return (u: Unit)
-- ensures eq (merge l a b) (merge l b a)
-- do
--     return ()

-- prove_correct merge_comm by
--     dsimp [merge_comm]
--     loom_solve


-- method merge_idem (s: concrete_st)return (u: Unit)
-- ensures eq (merge s s s) s
-- do
--     return ()

-- prove_correct merge_idem by
--     dsimp[merge_idem]
--     loom_solve


-- method base_2op (o1: op_t) (o2: op_t) return (u: Unit)
-- require (rc o2 o1 = rc_res.Fst_then_snd ∨ rc o2 o1 = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ distinct_ops o1 o2
-- ensures eq (merge init_st (do_ init_st o1) (do_ init_st o2)) (do_ (merge init_st init_st (do_ init_st o2)) o1)
-- do
--     return ()

-- prove_correct base_2op by
--     dsimp [base_2op]
--     loom_solve

-- method ind_lca_2op (l: concrete_st) (o1: op_t) (o2: op_t) (ol: op_t) return (u: Unit)
-- require (rc o2 o1 = rc_res.Fst_then_snd ∨ rc o2 o1 = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ distinct_ops o1 o2 ∧ distinct_ops o1 ol ∧ distinct_ops o2 ol ∧ eq (merge (do_ l ol) (do_ (do_ l ol) o1) (do_ l ol)) (do_ (merge (do_ l ol) (do_ l ol) (do_ l ol)) o1) ∧ eq (merge l (do_ l o1) (do_ l o2)) (do_ (merge l l (do_ l o2)) o1)
-- ensures eq (merge (do_ l ol) (do_ (do_ l ol) o1) (do_ (do_ l ol) o2)) (do_ (merge (do_ l ol) (do_ l ol) (do_ (do_ l ol) o2)) o1)
-- do
--     return ()



-- theorem mem_empty: forall (x:mytype) (s: Set mytype),  s = {} ∧ (x ∈ s) → False := by
-- intros
-- aesop


-- theorem equal_intro (s1 s2: Set mytype): (∀ (x:mytype), x ∈ s1 ↔ x ∈ s2) → s1 = s2  :=
-- by
-- rw [Set.ext_iff]
-- intros h
-- assumption


-- @[grind]
-- theorem mem_union (s1 s2: Set mytype) (x:mytype) :
-- x ∈ (s1 ∪ s2) ↔ (x ∈ s1 ∨ x ∈ s2) := by
-- rw [Set.mem_union]



-- @[grind]
-- theorem mem_singleton (x y: mytype) (s: Set mytype):
-- s = {x} → y ∈ s → y = x := by
-- intros h1 h2
-- rw [h1] at h2
-- rw [Set.mem_singleton_iff] at h2
-- assumption


-- @[grind]
-- theorem mem_intersection (s1 s2: Set mytype) (x:mytype) :
-- x ∈ (s1 ∩ s2) ↔ (x ∈ s1 ∧ x ∈ s2) := by
-- rw [Set.mem_inter_iff]



-- @[grind]
-- theorem mem_complement (s: Set mytype) (x: mytype) :
-- x ∈ sᶜ ↔ x ∉ s := by
-- rw [Set.mem_compl_iff]


-- prove_correct ind_lca_2op by
--     dsimp [ind_lca_2op]
--     loom_solve
--     {
--       simp [insert, Set.insert, Set.instInter, Set.inter, Set.instUnion, Set.union] at *
--       rw [Set.ext_iff] at a_5
--       rw [Set.ext_iff] at a_6
--       ext
--       simp at *
--       aesop
--       sorry
--     }
--     {
--       simp [insert, Set.insert, Set.instInter, Set.inter, Set.instUnion, Set.union, Set.instMembership, Set.Mem] at *
--       rw [Set.ext_iff] at a_5
--       rw [Set.ext_iff] at a_6
--       ext
--       simp at *
--       aesop
--       linarith
--       sorry
--     }
--     sorry
--     sorry
--     sorry
--     sorry



-- method inter_right_base_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ob: op_t) (ol: op_t) return (u: Unit)
-- require (rc o2 o1 = rc_res.Fst_then_snd ∨ rc o2 o1 = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ rc ob o1 = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧ distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o2 ob ∧ distinct_ops o2 ol ∧ distinct_ops ob ol ∧
--                     eq (merge l (do_ a o1) (do_ b o2)) (do_ (merge l a (do_ b o2)) o1) ∧
--                     eq (merge l (do_ a o1) (do_ (do_ b ob) o2)) (do_ (merge l a (do_ (do_ b ob) o2)) o1) ∧
--                     eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ol) o2)) o1)
-- ensures eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ b ob) ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ b ob) ol) o2)) o1)
-- do
--     return ()

-- prove_correct inter_right_base_2op by
--     dsimp [inter_right_base_2op]
--     loom_solve

-- method inter_left_base_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ob: op_t) (ol: op_t) return (u: Unit)
-- require (rc o2 o1) = rc_res.Fst_then_snd ∧ (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid o2 != get_rid o1 ∧ get_rid ob != get_rid ol ∧
--                     distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o2 ob ∧ distinct_ops o2 ol ∧ distinct_ops ob ol ∧
--                     eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ol) o2)) o1)
-- ensures eq (merge (do_ l ol) (do_ (do_ (do_ a ob) ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ (do_ a ob) ol) (do_ (do_ b ol) o2)) o1)
-- do
--     return ()

-- prove_correct inter_left_base_2op by
--     dsimp [inter_left_base_2op]
--     loom_solve


-- method inter_right_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ob: op_t) (ol: op_t) return (u: Unit)
-- require ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
--                     (¬ ((rc o ob) = rc_res.Either) ∨ (rc o ol) = rc_res.Fst_then_snd) ∧
--                     distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops o2 ob ∧
--                     distinct_ops o2 ol ∧ distinct_ops o2 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧
--                     get_rid o != get_rid ol ∧
--                     eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ b ob) ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ b ob) ol) o2)) o1)
-- ensures eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ (do_ b o) ob) ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ (do_ b o) ob) ol) o2)) o1)
-- do
--     return ()

-- prove_correct inter_right_2op by
--     dsimp[inter_right_2op]
--     loom_solve


-- method inter_left_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ob: op_t) (ol: op_t) return (u: Unit)
-- require (rc o2 o1) = rc_res.Fst_then_snd ∧ (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid o2 != get_rid o1 ∧ get_rid ob != get_rid ol ∧
--                     (¬ ((rc o ob) = rc_res.Either) ∨ (rc o ol) = rc_res.Fst_then_snd) ∧
--                     distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops o2 ob ∧
--                     distinct_ops o2 ol ∧ distinct_ops o2 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧
--                     get_rid o != get_rid ol ∧
--                     eq (merge (do_ l ol) (do_ (do_ (do_ a ob) ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ (do_ a ob) ol) (do_ (do_ b ol) o2)) o1)
-- ensures  eq (merge (do_ l ol) (do_ (do_ (do_ (do_ a o) ob) ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ (do_ (do_ a o) ob) ol) (do_ (do_ b ol) o2)) o1)
-- do
--     return ()

-- prove_correct inter_left_2op by
--     dsimp [inter_left_2op]
--     loom_solve

-- method inter_lca_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ol: op_t) return (u: Unit)
-- require ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧
--                     distinct_ops o1 o2 ∧ distinct_ops o1 ol ∧ distinct_ops o2 ol ∧
--                     (exists o, (rc o ol) = rc_res.Fst_then_snd) ∧
--                     eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b ol)) o1) ∧
--                     eq (merge l (do_ a o1) (do_ b o2)) (do_ (merge l a (do_ b o2)) o1)
-- ensures   eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ol) o2)) o1)
-- do
--     return ()

-- prove_correct inter_lca_2op by
--     dsimp [inter_lca_2op]
--     loom_solve

-- method ind_right_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (o2': op_t) return (u: Unit)
-- require (rc o2 o1) = rc_res.Fst_then_snd ∧ get_rid o1 != get_rid o2 ∧
--                     distinct_ops o1 o2 ∧ distinct_ops o1 o2' ∧ distinct_ops o2 o2' ∧
--                     eq (merge l (do_ a o1) (do_ b o2)) (do_ (merge l a (do_ b o2)) o1)
-- ensures eq (merge l (do_ a o1) (do_ (do_ b o2') o2)) (do_ (merge l a (do_ (do_ b o2') o2)) o1)
-- do
--     return ()

-- prove_correct ind_right_2op by
--     dsimp [ind_right_2op]
--     loom_solve


-- method ind_left_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (o1': op_t) return (u: Unit)
-- require  ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧
--                     distinct_ops o1 o2 ∧ distinct_ops o1 o1' ∧ distinct_ops o2 o1' ∧
--                     eq (merge l (do_ a o1) (do_ b o2)) (do_ (merge l a (do_ b o2)) o1)

-- ensures  eq (merge l (do_ (do_ a o1') o1) (do_ b o2)) (do_ (merge l (do_ a o1') (do_ b o2)) o1)
-- do
--     return ()

-- prove_correct ind_left_2op by
--     dsimp [ind_left_2op]
--     loom_solve


-- method base_1op (o1: op_t) return (u: Unit)
-- ensures eq (merge init_st (do_ init_st o1) init_st) (do_ (merge init_st init_st init_st) o1)
-- do
--     return ()

-- prove_correct base_1op by
--     dsimp [base_1op]
--     loom_solve

-- method ind_lca_1op (l: concrete_st) (o1: op_t) (ol: op_t) return (u: Unit)
-- require  distinct_ops o1 ol ∧
--                     (get_rid o1 != get_rid ol ∨ Prod.fst ol < Prod.fst o1) ∧
--                     eq (merge l (do_ l o1) l) (do_ (merge l l l) o1)
-- ensures  eq (merge (do_ l ol) (do_ (do_ l ol) o1) (do_ l ol)) (do_ (merge (do_ l ol) (do_ l ol) (do_ l ol)) o1)
-- do
--     return ()

-- prove_correct ind_lca_1op by
--     dsimp [ind_lca_1op]
--     loom_solve



-- method inter_right_base_1op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ob: op_t) (ol: op_t) return (u: Unit)
-- require (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
--                     distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops ob ol ∧
--                     ((rc ob o1) = rc_res.Fst_then_snd → eq (merge l (do_ a o1) (do_ b ob)) (do_ (merge l a (do_ b ob)) o1)) ∧
--                     eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b ol)) o1)
-- ensures  eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ob) ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ob) ol)) o1)
-- do
--     return ()


-- prove_correct inter_right_base_1op by
--     dsimp [inter_right_base_1op]
--     loom_solve


-- method inter_left_base_1op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ob: op_t) (ol: op_t) return (u: Unit)
-- require (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
--                     distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops ob ol ∧
--                     eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b ol)) o1)
-- ensures  eq (merge (do_ l ol) (do_ (do_ (do_ a ob) ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ (do_ a ob) ol) (do_ b ol)) o1)
-- do
--     return ()

-- prove_correct inter_left_base_1op by
--     dsimp [inter_left_base_1op]
--     loom_solve


-- method inter_right_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ob: op_t) (ol: op_t) (o: op_t) return (u: Unit)
-- require rc ob ol =  rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧ (¬(rc o ob = rc_res.Either) ∨ (rc o ol = rc_res.Fst_then_snd)) ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧ get_rid o != get_rid ol ∧ eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ob) ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ob) ol)) o1)
-- ensures eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ b o) ob) ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ b o) ob) ol)) o1)
-- do
--     return ()


-- prove_correct inter_right_1op by
--     dsimp [inter_right_1op]
--     loom_solve


-- method inter_left_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ob: op_t) (ol: op_t) (o: op_t) return (u: Unit)
-- require (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
--                     (¬ ((rc o ob) = rc_res.Either) ∨ (rc o ol) = rc_res.Fst_then_snd) ∧
--                     distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧
--                     get_rid o != get_rid ol ∧
--                     eq (merge (do_ l ol) (do_ (do_ (do_ a ob) ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ (do_ a ob) ol) (do_ b ol)) o1)
-- ensures  eq (merge (do_ l ol) (do_ (do_ (do_ (do_ a o) ob) ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ (do_ (do_ a o) ob) ol) (do_ b ol)) o1)
-- do
--     return ()

-- prove_correct inter_left_1op by
--     dsimp [inter_left_1op]
--     loom_solve

-- method inter_lca_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ol: op_t) (oi: op_t) return (u: Unit)
-- require  distinct_ops o1 ol ∧ distinct_ops o1 oi ∧ distinct_ops ol oi ∧
--                     (exists o, (rc o ol) = rc_res.Fst_then_snd) ∧
--                     (exists o, (rc o oi) = rc_res.Fst_then_snd) ∧
--                     eq (merge (do_ l oi) (do_ (do_ a oi) o1) (do_ b oi)) (do_ (merge (do_ l oi) (do_ a oi) (do_ b oi)) o1) ∧
--                     eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b ol)) o1)
-- ensures  eq (merge (do_ (do_ l oi) ol) (do_ (do_ (do_ a oi) ol) o1) (do_ (do_ b oi) ol))
--                       (do_ (merge (do_ (do_ l oi) ol) (do_ (do_ a oi) ol) (do_ (do_ b oi) ol)) o1)
-- do
--     return ()

-- prove_correct inter_lca_1op by
--     dsimp [inter_lca_1op]
--     loom_solve


-- method ind_left_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o1': op_t) (ol: op_t) return (u: Unit)
-- require  distinct_ops o1 o1' ∧ distinct_ops o1 ol ∧ distinct_ops o1' ol ∧
--                     eq (merge (do_ l ol) (do_ a o1) (do_ b ol)) (do_ (merge (do_ l ol) a (do_ b ol)) o1)
-- ensures  eq (merge (do_ l ol) (do_ (do_ a o1') o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a o1') (do_ b ol)) o1)
-- do
--     return ()

-- prove_correct ind_left_1op by
--     dsimp [ind_left_1op]
--     loom_solve

-- method ind_right_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o2: op_t) (o2': op_t) (ol: op_t)  return (u: Unit)
-- require distinct_ops o2 o2' ∧ distinct_ops o2 ol ∧ distinct_ops o2' ol ∧
--                     eq (merge (do_ l ol) (do_ a ol) (do_ b o2)) (do_ (merge (do_ l ol) (do_ a ol) b) o2)
-- ensures  eq (merge (do_ l ol) (do_ a ol) (do_ (do_ b o2') o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b o2')) o2)
-- do
--     return ()

-- prove_correct ind_right_1op by
--     dsimp [ind_right_1op]
--     loom_solve


-- method lem_0op (l: concrete_st) (a: concrete_st) (b: concrete_st) (ol: op_t) return (u: Unit)
-- ensures  eq (merge (do_ l ol) (do_ a ol) (do_ b ol)) (do_ (merge l a b) ol)
-- do
--     return ()

-- prove_correct lem_0op by
--     dsimp [lem_0op]
--     loom_solve
