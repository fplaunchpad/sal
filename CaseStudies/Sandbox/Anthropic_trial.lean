import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Std.Tactic.BVDecide


@[simp]
abbrev set (a:Type) [DecidableEq a] := a → Bool

@[simp, grind]
def equal {a:Type} [DecidableEq a] (s1: set a) (s2: set a)
:= ∀ x : a, s1 x == s2 x

@[simp, grind]
def empty {a:Type} [DecidableEq a] : set a := fun x => false

@[simp, grind]
def singleton {a:Type} [DecidableEq a] (x: a): set a := fun y => y = x

@[simp, grind]
def union {a:Type} [DecidableEq a] (s1 s2 : set a) : set a :=
(fun x => s1 x || s2 x)

@[simp, grind]
def intersection {a:Type} [DecidableEq a] (s1 s2: set a) : set a :=
(fun x => s1 x && s2 x)

@[simp, grind]
def complement {a:Type} [DecidableEq a] (s : set a) : set a :=
(fun x => not (s x))

@[simp, grind ]
def mem {a:Type} [DecidableEq a] (x: a) (s: set a) : Bool :=
s x

@[simp, grind]
def difference {a:Type}  [DecidableEq a] (s1 s2: set a) : set a :=
(fun x => s1 x && not (s2 x))

@[simp, grind]
def filter {a:Type}  [DecidableEq a] (s1: set a) (p: a → Bool) : set a :=
(fun x => s1 x && p x)

@[simp, grind]
def remove {a: Type} [DecidableEq a] (s1: set a) x :=
(fun y => s1 y && x != y)

@[simp, grind]
def subset {a: Type} [DecidableEq a] (s1 s2: set a) :=
forall x, mem x s1 → mem x s2

@[simp, grind]
def add {a: Type} [DecidableEq a] (x:a) (s: set a) : set a :=
union s (singleton x)


@[simp, grind?]
lemma mem_empty {a: Type} [DecidableEq a] (x: a) :
not (mem x empty) := by simp

grind_pattern mem_empty => (mem x empty)



@[simp]
lemma equal_intro {a: Type} [DecidableEq a] (s1 s2 : set a) :
(forall x:a, mem x s1 == mem x s2) → equal s1 s2 := by
simp


grind_pattern equal_intro => (equal s1 s2)

@[simp, grind?]
lemma equal_intro' {a: Type} [DecidableEq a] (s1 s2 : set a) :
equal s1 s2 ↔ s1 = s2 := by
simp
aesop



lemma equal_elim  {a: Type} [DecidableEq a] (s1 s2 : set a) :
equal s1 s2 → s1 = s2 := by
simp
aesop


grind_pattern equal_elim => equal s1 s2


@[simp, grind?]
lemma equal_refl  {a: Type} [DecidableEq a] (s1 s2 : set a) :
s1 = s2 → (forall x:a, mem x s1 == mem x s2) ∧ equal s1 s2 := by
simp
grind


lemma equal_refl' {a:Type} [DecidableEq a] (s1 s2: set a) :
equal s1 s2 ↔ (forall x:a, mem x s1 == mem x s2) := by
simp



@[simp, grind]
lemma equal_refl1 {a: Type} [DecidableEq a] (s: set a) :
equal s s := by simp


@[simp]
lemma mem_subset {a: Type} [DecidableEq a] (s1 s2: set a) :
(forall x, mem x s1 → mem x s2) → subset s1 s2 := by
simp

grind_pattern mem_subset => subset s1 s2

@[simp, grind?]
lemma subset_mem {a: Type} [DecidableEq a] (s1 s2: set a) :
subset s1 s2 → (forall x, mem x s1 → mem x s2) := by simp


@[simp]
lemma mem_union {a: Type} [DecidableEq a] (s1 s2: set a) (x:a) :
mem x (union s1 s2) ↔ (mem x s1 || mem x s2) := by simp

grind_pattern mem_union => mem x (union s1 s2)


@[simp]
lemma mem_singleton {a: Type} [DecidableEq a] (x y : a):
mem y (singleton x) = (x = y) := by
simp
grind

grind_pattern mem_singleton => mem y (singleton x)

@[simp]
lemma mem_intersection {a: Type} [DecidableEq a] (s1 s2: set a) (x: a) :
mem x (intersection s1 s2) ↔ (mem x s1 ∧ mem x s2) := by simp

grind_pattern mem_intersection => mem x (intersection s1 s2)

@[simp]
lemma mem_complement {a: Type} [DecidableEq a] (s: set a) (x: a) :
mem x (complement s) ↔ not (mem x s) := by simp

grind_pattern mem_complement => mem x (complement s)

@[simp]
lemma mem_difference {a: Type} [DecidableEq a] (s1 s2: set a) (x: a) :
mem x (difference s1 s2) ↔ (mem x s1 ∧ ¬ (mem x s2)) := by simp

grind_pattern mem_difference => mem x (difference s1 s2)

@[simp, grind?]
lemma mem_filter {a: Type} [DecidableEq a] (s: set a) (p: a → Bool) (x: a):
mem x (filter s p) ↔ (mem x s ∧ p x) := by simp

@[simp, grind?]
lemma mem_remove_x {a: Type} [DecidableEq a] (s: set a) (x: a):
not (mem x (remove s x)) := by simp

@[simp, grind?]
lemma mem_remove_y {a: Type} [DecidableEq a] (s: set a) (x: a) (y: a) :
x !=y → mem y (remove s x) == mem y s := by
simp
grind



structure map (key:Type) [DecidableEq key] (value:Type) where
(mappings: key → value) (domain: set key)

#check map.domain

@[simp, grind]
def sel {key:Type} [DecidableEq key] {value: Type} (m: map key value) (k:key)
:=
m.mappings k

@[simp, grind]
def upd {key:Type} [DecidableEq key] {value: Type} (m: map key value) (k:key) (v:value)
:=
map.mk (fun (x : key) => if x = k then v else m.mappings x) (union (m.domain) (singleton k))

@[simp, grind]
def const {key:Type} [DecidableEq key] {value: Type} (v:value) : map key value
:=
map.mk (fun _ => v) (complement empty)

@[simp, grind]
def domain {key:Type} [DecidableEq key] {value: Type} (m: map key value) := m.domain

@[simp, grind]
def del {key:Type} [DecidableEq key] {value: Type} (m: map key value) (k: key) :=
map.mk (fun x => m.mappings x) (remove (domain m) k)

@[simp, grind]
def contains {key:Type} [DecidableEq key] {value: Type} (m: map key value) (k: key)
:=
mem k m.domain

@[simp, grind]
def concat {key:Type} [DecidableEq key] {value: Type} (m1: map key value) (m2: map key value)
:=
map.mk (fun x => if mem x (m2.domain) then m2.mappings x else m1.mappings x) (union (m1.domain) (m2.domain))

@[simp, grind]
def map_val {val1: Type} {val2: Type} (f: val1 → val2) {key:Type} [DecidableEq key] (m: map key val1) : map key val2 :=
map.mk (fun x => f (m.mappings x)) (m.domain)

@[simp, grind]
def iter_upd {key:Type} [DecidableEq key] {val1: Type} {val2: Type} (f:key → val1 → val2) (m: map key val1): map key val2 :=
map.mk (fun x => f x (m.mappings x)) (m.domain)

@[simp, grind]
def restrict {key:Type} [DecidableEq key] {value: Type} (s: set key) (m: map key value): map key value :=
map.mk (m.mappings) (intersection s m.domain)

@[simp, grind]
def const_on {key:Type} [DecidableEq key] {value: Type} (dom: set key) (v: value) : map key value :=
restrict dom (const v)

@[simp, grind]
def disjoint_dom {key: Type} [DecidableEq key] {value:Type} (m1: map key value) (m2: map key value) :=
forall x, contains m1 x → not (contains m2 x)

@[simp, grind]
def has_dom {key: Type} [DecidableEq key] {value:Type} (m: map key value) (dom: set key) :=
forall x, contains m x ↔ mem x dom


@[simp, grind?]
lemma lemma_SelUpd1 {key: Type} [DecidableEq key] {value:Type} (m: map key value) (k:key) (v:value)
: sel (upd m k v) k = v
:= by
simp

@[simp, grind?]
lemma lemma_SelUpd2 {key: Type} [DecidableEq key] {value:Type} (m: map key value) (k1:key) (k2: key) (v:value) :
k2 != k1 → sel (upd m k2 v) k1 = sel m k1
:= by
simp
grind

@[simp, grind?]
lemma lemma_SelConst {key: Type} [DecidableEq key] {value:Type} (v: value) (k: key) :
sel (const v) k = v := by simp

@[simp, grind?]
lemma lemma_SelRestrict  {key: Type} [DecidableEq key] {value:Type} (m: map key value) (ks: set key) (k: key):
sel (restrict ks m) k = sel m k := by simp

@[simp, grind?]
lemma lemma_SelConcat1 {key: Type} [DecidableEq key] {value:Type} (m1: map key value) (m2: map key value) (k: key):
contains m2 k →  sel (concat m1 m2) k = sel m2 k := by
simp
grind

@[simp, grind?]
lemma lemma_SelConcat2 {key: Type} [DecidableEq key] {value:Type} (m1: map key value) (m2: map key value) (k: key):
not (contains m2 k) → sel (concat m1 m2) k = sel m1 k := by
simp
grind

@[simp, grind?]
lemma lemma_SelMapVal {val1: Type} {val2: Type} (f:val1 → val2) {key: Type} [DecidableEq key] (m: map key val1) (k:key) :
sel (map_val f m) k = f (sel m k) := by simp

@[simp, grind?]
lemma lemma_IterUpd {key:Type} [DecidableEq key] {val1: Type} {val2: Type} (f:key → val1 → val2) (m: map key val1) (k:key):
sel (iter_upd f m) k = f k (sel m k) := by simp

@[simp, grind?]
lemma lemma_InDomUpd1 {key: Type} [DecidableEq key] {value:Type} (m: map key value) (k1 k2: key) (v: value) :
contains (upd m k1 v) k2 = (k1=k2 || contains m k2) := by
simp
grind

@[simp, grind?]
lemma lemma_InDomUpd2 {key: Type} [DecidableEq key] {value:Type} (m: map key value) (k1 k2: key) (v: value) :
(k2 != k1 → contains (upd m k2 v) k1 = contains m k1) := by
simp
grind

@[simp, grind?]
lemma lemma_InDomConstMap {key: Type} [DecidableEq key] {value: Type} (v: value) (k: key) :
contains (const v) k := by simp

@[simp, grind?]
lemma lemma_InDomConcat {key: Type} [DecidableEq key] {value: Type} (m1: map key value) (m2: map key value) (k: key) :
contains (concat m1 m2) k = (contains m1 k || contains m2 k) := by simp

@[simp, grind?]
lemma lemma_InMapVal {val1: Type} {val2: Type} (f: val1 → val2) {key:Type} [DecidableEq key] (m: map key val1) (k: key) :
contains (map_val f m) k == contains m k := by simp

@[simp, grind?]
lemma lemma_InIterUpd {key:Type} [DecidableEq key] {val1: Type} {val2: Type} (f:key → val1 → val2) (m: map key val1) (k:key):
contains (iter_upd f m) k == contains m k := by simp

@[simp, grind?]
lemma lemma_InDomRestrict {key: Type} [DecidableEq key] {value:Type} (m: map key value) (ks: set key) (k: key) :
contains (restrict ks m) k == (mem k ks && contains m k) := by simp

@[simp, grind?]
lemma lemma_ContainsDom {key: Type} [DecidableEq key] {value:Type} (m: map key value) (k: key) :
contains m k = mem k (domain m) := by
simp

@[simp, grind?]
lemma lemma_UpdDomain {key: Type} [DecidableEq key] {value:Type} (m: map key value) (k: key) (v: value) :
equal (domain (upd m k v)) (union (domain m) (singleton k)) := by simp

@[simp]
def map_equal {key: Type} [DecidableEq key] {value: Type} (m1: map key value) (m2: map key value) :=
m1.mappings  = m2.mappings ∧ equal m1.domain m2.domain

@[simp, grind?]
theorem map_lemma_equal_intro  {key: Type} [DecidableEq key] {value: Type} (m1: map key value) (m2: map key value)  :
(forall k:key, sel m1 k = sel m2 k ∧ contains m1 k = contains m2 k) ↔ map_equal m1 m2 :=
by
simp
cases m1
cases m2
aesop

@[simp]
theorem map_lemma_equal_elim {key: Type} [DecidableEq key] {value: Type} (m1: map key value) (m2: map key value) :
map_equal m1 m2 ↔ m1 = m2 := by
dsimp
cases m1; cases m2
aesop


@[simp] abbrev concrete_st := map ℕ Int × map ℕ Int × map (ℕ × ℕ) Int
-- Increment map, decrement map, transfer map

@[simp]
def mysel {α : Type} [DecidableEq α] (s: map α Int) (k: α) : Int :=
if (contains s k) then (sel s k) else 0

@[simp]
def init_st : concrete_st:= (const_on empty 0, const_on empty 0, const_on empty 0)

@[simp]
def eq (a b: concrete_st) :=
(forall id, (contains (Prod.fst a) id = contains (Prod.fst b) id) ∧ (mysel (Prod.fst a) id = mysel (Prod.fst b) id)) ∧
(forall id, (contains (Prod.fst (Prod.snd a)) id = contains (Prod.fst (Prod.snd b)) id) ∧ (mysel (Prod.fst (Prod.snd a)) id = mysel (Prod.fst (Prod.snd b)) id)) ∧
(forall id, (contains (Prod.snd (Prod.snd a)) id = contains (Prod.snd (Prod.snd b)) id) ∧ (mysel (Prod.snd (Prod.snd a)) id = mysel (Prod.snd (Prod.snd b)) id))



-- Helper to get increment map from state
@[simp]
def get_inc (s: concrete_st) : map ℕ Int := Prod.fst s

-- Helper to get decrement map from state
@[simp]
def get_dec (s: concrete_st) : map ℕ Int := Prod.fst (Prod.snd s)

-- Helper to get transfer map from state
@[simp]
def get_transfers (s: concrete_st) : map (ℕ × ℕ) Int := Prod.snd (Prod.snd s)

-- Calculate a simplified value for the bounded counter
-- For a specific replica: its increments minus its decrements
@[simp]
def replica_value (replica: ℕ) (s: concrete_st) : Int :=
  mysel (get_inc s) replica - mysel (get_dec s) replica

-- Calculate the quota available for a replica
-- This is a simplified version: replica's own value plus net transfers
@[simp]
def quota (replica: ℕ) (s: concrete_st) : Int :=
  replica_value replica s

-- Increment operation - always succeeds (increment by 1)
@[simp]
def inc (replica: ℕ) (s: concrete_st) : concrete_st :=
  let inc_map := get_inc s
  let new_inc_map := upd inc_map replica (mysel inc_map replica + 1)
  (new_inc_map, get_dec s, get_transfers s)

-- Decrement operation - may fail if insufficient quota (decrement by 1)
def dec (replica: ℕ) (s: concrete_st) : Option concrete_st :=
  let q := quota replica s
  if q >= 1 then
    let dec_map := get_dec s
    let new_dec_map := upd dec_map replica (mysel dec_map replica + 1)
    some (get_inc s, new_dec_map, get_transfers s)
  else
    none

-- Transfer quota from sender to receiver - may fail if insufficient quota
def transfer (sender: ℕ) (receiver: ℕ) (amount: Int) (s: concrete_st) : Option concrete_st :=
  let q := quota sender s
  if q >= amount then
    let transfers := get_transfers s
    let pair := (sender, receiver)
    let new_transfers := upd transfers pair (mysel transfers pair + amount)
    some (get_inc s, get_dec s, new_transfers)
  else
    none

-- Merge operation for bounded counters
@[simp]
def merge (a b: concrete_st) : concrete_st :=
  -- Merge increment maps (take max like PN-Counter)
  let keys_inc := union (domain (get_inc a)) (domain (get_inc b))
  let u_inc := const_on keys_inc 0
  let merged_inc := iter_upd (fun k _ => max (mysel (get_inc a) k) (mysel (get_inc b) k)) u_inc

  -- Merge decrement maps (take max like PN-Counter)
  let keys_dec := union (domain (get_dec a)) (domain (get_dec b))
  let u_dec := const_on keys_dec 0
  let merged_dec := iter_upd (fun k _ => max (mysel (get_dec a) k) (mysel (get_dec b) k)) u_dec

  -- Merge transfer maps (take max - transfers are monotonically increasing)
  let keys_transfer := union (domain (get_transfers a)) (domain (get_transfers b))
  let u_transfer := const_on keys_transfer 0
  let merged_transfer := iter_upd (fun k _ => max (mysel (get_transfers a) k) (mysel (get_transfers b) k)) u_transfer

  (merged_inc, merged_dec, merged_transfer)

-- Operation types for the CRDT framework
inductive app_op_t : Type where
| Inc
| Dec
| Transfer (receiver: ℕ) (amount: ℕ)

abbrev op_t := ℕ × ℕ × app_op_t

@[simp]
def distinct_ops (op1 op2 : op_t) := Prod.fst op1 != Prod.fst op2

@[simp]
def get_rid (o : op_t) :=
match o with
| (_, (rid, _)) => rid

@[simp]
def do_ (s: concrete_st) (o: op_t) : concrete_st :=
match o with
| (_, (replica, app_op_t.Inc)) => inc replica s
| (_, (replica, app_op_t.Dec)) =>
    match dec replica s with
    | some s' => s'
    | none => s  -- If dec fails, state remains unchanged
| (_, (sender, app_op_t.Transfer receiver amount)) =>
    match transfer sender receiver amount s with
    | some s' => s'
    | none => s  -- If transfer fails, state remains unchanged

inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

@[simp]
def rc (_ _ : op_t) := rc_res.Either

@[simp]
def commutes_with (o1 o2 : op_t) :=
    forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)


theorem ind_lca_2op (l: concrete_st) (o1 o2 ol: op_t) :
 ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ol ∧ distinct_ops o2 ol ∧
                    eq (merge (do_ l o1) (do_ l o2)) (do_ (merge l (do_ l o2)) o1)
→
 eq (merge (do_ (do_ l ol) o1) (do_ (do_ l ol) o2)) (do_ (merge (do_ l ol) (do_ (do_ l ol) o2)) o1)
:= by sorry

theorem ind_left_2op (a b:concrete_st) (o1 o2 o1':op_t) :
 ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 o1' ∧ distinct_ops o2 o1' ∧
                    eq (merge (do_ a o1) (do_ b o2)) (do_ (merge a (do_ b o2)) o1)
→
 eq (merge (do_ (do_ a o1') o1) (do_ b o2)) (do_ (merge (do_ a o1') (do_ b o2)) o1)
:= by sorry

theorem ind_left_1op (a b:concrete_st) (o1 o1' ol:op_t) :
 distinct_ops o1 o1' ∧ distinct_ops o1 ol ∧ distinct_ops o1' ol ∧
                    eq (merge (do_ a o1) (do_ b ol)) (do_ (merge a (do_ b ol)) o1)
→
 eq (merge (do_ (do_ a o1') o1) (do_ b ol)) (do_ (merge (do_ a o1') (do_ b ol)) o1)
 := by sorry



theorem ind_right_1op (a b: concrete_st) (o2 o2' ol:op_t) :
 distinct_ops o2 o2' ∧ distinct_ops o2 ol ∧ distinct_ops o2' ol ∧
                    eq (merge (do_ a ol) (do_ b o2)) (do_ (merge (do_ a ol) b) o2)
→
 eq (merge (do_ a ol) (do_ (do_ b o2') o2)) (do_ (merge (do_ a ol) (do_ b o2')) o2)
:= by sorry



theorem lem_0op (a b:concrete_st) (ol:op_t) :
eq (merge (do_ a ol) (do_ b ol)) (do_ (merge a b) ol) := by sorry
