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


abbrev concrete_st := Int × Bool

@[simp]
def init_st: concrete_st := (0, false)

@[simp]
def eq (a b: concrete_st) := (a = b)

inductive app_op_t : Type where
| Enable
| Disable

abbrev op_t:= ℕ × ℕ × app_op_t

@[simp]
def distinct_ops (op1 op2: op_t) := Prod.fst op1 != Prod.fst op2

@[simp]
def get_rid (o: op_t) :=
match o with
| (_, (rid, _)) => rid

@[simp]
def do_ (s:concrete_st) (o: op_t) : concrete_st
:= match o with
| (_, (rid, .Enable)) => (Prod.fst s + 1, true)
| (_, (rid, .Disable)) => (Prod.fst s, false)


inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

@[simp]
def rc (o1 o2: op_t) :=
match (Prod.snd (Prod.snd o1), Prod.snd (Prod.snd o2)) with
| (.Enable, .Disable) => rc_res.Snd_then_fst
| (.Disable, .Enable) => rc_res.Fst_then_snd
| _ => rc_res.Either

@[simp]
def merge_flag (l a b: concrete_st) :=
  if Prod.snd a && Prod.snd b then true
  else if not (Prod.snd a) && not (Prod.snd b) then false
  else if Prod.snd a then Prod.fst a > Prod.fst l
  else Prod.fst b > Prod.fst l

@[simp]
def merge (l a b: concrete_st) : concrete_st
:= (Prod.fst a + Prod.fst b - Prod.fst l , merge_flag l a b)

@[simp]
def commutes_with (o1 o2: op_t) :=
    forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)

theorem inter_right_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ob: op_t) (ol: op_t) (o: op_t) :
rc ob ol =  rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧ (¬(rc o ob = rc_res.Either) ∨ (rc o ol = rc_res.Fst_then_snd)) ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧ get_rid o != get_rid ol ∧ eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ob) ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ob) ol)) o1)
→
eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ b o) ob) ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ b o) ob) ol)) o1)
:= by sorry

example : False := by sorry
