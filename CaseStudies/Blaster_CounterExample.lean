import Mathlib.Data.Real.Basic
import Blaster

@[simp]
abbrev set (a:Type) [DecidableEq a] := a → Bool

@[simp, grind]
def equal {a:Type} [DecidableEq a] (s1: set a) (s2: set a)
:= s1 = s2

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

@[simp, grind]
def mem {a:Type} [DecidableEq a] (x: a) (s: set a) : Bool :=
s x

@[simp, grind]
def remove {a: Type} [DecidableEq a] (s1: set a) x :=
(fun y => s1 y && x != y)

@[simp, grind]
def subset {a: Type} [DecidableEq a] (s1 s2: set a) :=
forall x, mem x s1 → mem x s2

@[simp, grind]
def add {a: Type} [DecidableEq a] (x:a) (s: set a) : set a :=
union s (singleton x)

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
map.mk (fun x => if x = k then v else m.mappings x) (union (m.domain) (singleton k))

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
def iter_upd {key:Type} [DecidableEq key] {val1: Type} {val2: Type} (f:key → val1 → val2) (m: map key val1): map key val2 :=
map.mk (fun x => f x (m.mappings x)) (m.domain)

@[simp, grind]
def restrict {key:Type} [DecidableEq key] {value: Type} (s: set key) (m: map key value): map key value :=
map.mk (m.mappings) (intersection s m.domain)

@[simp, grind]
def const_on {key:Type} [DecidableEq key] {value: Type} (dom: set key) (v: value) : map key value :=
restrict dom (const v)

@[simp] abbrev concrete_st := map ℕ Int
/- keys: replicas IDs, values: int -/

@[simp]
def mysel (s: concrete_st) (k: ℕ) : Int :=
if (contains s k) then (sel s k) else 0

@[simp]
def init_st : concrete_st := const_on empty 0

@[simp]
def eq (a b: concrete_st) := (forall id:ℕ, (contains a id = contains b id) ∧ (mysel a id = mysel b id))

inductive app_op_t : Type where
| Incr

abbrev op_t:= ℕ × ℕ × app_op_t

@[simp]
def distinct_ops (op1 op2 : op_t) := Prod.fst op1 != Prod.fst op2

@[simp]
def get_rid (o : op_t) :=
match o with
| (_, (rid, _)) => rid

@[simp]
def do_ (s: concrete_st) (o: op_t) : concrete_st :=
match o with
| (_, (r, _)) => upd s r (mysel s r + 1)

inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

@[simp]
def rc (o1 o2 : op_t) := rc_res.Either

@[simp]
def commutes_with (o1 o2 : op_t) :=
    forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)

@[simp]
def merge (a b: concrete_st) : concrete_st :=
let keys := union (domain a) (domain b)
let u := const_on keys 0
iter_upd (fun k v => max (mysel a k) (mysel b k)) u

theorem merge_comm (a b: concrete_st) :
eq (merge a b) (merge b a) := by
simp
grind
