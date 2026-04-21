import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Std.Tactic.BVDecide
import Blaster

macro "neem" : tactic =>
  `(tactic| first | grind | blaster)

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
