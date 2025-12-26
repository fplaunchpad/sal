import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

import Blaster

theorem fst_of_two_props :
∀a b : Prop, a → b → a :=
by
intro a b ha hb
apply ha


@[simp]
def reverse {α: Type} (xs : List α) :=
match xs with
| [] => []
| y::ys => (reverse ys) ++ [y]

theorem reverse_append_tactical {α : Type} (xs ys : List α) :
reverse (xs ++ ys) = reverse ys ++ reverse xs :=
by
induction xs with
| nil => simp
| cons x xs' ih => simp [reverse, ih]

inductive myEven : ℕ → Prop where
  | zero    : myEven 0
  | add_two : ∀k : ℕ, myEven k → myEven (k + 2)


example: myEven 4 := by
apply myEven.add_two
apply myEven.add_two
apply myEven.zero

/- ## Tactic Combinators

When programming our own tactics, we often need to repeat some actions on
several goals, or to recover if a tactic fails. Tactic combinators help in such
cases.

`repeat'` applies its argument repeatedly on all (sub…sub)goals until it cannot
be applied any further. -/

theorem repeat'_example :
    myEven 4 ∧ myEven 8 ∧ myEven 16 ∧ myEven 0 :=
  by
    repeat' apply And.intro
    repeat' apply myEven.add_two
    repeat' apply myEven.zero

/- The "first" combinator `first | ⋯ | ⋯ | ⋯` tries its first argument. If that
fails, it applies its second argument. If that fails, it applies its third
argument. And so on. -/

theorem repeat'_first_example :
    myEven 4 ∧ myEven 7 ∧ myEven 3 ∧ myEven 0 :=
  by
    repeat' apply And.intro
    repeat'
      first
      | apply myEven.add_two
      | apply myEven.zero
    repeat' sorry

/- `all_goals` applies its argument exactly once to each goal. It succeeds only
if the argument succeeds on **all** goals. -/

/-
theorem all_goals_example :
    myEven 4 ∧ myEven 7 ∧ myEven 3 ∧ myEven 0 :=
  by
    repeat' apply And.intro
    all_goals apply myEven.add_two   -- fails
    repeat' sorry
-/

/- `try` transforms its argument into a tactic that never fails. -/

theorem all_goals_try_example :
    myEven 4 ∧ myEven 7 ∧ myEven 3 ∧ myEven 0 :=
  by
    repeat' apply And.intro
    all_goals try apply myEven.add_two
    repeat sorry

/- `any_goals` applies its argument exactly once to each goal. It succeeds
if the argument succeeds on **any** goal. -/

theorem any_goals_example :
    myEven 4 ∧ myEven 7 ∧ myEven 3 ∧ myEven 0 :=
  by
    repeat' apply And.intro
    any_goals apply myEven.add_two
    repeat' sorry


/- using Grind -/

example {α} (f g : α → α) (x y : α)
(h1 : x = y) (h2 : f y = g y) :
f x = g x :=
by
-- After `h1`, `x` and `y` share a class,
-- `h2` adds `f y = g y`, and
-- closure bridges to `f x = g x`
grind


/- E-matching is a mechanism used by grind to instantiate theorems efficiently.
It is especially effective when combined with congruence closure, enabling grind to
discover non-obvious consequences of equalities and annotated theorems automatically.-/

def f (a : Nat) : Nat :=
  a + 1

def g (a : Nat) : Nat :=
  a - 1

@[grind?]
theorem gf (x : Nat) : g (f x) = x :=
by
simp [f, g]

example {a b} (h : f b = a) : g a = b :=
by
grind

example (h₁ : f b = a) (h₂ : f c = a) : b = c :=
by
grind

/--
trace: [grind.ematch.instance] gf: g (f c) = c
[grind.ematch.instance] gf: g (f b) = b
-/
example (h₁ : f b = a) (h₂ : f c = a) : b = c :=
by
set_option trace.grind.ematch.instance true in
grind
