import CaseStudies.Tactics.Sal
import Mathlib.Data.Nat.Basic

-- Example 1: Simple arithmetic proof
example (a b : Nat) : a + b = b + a := by
  sal

-- Example 2: List property
example (xs ys : List α) : (xs ++ ys).length = xs.length + ys.length := by
  sal

-- Example 3: Boolean logic
example (p q : Prop) [Decidable p] [Decidable q] : (p ∧ q) → p := by
  sal

-- Example 4: More complex proof
theorem nat_add_comm (a b : Nat) : a + b = b + a := by
  sal

-- You can also use sal in the middle of a proof
example (a b c : Nat) (h : a = b) : a + c = b + c := by
  rw [h]
  sal











