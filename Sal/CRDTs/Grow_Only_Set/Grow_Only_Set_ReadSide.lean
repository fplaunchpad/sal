import Sal.Interfaces.Set_Extended
import Sal.CRDTs.Grow_Only_Set.Grow_Only_Set_CRDT

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000
open Classical

/-! # Grow_Only_Set (CRDT): read-side projection

The 24 VCs prove the set converges under union. The headline read
is `lookup e`: is element `e` in the set? `Add e` makes `e` live;
elements never become dead. -/

def lookup (s : concrete_st) (e : ℕ) : Bool := mem e s

theorem lookup_convergent (s₁ s₂ : concrete_st) (e : ℕ) :
    eq s₁ s₂ → lookup s₁ e = lookup s₂ e := by
  intro h; subst h; rfl

/-- **Add e** makes `e` live. -/
theorem lookup_after_add (s : concrete_st) (ts rid e : ℕ) :
    lookup (do_ s (ts, rid, app_op_t.Add e)) e = true := by
  simp [lookup, do_, mem, add]

/-- **Membership grows monotonically.** Anything live before remains live. -/
theorem lookup_monotone (s : concrete_st) (ts rid e e' : ℕ) :
    lookup s e = true → lookup (do_ s (ts, rid, app_op_t.Add e')) e = true := by
  intro h
  simp [lookup, do_, mem, add] at *
  grind
