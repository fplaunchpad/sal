import Sal.Interfaces.Set_Extended
import Sal.MRDTs.Grow_Only_Set.Grow_Only_Set_MRDT

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000
open Classical

/-! # Grow_Only_Set (MRDT): read-side projection

Same shape as the CRDT but on the three-way merge. The lookup is
`mem e`; `Add e` makes `e` live; once live, always live. -/

def lookup (s : concrete_st) (e : ℕ) : Bool := mem e s

theorem lookup_convergent (s₁ s₂ : concrete_st) (e : ℕ) :
    eq s₁ s₂ → lookup s₁ e = lookup s₂ e := by
  intro h; subst h; rfl

/-- **Add e** makes `e` live. -/
theorem lookup_after_add (s : concrete_st) (ts rid e : ℕ) :
    lookup (do_ s (ts, rid, e)) e = true := by
  simp [lookup, do_, mem, add]
