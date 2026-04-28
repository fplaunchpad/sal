import Std.Tactic.BVDecide
import Sal.Interfaces.Map_Extended
import Sal.Tactic.Sal
import Sal.CRDTs.LWW_Map.LWW_Map_CRDT
import Mathlib

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

open scoped Classical
set_option maxHeartbeats 400000
set_option relaxedAutoImplicit false
set_option autoImplicit false
open Classical

/-! # LWW_Map (CRDT) — read-side projection

The 24 VCs prove the per-key `(ts, value)` map converges under
per-key lex-max. The headline read is `lookup k`: the value at key
`k`. A `Write k v` at strictly higher ts than the current
per-key timestamp installs `v`. -/

/-- Per-key value. -/
def lookup (s : concrete_st) (k : ℕ) : ℕ := Prod.snd (mysel s k)

/-- Per-key timestamp of the write that installed the current value. -/
def timestamp_at (s : concrete_st) (k : ℕ) : ℕ := Prod.fst (mysel s k)

theorem lookup_convergent (s₁ s₂ : concrete_st) (k : ℕ) :
    eq s₁ s₂ → lookup s₁ k = lookup s₂ k := by
  intro h_eq
  unfold lookup
  rw [(h_eq k).2]

/-- **Write at strictly newer ts installs the new value.** -/
theorem lookup_after_write_higher_ts
    (s : concrete_st) (k v ts rid : ℕ) (h_ts : ts > timestamp_at s k) :
    lookup (do_ s (ts, rid, app_op_t.Write k v)) k = v := by
  unfold lookup timestamp_at at *
  simp [do_, mysel, lex_max]
  split_ifs with h <;> simp_all <;> omega

/-- **Write at key k' does not affect key k.** -/
theorem lookup_unchanged_at_other_key
    (s : concrete_st) (k k' v ts rid : ℕ) (h_ne : k ≠ k') :
    lookup (do_ s (ts, rid, app_op_t.Write k' v)) k = lookup s k := by
  simp [lookup, do_, mysel, h_ne, Ne.symm h_ne]
