import Sal.CRDTs.LWW_Register.LWW_Register_CRDT

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 400000
open Classical

/-! # LWW_Register (CRDT) — read-side projection

The 24 VCs prove the `(ts, value)` pair converges under lexicographic
max. The headline read is `the value field of the lex-max pair`.
A `Write` with strictly higher ts overrides the prior value. -/

/-- The register's current value: the second component of the
lex-max pair. -/
def value (s : concrete_st) : ℕ := Prod.snd s

/-- The timestamp of the write that installed the current value. -/
def timestamp (s : concrete_st) : ℕ := Prod.fst s

theorem value_convergent (s₁ s₂ : concrete_st) :
    eq s₁ s₂ → value s₁ = value s₂ := by
  intro h; subst h; rfl

/-- **Write at strictly newer ts installs the new value.** -/
theorem value_after_write_higher_ts
    (s : concrete_st) (v ts rid : ℕ) (h_ts : ts > timestamp s) :
    value (do_ s (ts, rid, app_op_t.Write v)) = v := by
  simp [value, timestamp, do_, lex_max] at *
  split_ifs <;> omega

/-- **Write at older ts is ignored.** -/
theorem value_after_write_lower_ts
    (s : concrete_st) (v ts rid : ℕ) (h_ts : ts < timestamp s) :
    value (do_ s (ts, rid, app_op_t.Write v)) = value s := by
  simp [value, timestamp, do_, lex_max] at *
  split_ifs <;> omega
