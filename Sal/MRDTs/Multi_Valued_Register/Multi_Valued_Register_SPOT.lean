import Sal.Interfaces.Set_Extended
import Sal.MRDTs.Multi_Valued_Register.Multi_Valued_Register_MRDT
import Sal.MRDTs.Multi_Valued_Register.Multi_Valued_Register_ReadSide

set_option linter.mathlibStandardSet false

open Classical

/-! # Multi-Valued Register (MRDT, classical): SPOTs

Small Proof-Oriented Tests: concrete `do`/`merge` scenarios with
expected `is_visible_value` outcomes, machine-checked. Two roles:

* **regression tests**: small instances of the operational semantics
  proved by reduction (cheap path, this file);
* **verified API documentation**: the same scenarios that the
  `demos/` MVR page renders interactively, here pinned by proof.

Each SPOT is named after the headline read-side claim it exercises.
Reference: Shapiro et al. INRIA RR-7506 §3.2.2 Spec 14. -/

namespace MVR_SPOT

/-- **SPOT 1: concurrent writes both visible.**

Two replicas concurrently `Write` distinct values from the initial
state (each with empty prepare-time snapshot, since neither sees the
other). After three-way merge against the empty LCA, both values are
visible. -/
example :
    let σ_a : concrete_st := do_ init_st (1, 0, app_op_t.Write 42 empty)
    let σ_b : concrete_st := do_ init_st (2, 1, app_op_t.Write 99 empty)
    let σ  : concrete_st := merge init_st σ_a σ_b
    is_visible_value σ 42 ∧ is_visible_value σ 99 := by
  refine ⟨⟨1, ?_, ?_⟩, ⟨2, ?_, ?_⟩⟩ <;> decide

/-- **SPOT 2: sequential write supersedes prior.**

A single replica writes `42` (ts = 1), then writes `99` (ts = 2) with
prepare-time snapshot `{1}` (it has observed the prior write). The
prior `42` is no longer visible because its only witness ts is now
in `removed`. The negative half applies
`sequential_write_supersedes_value`, `99 ≠ 42` and σ₁'s only visible
witness for `42` is `ts = 1`, which is in `O₂ = {1}`. -/
example :
    let σ₁ : concrete_st := do_ init_st (1, 0, app_op_t.Write 42 empty)
    let σ₂ : concrete_st := do_ σ₁ (2, 0, app_op_t.Write 99 (add 1 empty))
    is_visible_value σ₂ 99 ∧ ¬ is_visible_value σ₂ 42 := by
  refine ⟨⟨2, ?_, ?_⟩, ?_⟩
  · decide
  · decide
  · apply sequential_write_supersedes_value
      (do_ init_st (1, 0, app_op_t.Write 42 empty)) 42 99 2 0 (add 1 empty)
      (by decide)
    intro ts h_in _
    simp [do_, add, _root_.singleton, init_st, _root_.empty] at h_in
    subst h_in
    decide

/-- **SPOT 3: concurrent writes both supersede a common ancestor.**

Replica 0 writes `42` (ts = 1). Replicas 1 and 2 each fork from this
state and concurrently write `99` (ts = 2) and `77` (ts = 3) with
prepare-time snapshot `{1}`. After three-way merge against the
common ancestor, both `99` and `77` are visible while `42` is not.

This is the distinctive classical-MVR shape: concurrent writes
survive (cf. SPOT 1), and they jointly retire any write they both
observed (cf. SPOT 2). -/
example :
    let σ_pre : concrete_st := do_ init_st (1, 0, app_op_t.Write 42 empty)
    let σ_a   : concrete_st := do_ σ_pre (2, 1, app_op_t.Write 99 (add 1 empty))
    let σ_b   : concrete_st := do_ σ_pre (3, 2, app_op_t.Write 77 (add 1 empty))
    let σ     : concrete_st := merge σ_pre σ_a σ_b
    is_visible_value σ 99 ∧ is_visible_value σ 77 ∧ ¬ is_visible_value σ 42 := by
  refine ⟨⟨2, ?_, ?_⟩, ⟨3, ?_, ?_⟩, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · rintro ⟨ts, h_in_writes, h_not_removed⟩
    simp [do_, merge] at h_in_writes h_not_removed
    grind

/-! ## Negative companion (should-FAIL pin) -/

/-- The read is not constantly true: a never-written value is invisible
even in the merged two-writer state. -/
example :
    ¬ is_visible_value
        (merge init_st
          (do_ init_st (1, 0, app_op_t.Write 42 empty))
          (do_ init_st (2, 1, app_op_t.Write 99 empty))) 7 := by
  rintro ⟨ts, h_in_writes, h_not_removed⟩
  simp [do_, merge, init_st] at h_in_writes

end MVR_SPOT
