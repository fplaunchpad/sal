import Sal.Interfaces.Set_Extended
import Sal.CRDTs.Multi_Valued_Register.Multi_Valued_Register_CRDT
import Sal.CRDTs.Multi_Valued_Register.Multi_Valued_Register_ReadSide

set_option linter.mathlibStandardSet false

open Classical

/-! # Multi-Valued Register (CRDT, classical) — SPOTs

CRDT-side mirror of `Sal/MRDTs/Multi_Valued_Register/Multi_Valued_Register_SPOT.lean`.
Same scenarios, same theorem-application discharge style; the only
difference is the absence of an LCA argument in `merge`.

Reference: Shapiro et al. INRIA RR-7506 §3.2.2 Spec 14. -/

namespace MVR_CRDT_SPOT

/-- **SPOT 1 — concurrent writes both visible.**

Two replicas concurrently `Write` distinct values from the initial
state (each with empty prepare-time snapshot, since neither sees the
other). After CRDT merge (componentwise union), both values are
visible. -/
example :
    let σ_a : concrete_st := do_ init_st (1, 0, app_op_t.Write 42 empty)
    let σ_b : concrete_st := do_ init_st (2, 1, app_op_t.Write 99 empty)
    let σ  : concrete_st := merge σ_a σ_b
    is_visible_value σ 42 ∧ is_visible_value σ 99 := by
  refine ⟨⟨1, ?_, ?_⟩, ⟨2, ?_, ?_⟩⟩ <;> decide

/-- **SPOT 2 — sequential write supersedes prior.**

A single replica writes `42` (ts = 1), then writes `99` (ts = 2)
with prepare-time snapshot `{1}`. The prior `42` is no longer
visible because its only witness ts is now in `removed`. The
negative half applies `sequential_write_supersedes_value` —
discharging both `v₂ ≠ v₁` (`99 ≠ 42`) and the coverage premise
(σ₁'s only visible witness for `42` is `ts = 1`, which is in `O₂`). -/
example :
    let σ₁ : concrete_st := do_ init_st (1, 0, app_op_t.Write 42 empty)
    let σ₂ : concrete_st := do_ σ₁ (2, 0, app_op_t.Write 99 (add 1 empty))
    is_visible_value σ₂ 99 ∧ ¬ is_visible_value σ₂ 42 := by
  refine ⟨⟨2, ?_, ?_⟩, ?_⟩
  · decide
  · decide
  · -- Apply `sequential_write_supersedes_value` with σ = σ₁, ts₂ = 2,
    -- O₂ = {1}, v₁ = 42, v₂ = 99.
    apply sequential_write_supersedes_value
      (do_ init_st (1, 0, app_op_t.Write 42 empty)) 42 99 2 0 (add 1 empty)
      (by decide)
    -- Coverage: any visible witness (ts, 42) in σ₁ has ts = 1, which is in {1}.
    intro ts h_in _
    simp [do_, add, _root_.singleton, init_st, _root_.empty] at h_in
    -- h_in : ts = 1
    subst h_in
    decide

/-- **SPOT 3 — concurrent writes jointly retire a common ancestor.**

Replica 0 writes `42` (ts = 1). Replicas 1 and 2 each fork from this
state and concurrently write `99` (ts = 2) and `77` (ts = 3) with
prepare-time snapshot `{1}`. After CRDT merge of both branches
(componentwise union of `writes` and of `removed`), both `99` and
`77` are visible while `42` is not. -/
example :
    let σ_pre : concrete_st := do_ init_st (1, 0, app_op_t.Write 42 empty)
    let σ_a   : concrete_st := do_ σ_pre (2, 1, app_op_t.Write 99 (add 1 empty))
    let σ_b   : concrete_st := do_ σ_pre (3, 2, app_op_t.Write 77 (add 1 empty))
    let σ     : concrete_st := merge σ_a σ_b
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
        (merge (do_ init_st (1, 0, app_op_t.Write 42 empty))
               (do_ init_st (2, 1, app_op_t.Write 99 empty))) 7 := by
  rintro ⟨ts, h_in_writes, h_not_removed⟩
  simp [do_, merge, init_st] at h_in_writes

end MVR_CRDT_SPOT
