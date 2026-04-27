import Sal.Interfaces.Set_Extended
import Sal.CRDTs.OR_Set.OR_Set_CRDT
import Sal.CRDTs.OR_Set.OR_Set_ReadSide

set_option linter.mathlibStandardSet false

open Classical

/-! # OR-Set (CRDT) — SPOTs

Small Proof-Oriented Tests: concrete `do`/`merge` scenarios with
expected `lookup` outcomes, machine-checked. Two roles:

* **regression tests** — small instances of the operational semantics
  proved by reduction (cheap path, this file);
* **verified API documentation** — the same scenarios that the paper's
  §3.3.5 Spec 14/15 narrates, here pinned by proof.

Each SPOT is named after the headline read-side claim it exercises.
Reference: Shapiro et al. INRIA RR-7506 §3.3.5. -/

namespace OR_Set_CRDT_SPOT

/-- **SPOT 1 — Add makes element live.**

A single `Add 5` from the initial state makes `5` live by the
`(5, 1) ∈ adds, (5, 1) ∉ tombstones` witness. -/
example :
    let σ : concrete_st := do_ init_st (1, 0, app_op_t.Add 5)
    lookup σ 5 := by
  refine ⟨1, ?_, ?_⟩ <;> decide

/-- **SPOT 2 — concurrent Add wins over Rem (headline).**

Replica 0 issues `Add 5` at ts = 1; replica 1 concurrently issues
`Rem 5` at ts = 2. The Rem's local `adds` is empty (it never
observed the Add), so its tombstone-union is empty. After merge,
`(5, 1)` survives in `adds` and is not in `tombstones`. -/
example :
    let σ_a : concrete_st := do_ init_st (1, 0, app_op_t.Add 5)
    let σ_b : concrete_st := do_ init_st (2, 1, app_op_t.Rem 5)
    let σ  : concrete_st := merge σ_a σ_b
    lookup σ 5 := by
  refine ⟨1, ?_, ?_⟩ <;> decide

/-- **SPOT 3 — sequential Add then Rem extinguishes.**

A single replica issues `Add 5` at ts = 1, then `Rem 5` at ts = 2.
The `Rem` snapshots the just-added `(5, 1)` into tombstones, so
`5` is not live. -/
example :
    ¬ lookup
        (do_ (do_ init_st (1, 0, app_op_t.Add 5)) (2, 0, app_op_t.Rem 5))
        5 :=
  add_then_remove_extinguishes init_st 5 1 2 0 0

/-- **SPOT 4 — Add-wins survives even after concurrent Rem and merge.**

Same shape as SPOT 2, but with three concurrent ops: replica 0 adds
`5` at ts = 1, replicas 1 and 2 each issue `Rem 5` independently.
Since neither Rem observed the Add, the merged tombstones miss
`(5, 1)`, and the element remains live after the cascading merge. -/
example :
    let σ_a : concrete_st := do_ init_st (1, 0, app_op_t.Add 5)
    let σ_b : concrete_st := do_ init_st (2, 1, app_op_t.Rem 5)
    let σ_c : concrete_st := do_ init_st (3, 2, app_op_t.Rem 5)
    let σ  : concrete_st := merge (merge σ_a σ_b) σ_c
    lookup σ 5 := by
  refine ⟨1, ?_, ?_⟩ <;> decide

end OR_Set_CRDT_SPOT
