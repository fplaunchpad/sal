import Sal.Interfaces.Map_Extended
import Sal.CRDTs.RGA_with_tombstones.RGA_CRDT
import Sal.CRDTs.RGA_with_tombstones.RGA_ReadSide

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 400000

open Classical

/-! # RGA (CRDT) — SPOTs

CRDT-side mirror of `Sal/MRDTs/RGA/RGA_SPOT.lean`.
Same scenarios; the CRDT carries `(chars, afters, deleted)` map
components with `OpId = ℕ × ℕ` (rather than the MRDT's flat sets
keyed by `ℕ`), so the discharge of `after_of` facts unfolds to
`contains`/`mysel_a` rather than set-membership. -/

namespace RGA_CRDT_SPOT

/-- **SPOT 1 — Insert tombstone visibility.**

A single Insert at `(1, 0)` after sentinel `(0, 0)` makes the new
OpId visible. -/
example :
    let σ : concrete_st := do_ init_st (1, 0, app_op_t.Insert 65 (0, 0))
    visible σ (1, 0) = true := by
  simp [visible, do_, init_st, mysel_d]

/-- **SPOT 2 — causal order across an Insert chain.**

`σ₀` = Insert 'A' at (1,0) after sentinel (0,0); `σ` = `σ₀` then
Insert 'B' at (2,0) after (1,0). The afters_reach chain
B → A → sentinel yields `visible_lt σ (0,0) (2,0)`. -/
example :
    let σ₀ := do_ init_st (1, 0, app_op_t.Insert 65 (0, 0))
    let σ  := do_ σ₀     (2, 0, app_op_t.Insert 66 (1, 0))
    visible_lt σ (0, 0) (2, 0) := by
  set σ₀ := do_ init_st (1, 0, app_op_t.Insert 65 (0, 0)) with hσ₀
  set σ  := do_ σ₀     (2, 0, app_op_t.Insert 66 (1, 0)) with hσ
  have h_ba : after_of σ (2, 0) (1, 0) = true := by
    simp [hσ, after_of, do_]
  have h_a0 : after_of σ (1, 0) (0, 0) = true := by
    simp [hσ, hσ₀, after_of, do_, init_st]
  have h_reach : afters_reach σ (2, 0) (0, 0) :=
    afters_reach.step h_ba (afters_reach.step h_a0 (afters_reach.refl _))
  exact causal_order_visible_lt σ (2, 0) (0, 0) h_reach (by decide)

/-- **SPOT 3 — Remove tombstones its target.**

After Inserting 'A' at (1,0) and Removing it, (1,0) is no longer
visible. Direct application of `remove_tombstones_target`. -/
example :
    let σ : concrete_st :=
      do_ (do_ init_st (1, 0, app_op_t.Insert 65 (0, 0)))
          (2, 0, app_op_t.Remove (1, 0))
    visible σ (1, 0) = false :=
  remove_tombstones_target _ 2 0 (1, 0)

/-- **SPOT 4 — concurrent Inserts at same anchor get deterministic order.**

Two replicas concurrently insert 'A' at (1,0) and 'B' at (2,1)
after the sentinel. After CRDT merge of both branches,
`visible_lt σ (2,1) (1,0)` holds — `opid_max (2,1) (1,0) = (2,1)`
by lex max on (ts, rid), so (2,1) comes first. -/
example :
    let σ_a : concrete_st := do_ init_st (1, 0, app_op_t.Insert 65 (0, 0))
    let σ_b : concrete_st := do_ init_st (2, 1, app_op_t.Insert 66 (0, 0))
    let σ   : concrete_st := merge σ_a σ_b
    visible_lt σ (2, 1) (1, 0) := by
  set σ_a := do_ init_st (1, 0, app_op_t.Insert 65 (0, 0)) with hσa
  set σ_b := do_ init_st (2, 1, app_op_t.Insert 66 (0, 0)) with hσb
  set σ   := merge σ_a σ_b with hσ
  have h_2 : after_of σ (2, 1) (0, 0) = true := by
    simp [hσ, hσa, hσb, after_of, do_, merge, init_st]
  have h_1 : after_of σ (1, 0) (0, 0) = true := by
    simp [hσ, hσa, hσb, after_of, do_, merge, init_st]
  exact concurrent_insert_tiebreak_deterministic σ (0, 0) (2, 1) (1, 0)
    h_2 h_1 (by decide) (by decide)

end RGA_CRDT_SPOT
