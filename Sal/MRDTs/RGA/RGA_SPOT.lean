import Sal.Interfaces.Set_Extended
import Sal.MRDTs.RGA.RGA_MRDT
import Sal.MRDTs.RGA.RGA_ReadSide

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 400000

open Classical

/-! # RGA (MRDT) — SPOTs

Small Proof-Oriented Tests for the canonical RGA semantic claims.
The state is `set (ts × (afterId × elem)) × set ts` — insert records
and tombstones — with sentinel root id `0`.

Each SPOT is named after the headline read-side claim it exercises.
Reference: Sal/MRDTs/.../Replicated_Growable_Array_ReadSide.lean. -/

namespace RGA_MRDT_SPOT

/-- **SPOT 1 — Insert makes id visible.**

Inserting `'A'` (codepoint 65) after the sentinel root (id = 0)
produces an insert record `(1, 0, 65)` and no tombstone, so `id = 1`
is visible. -/
example :
    let σ : concrete_st := do_ init_st (1, 0, app_op_t.Add_after 0 65)
    visible σ 1 := by
  refine ⟨⟨0, 65, ?_⟩, ?_⟩ <;> decide

/-- **SPOT 2 — causal order across an Insert chain.**

`σ₀` = Insert 'A' after root; `σ` = `σ₀` then Insert 'B' after 'A'.
The `afters_reach σ 2 0` chain (B→A→root) yields `visible_lt σ 0 2`
via the readside theorem. -/
example :
    let σ₀ : concrete_st := do_ init_st (1, 0, app_op_t.Add_after 0 65)
    let σ  : concrete_st := do_ σ₀ (2, 0, app_op_t.Add_after 1 66)
    visible_lt σ 0 2 := by
  set σ₀ := do_ init_st (1, 0, app_op_t.Add_after 0 65) with hσ₀
  set σ  := do_ σ₀ (2, 0, app_op_t.Add_after 1 66) with hσ
  have h_ba : after_of σ 2 1 := ⟨66, by simp [hσ, do_]⟩
  have h_a0 : after_of σ 1 0 := ⟨65, by simp [hσ, hσ₀, do_, init_st]⟩
  have h_reach : afters_reach σ 2 0 :=
    afters_reach.step h_ba (afters_reach.step h_a0 (afters_reach.refl _))
  exact causal_order_visible_lt σ 2 0 h_reach (by decide)

/-- **SPOT 3 — Remove tombstones its target.**

After Inserting 'A' at id = 1 and then Removing id = 1, id = 1 is
no longer visible. Direct application of `remove_tombstones_target`. -/
example :
    let σ : concrete_st :=
      do_ (do_ init_st (1, 0, app_op_t.Add_after 0 65))
          (2, 0, app_op_t.Remove 1)
    ¬ visible σ 1 :=
  remove_tombstones_target _ 2 0 1

/-- **SPOT 4 — concurrent Inserts at same anchor get deterministic order.**

Two replicas concurrently insert 'A' (ts = 1, rid = 0) and 'B'
(ts = 2, rid = 1) after the sentinel. After merging both insert
records, `visible_lt σ 2 1` holds — the higher ts comes first by
the sibling rule. -/
example :
    let σ_a : concrete_st := do_ init_st (1, 0, app_op_t.Add_after 0 65)
    let σ_b : concrete_st := do_ init_st (2, 1, app_op_t.Add_after 0 66)
    let σ   : concrete_st := merge init_st σ_a σ_b
    visible_lt σ 2 1 := by
  set σ_a := do_ init_st (1, 0, app_op_t.Add_after 0 65) with hσa
  set σ_b := do_ init_st (2, 1, app_op_t.Add_after 0 66) with hσb
  set σ   := merge init_st σ_a σ_b with hσ
  have h_2 : after_of σ 2 0 := ⟨66, by simp [hσ, hσa, hσb, do_, merge, init_st]⟩
  have h_1 : after_of σ 1 0 := ⟨65, by simp [hσ, hσa, hσb, do_, merge, init_st]⟩
  exact concurrent_insert_tiebreak_deterministic σ 0 2 1 h_2 h_1
    (by decide) (by decide)

end RGA_MRDT_SPOT
