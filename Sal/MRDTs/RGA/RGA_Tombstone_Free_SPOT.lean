import Sal.MRDTs.RGA.RGA_Tombstone_Free_ReadSide

open RGA_TF_Read

/-! # Tombstone-free RGA — SPOT (concrete-execution tests)

Small self-checking executions of the datatype and its read (`document` /
`readText` of `RGA_Tombstone_Free_ReadSide.lean`), tracking the figures of
`doc/why-the-path-matters.pdf`. Every fact is `native_decide` on a concrete
state; the general theorems are in the MRDT and ReadSide files.

Records are `(id, element, anchor)`; `mk` builds the state, `do_` applies an
operation `(ts, replica, app_op)`, `document s ids` is the depth-first read
(siblings by descending id = newest first). Read lists are printed by identity.
-/

namespace RGA_TF_SPOT

/-! ## Insert intent: a fresh insert lands immediately after its anchor

State: id `5` under the root. Insert `10` (element `90`) after `5` — `5` is a
root child so its ancestor path (root excluded) is `[]`. The read must place
`10` right after `5`. (Fig. "the fix", insert half.) -/

def s_ins : concrete_st := mk [(5, 83, 0)]

theorem ins_intent_document :
    document (do_ s_ins (10, 1, .Ins 90 [] 5)) [10, 5] = [5, 10] := by
  native_decide

theorem ins_intent_readText :
    readText (do_ s_ins (10, 1, .Ins 90 [] 5)) [10, 5] = [83, 90] := by
  native_decide

/-! ## Delete erases its target, preserving the order of survivors (leaf case)

Chain `0 ← 1`, with `2` and `3` both children of `1` (siblings). Deleting the
leaf `3` leaves `[1, 2]` — the old read with `3` filtered out, order intact.
(Fig. "delete rehoming", the easy case: a leaf has no subtree to migrate.) -/

def s_leaf : concrete_st := mk [(1, 65, 0), (2, 66, 1), (3, 67, 1)]

theorem leaf_document_before :
    document s_leaf [3, 2, 1] = [1, 3, 2] := by native_decide

theorem leaf_del_preserves_order :
    document (do_ s_leaf (9, 1, .Del [1] 3)) [2, 1]
      = (document s_leaf [3, 2, 1]).filter (· ≠ 3) := by native_decide

/-! ## Delete CAN reorder survivors — the read-side cost of tombstone-freedom

Root children `5` (elder) and `6` (younger); `5` has a child `8` (youngest).
The read is `[6, 5, 8]` (siblings newest-first: `6` before `5`; `8` nested
under `5`). Delete `5`: tombstone-free, so `5`'s child `8` **rehomes to the
root** and re-sorts among the root's children by id — and `8`, being younger
than `6`, jumps *ahead* of it. The new read is `[8, 6]`, whereas the old read
with `5` removed is `[6, 8]`: the survivor order changed.

A tombstoned RGA keeps `5` as a dead position-holder, so `8`'s subtree never
migrates and the order is preserved; the physical splice cannot offer that.
This is exactly the general order-preservation claim, shown **false**. -/

def s_reorder : concrete_st := mk [(5, 100, 0), (6, 101, 0), (8, 102, 5)]

theorem reorder_document_before :
    document s_reorder [8, 6, 5] = [6, 5, 8] := by native_decide

theorem del_can_reorder_survivors :
    document (do_ s_reorder (9, 1, .Del [] 5)) [8, 6]
      ≠ (document s_reorder [8, 6, 5]).filter (· ≠ 5) := by native_decide

/-! ## Merge reads (three-way, from the MRDT oracle scenarios)

The design note's concurrent-insert scenario: LCA `{1}`, branch A inserts `2`
under `1`, branch B inserts `3` under `1`. The merge keeps both; the read
interleaves the two concurrent children newest-first under `1`. -/

def s_lca : concrete_st := mk [(1, 65, 0)]
def s_A   : concrete_st := mk [(1, 65, 0), (2, 89, 1)]
def s_B   : concrete_st := mk [(1, 65, 0), (3, 90, 1)]

theorem merge_document :
    document (merge s_lca s_A s_B) [3, 2, 1] = [1, 3, 2] := by native_decide

theorem merge_convergent_read :
    document (merge s_lca s_A s_B) [3, 2, 1]
      = document (merge s_lca s_B s_A) [3, 2, 1] := by native_decide

end RGA_TF_SPOT
