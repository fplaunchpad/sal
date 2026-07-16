import Sal.MRDTs.RGA_Rehoming.RGA_Tombstone_Free_ReadSide

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

/-! ## Delete CAN reorder survivors — a SEQUENTIAL-spec violation

This is not merely a read-side cosmetic cost of tombstone-freedom: it is a
violation of the datatype's **sequential** specification. A single `Del`,
applied at one replica with no concurrency whatsoever, reorders the elements
that survive it.

Root children `5` (elder) and `6` (younger); `5` has a child `8` (youngest).
The read is `[6, 5, 8]` (siblings newest-first: `6` before `5`; `8` nested
under `5`). Delete `5`: tombstone-free, so `5`'s child `8` **rehomes to the
root** and re-sorts among the root's children by id — and `8`, being younger
than `6`, jumps *ahead* of it. The new read is `[8, 6]`, whereas the old read
with `5` removed is `[6, 8]`: the survivor order changed.

**Why our RA-linearizability cannot detect this.** The certified reference
sequence in the framework IS the datatype's own `do_` fold: convergence is
proved by showing every merge equals that fold. So `merge = fold` — and here
the fold is *itself* the wrong sequence. Both sides of the convergence VC
compute the same reordered read and agree; the certificate is satisfied while
the single-replica semantics is broken. Catching this needs a spec independent
of the implementation's own fold (open question `oq:linspec`).

A tombstoned RGA keeps `5` as a dead position-holder, so `8`'s subtree never
migrates and the order is preserved; the physical splice cannot offer that.
This is exactly the general order-preservation claim, shown **false** below
(`tombstone_free_violates_delete_order`). The positive contrast — the
tombstoned RGA *satisfies* the same property — is `remove_preserves_visible_lt`
in `Sal/MRDTs/RGA_with_tombstones/RGA_ReadSide.lean`. -/

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

/-! ## KC's minimal reordering witness, built through `do_`

The reordering is exhibited on the exact operation sequence
`1 ← ins(a after 0); 2 ← ins(b after 0); 3 ← ins(c after a)`, constructed with
`do_` (not the `mk` oracle) so that it is faithful to a genuine single-replica
execution rather than a hand-assembled state. Elements are `a = 101`,
`b = 102`, `c = 103`; the identities are the timestamps `1, 2, 3`.

`a` (id 1) and `b` (id 2) are same-anchor siblings under the root, so the
newest-first read puts `b` before `a`; `c` (id 3) lives under `a`. The document
reads `[b, a, c] = [2, 1, 3]`. Deleting `a` *should* leave `[b, c]`; instead
`c`, rehomed to the root when `a` is spliced out, now out-ranks `b` under the
newest-first tiebreak (id 3 > id 2) and leapfrogs ahead — the read becomes
`[c, b] = [3, 2]`. -/

def s_bac : concrete_st :=
  do_ (do_ (do_ (mk []) (1, 0, .Ins 101 [] 0)) (2, 0, .Ins 102 [] 0)) (3, 0, .Ins 103 [] 1)

/-- Before the delete the document reads `b, a, c` (ids `2, 1, 3`). -/
theorem doc_bac : document s_bac [3, 2, 1] = [2, 1, 3] := by native_decide

/-- After deleting `a` (id `1`) the document reads `c, b` (ids `3, 2`): the two
survivors have swapped relative to their pre-delete order. -/
theorem del_a_document :
    document (do_ s_bac (9, 0, .Del [] 1)) [3, 2] = [3, 2] := by native_decide

/-- The single delete reorders the survivors: the post-delete read `[3, 2]`
(`c, b`) is *not* the pre-delete read with the deleted target filtered out,
`[2, 3]` (`b, c`). -/
theorem del_a_breaks_survivor_order :
    document (do_ s_bac (9, 0, .Del [] 1)) [3, 2]
      ≠ (document s_bac [3, 2, 1]).filter (· ≠ 1) := by native_decide

/-! ## The intent property and its refutation

`document` orders siblings newest-first, so the canonical read passes the
candidate ids in **descending** order. We encode that convention as
`List.Pairwise (· > ·) ids` (the codebase states such order constraints via
`List.Pairwise`; `List.Sorted` is deprecated in this Mathlib). The property is
additionally guarded by **completeness** — `ids` covers every live identity —
so that both the pre- and post-delete reads are the *full* documents; a
discrepancy is then a genuine reordering of survivors and never an artifact of a
short or mis-ordered candidate list. The refutation supplies KC's `s_bac` with
the complete, descending list `[3, 2, 1]`. -/

/-- Independent intent spec: a single `Del` only removes its target from the
read, leaving every survivor's relative order intact. RA-linearizability does
NOT entail this — the framework's certified reference sequence is the datatype's
own `do_` fold, so `merge = fold` computes the reordered read on both sides and
the convergence VC is satisfied while this property fails (`oq:linspec`).

The candidate list `ids` is required (i) **descending** (`List.Pairwise (· > ·)`,
the newest-first convention `document` implements) and (ii) **complete** (it
covers every live identity), so the equation compares two full documents in the
canonical order. -/
def DeleteOrderPreserving : Prop :=
  ∀ (s : concrete_st) (t r x : ℕ) (p ids : List ℕ),
    List.Pairwise (· > ·) ids → (∀ i, contains s i = true → i ∈ ids) →
    document (do_ s (t, r, .Del p x)) (ids.filter (· ≠ x))
      = (document s ids).filter (· ≠ x)

/-- **The tombstone-free RGA violates delete-order-preservation.** KC's witness
`s_bac`, read with the complete, strictly-descending candidate list `[3, 2, 1]`,
refutes the property: deleting `a` swaps the surviving `b` and `c`. Both guards
(descending, complete) are discharged on the concrete witness, so the failure is
a real reordering, not a read-argument artifact. Invisible to the framework's
RA-linearizability certificate (`oq:linspec`); the positive contrast is
`remove_preserves_visible_lt` for the tombstoned RGA. -/
theorem tombstone_free_violates_delete_order : ¬ DeleteOrderPreserving := by
  intro h
  have hdesc : List.Pairwise (· > ·) ([3, 2, 1] : List ℕ) := by decide
  have hcover : ∀ i, contains s_bac i = true → i ∈ ([3, 2, 1] : List ℕ) := by
    intro i hi
    have hi3 : i = 1 ∨ i = 2 ∨ i = 3 := by
      simp only [s_bac, do_, mk, List.foldl_nil] at hi
      simp [upd, contains, mem, union, _root_.singleton, init_st, const_on,
        restrict, const, intersection, empty, complement] at hi
      omega
    rcases hi3 with rfl | rfl | rfl <;> decide
  have key := h s_bac 9 0 1 [] [3, 2, 1] hdesc hcover
  exact absurd key (by native_decide)

end RGA_TF_SPOT

section AxiomAudit
#print axioms RGA_TF_SPOT.tombstone_free_violates_delete_order
#print axioms RGA_TF_SPOT.del_a_breaks_survivor_order
end AxiomAudit
