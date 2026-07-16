import Sal.MRDTs.RGA_Rehoming.RGA_Tombstone_Free_ReadSide

open RGA_TF_Read

/-!
# Sequential-spec REFUTATION: the rehoming RGA is not the naive text buffer

The negative row of the sequential-spec campaign (#65). The campaign proves,
per RDT, that the fold of any single-replica history equals a straightforward
sequential program: tier 1 the eleven flat RDTs, tier 2 the mergeable queue =
a plain FIFO, tier 3 the embedded-chain RGA = the naive insert-at-index text
buffer, with the published tombstoned RGA inheriting the buffer spec as a
corollary. This file is the same statement shape for the **rehoming**
tombstone-free RGA — and its refutation.

The witness is KC's `s_bac` trace (`RGA_Tombstone_Free_SPOT.lean`), restated
in campaign form: build `[b, a, c]` on one replica, honestly (every op
`accurate` + `fresh_ts` at the state it executes against — the datatype's own
conditioning predicates), then delete `a`. The naive buffer keeps the
survivors' order, `[b, c]`; the rehoming `do_` re-homes `c` to the root where
the newest-first tiebreak leapfrogs it over `b`, reading `[c, b]`. So
`RehomingSeqSound` — the exact analogue of the theorems the embed RGA and the
tombstoned RGA *satisfy* — is FALSE, at the `do` level, with no merge
anywhere.

The separation table this completes (do-faithful vs merge-faithful are
independently failable):

| design | seq-spec (do) | merge (RA-lin) |
|---|---|---|
| embedded-chain RGA | sound (`embed_seq_sound`) | sound (`embed_ra_linearizable3`) |
| published tombstoned RGA | sound (`rga_seq_read_eq_buffer`) | sound |
| **rehoming RGA** | **REFUTED (this file)** | sound (`rga_ra_linearizable3_eq`) |
| Shesha | sound (`sequential_soundness`) | REFUTED (`Shesha_Rows_Refuted`) |

The rehoming row is why the design is demoted from the canonical seat: its
convergence certificate is real, but convergence is to its own fold
(`oq:linspec`), and its own fold is not a text buffer. Downstream, fused
Peritext inherits this at the render (`fused_delete_reformats_survivor`,
`Peritext/Peritext_Read.lean`).

SPOT shape (per convention: PASS and FAIL cases both):
`seq_agrees_before_delete` is the should-PASS half — on the delete-free
prefix of the same trace the two sides agree — so the refutation isolates
the delete as the exact point of departure, and the harness is shown to
have discriminating power.
-/

namespace RGA_TF_SeqSpec

/-! ## The naive sequential buffer (the campaign's spec program) -/

/-- Insert `t` immediately after element `a` in a buffer of ids. -/
def bufIns (t a : ℕ) : List ℕ → List ℕ
  | [] => [t]
  | x :: xs => if x = a then x :: t :: xs else x :: bufIns t a xs

/-- One step of the naive buffer at the rehoming RGA's op alphabet:
`Ins … a` places the new id right after `a` (at the head for the root
sentinel `a = 0`); `Del … x` removes `x`. Ids are the timestamps, as in
the datatype's own read. -/
def bufStep (buf : List ℕ) (o : op_t) : List ℕ :=
  match o with
  | (t, _, .Ins _ _ a) => if a = 0 then t :: buf else bufIns t a buf
  | (_, _, .Del _ x)   => buf.filter (· ≠ x)

/-- The naive buffer replay of a single-replica history. -/
def bufFold (ops : List op_t) : List ℕ := ops.foldl bufStep []

/-- The datatype's own single-replica replay. -/
def replay (ops : List op_t) : concrete_st := ops.foldl do_ (mk [])

/-! ## Single-replica honesty (the datatype's own conditioning) -/

/-- Every op is `accurate` (claimed path = true ancestor chain) and
`fresh_ts` at the state it executes against — the same predicates the
commutation layer conditions on, so the refutation below attacks no
strawman: the trace is as honest as the datatype's own theorems demand. -/
def StepsHonestFrom (s : concrete_st) : List op_t → Prop
  | [] => True
  | o :: rest => accurate o s ∧ fresh_ts o s ∧ StepsHonestFrom (do_ s o) rest

def StepsHonest (ops : List op_t) : Prop := StepsHonestFrom (mk []) ops

/-! ## The soundness statement (the shape tiers 1–3 prove) and its refutation -/

/-- **Sequential-spec soundness for the rehoming RGA** — the statement the
embed RGA and the published tombstoned RGA satisfy: on every honest
single-replica history, read with a complete descending candidate list, the
document IS the naive buffer. FALSE for this datatype
(`rehoming_seq_refuted`). -/
def RehomingSeqSound : Prop :=
  ∀ (ops : List op_t) (ids : List ℕ),
    StepsHonest ops →
    List.Pairwise (· > ·) ids →
    (∀ i, contains (replay ops) i = true → i ∈ ids) →
    document (replay ops) ids = bufFold ops

/-- KC's witness trace, campaign form: `a`(1) and `b`(2) root siblings,
`c`(3) under `a`, then delete `a`. -/
def opsW : List op_t :=
  [ (1, 0, .Ins 101 [] 0)
  , (2, 0, .Ins 102 [] 0)
  , (3, 0, .Ins 103 [] 1)
  , (9, 0, .Del [] 1) ]

/-- The witness is honest: every op accurate + fresh at its state. -/
theorem stepsHonest_opsW : StepsHonest opsW := by
  simp only [StepsHonest, StepsHonestFrom, opsW, accurate, fresh_ts,
    IsAncPath, opLeaf, opPath]
  native_decide

/-- **Should-PASS half**: on the delete-free prefix the rehoming RGA and the
naive buffer agree — both read `[b, a, c] = [2, 1, 3]`. The departure below
is therefore exactly the delete. -/
theorem seq_agrees_before_delete :
    document (replay (opsW.take 3)) [3, 2, 1] = bufFold (opsW.take 3) := by
  native_decide

/-- The naive buffer's verdict on the full trace: survivors in order, `[2, 3]`. -/
theorem bufFold_opsW : bufFold opsW = [2, 3] := by native_decide

/-- The datatype's verdict on the full trace: survivors swapped, `[3, 2]`. -/
theorem replay_opsW_read : document (replay opsW) [3, 2] = [3, 2] := by
  native_decide

/-- **Should-FAIL half — the refutation.** The rehoming RGA does not
implement the naive text buffer: the tier-shaped soundness statement is
false, on an honest four-op single-replica trace, at the delete. -/
theorem rehoming_seq_refuted : ¬ RehomingSeqSound := by
  intro h
  have hdesc : List.Pairwise (· > ·) ([3, 2] : List ℕ) := by decide
  have hcover : ∀ i, contains (replay opsW) i = true → i ∈ ([3, 2] : List ℕ) := by
    intro i hi
    have hi3 : i = 2 ∨ i = 3 := by
      simp only [replay, opsW, List.foldl_cons, List.foldl_nil] at hi
      simp [do_, mk, upd, contains, mem, union, _root_.singleton, init_st,
        const_on, restrict, const, intersection, empty, complement] at hi
      omega
    rcases hi3 with rfl | rfl <;> decide
  have key := h opsW [3, 2] stepsHonest_opsW hdesc hcover
  exact absurd key (by native_decide)

end RGA_TF_SeqSpec

section AxiomAudit
#print axioms RGA_TF_SeqSpec.rehoming_seq_refuted
#print axioms RGA_TF_SeqSpec.seq_agrees_before_delete
end AxiomAudit
