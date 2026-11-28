import LeanProofs_no_spec_non_comm.Implementations.AnchoredQueue.Negative

/-!
# The anchored FIFO queue: the laws that do hold

`Laws(D_type)` has three fields and this row satisfies **two** of them. The
file is here to say which, so that "the row has no obligation bundle" is not
read as "nothing about the row's laws is provable".

```
  NO-RC-CHAIN   holds, vacuously: `rc` is empty, so there is no edge to
                start a chain with
  COND-COMM     holds, vacuously: its third hypothesis is an `rc` edge
  RC-NON-COMM   fails, and no choice of `rc` repairs it
```

`Negative.lean` beside this file is the third line: `no_laws` refutes the
appendix's empty `rc`, and `no_laws_any_rc` refutes the quantifier. Nothing
here contradicts that. `Laws` is a conjunction, and a conjunction can fail
on one conjunct.

The same split runs through the five conditions. VC1 asks `merge` to be
commutative at **every** triple of states, and `mergeDown` is a descending
merge with no tie-break and no deduplication, so two records carrying the
same coordinate come out in whichever order the arguments were given.
`not_vc1_merge_comm` below is that, and it is the same gap `Negative.lean`
measures: at a **valid** state distinct records have distinct keys, by
`key_ne_of_sourced`, so the collision cannot arise. That is why this row's
verification conditions live at `Valid` rather than at all of `Sigma`, in
`EmbeddedRGA/Invariant.lean` and `EmbeddedRGA/Commutation.lean`.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.AnchoredQueue

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface
open LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA

/-! ## `rc` has no edge, at operations -/

/-- `rc` is `Either` everywhere, so no pair of operations carries an edge.
`Negative.no_rc_edge` is the same fact at events. -/
theorem no_rc_op_edge (o₁ o₂ : type.OType) : ¬ Dq.RcBefore o₁ o₂ := by
  simp [Impl.RcBefore, Dq, Dα, EmbeddedRGA.D, EmbeddedRGA.rcOf]

/-! ## NO-RC-CHAIN -/

/-- **NO-RC-CHAIN holds.** A chain needs a first edge and there is none. -/
theorem no_rc_chain : ∀ o₁ o₂ o₃ : type.OType,
    ¬ (Dq.RcBefore o₁ o₂ ∧ Dq.RcBefore o₂ o₃) :=
  fun o₁ o₂ _ h => no_rc_op_edge o₁ o₂ h.1

/-! ## COND-COMM -/

/-- **COND-COMM holds.** The law is asked only of a pair carrying an `rc`
edge, which is its third hypothesis, so the empty `rc` discharges it
without a word about the queue. -/
theorem cond_comm : ∀ (sigma : Dq.Sigma) (e e' e'' : Dq.Event) (pi : List Dq.Event),
    Dq.time e ≠ Dq.time e' → Dq.rep e ≠ Dq.rep e' →
    Dq.EventRcBefore e e' → ¬ Dq.Commutes e' e'' →
    Dq.do_ (Dq.applyList (Dq.do_ (Dq.do_ sigma e') e) pi) e''
      = Dq.do_ (Dq.applyList (Dq.do_ (Dq.do_ sigma e) e') pi) e'' :=
  fun _ _ _ _ _ _ _ hrc _ => absurd hrc (no_rc_edge _ _)

/-! ## What is not here, and why

Two records with the same coordinate. `recKey` reads the coordinate alone,
so these have the same key, and `mergeDown` puts whichever one came second
in front. -/

/-- Identity `1`, value `7`, coordinate `[true, false]`. -/
def zA : Record := (1, 7, [true, false])
/-- Identity `2`, value `8`, the **same** coordinate. -/
def zB : Record := (2, 8, [true, false])

/-- **VC1 fails at unrestricted states.** `merge [] [zA] [zB]` is
`[zB, zA]` and `merge [] [zB] [zA]` is `[zA, zB]`. At a valid state the two
records could not share a key, which is the whole of the difference. -/
theorem not_vc1_merge_comm :
    ¬ ∀ l a b : Dq.Sigma, Dq.merge l a b = Dq.merge l b a := by
  intro h
  have key : mergeState [] [zA] [zB] = mergeState [] [zB] [zA] := h [] [zA] [zB]
  simp [EmbeddedRGA.mergeState, EmbeddedRGA.mergeDown, EmbeddedRGA.ids,
    EmbeddedRGA.recKey, zA, zB] at key
  split_ifs at key <;> simp at key

/-- **RC-NON-COMM fails**, which is `Negative.no_laws`, restated here so
that the three fields can be read off one file. -/
theorem not_rc_non_comm :
    ¬ ∀ e₁ e₂ : Dq.Event, Dq.time e₁ ≠ Dq.time e₂ → Dq.rep e₁ ≠ Dq.rep e₂ →
      ((¬ Dq.Commutes e₁ e₂ ∧ e₁.op ≠ e₂.op) ↔
        Dq.EventRcBefore e₁ e₂ ∨ Dq.EventRcBefore e₂ e₁) := by
  intro h
  rcases (h e1 e2 times_ne reps_ne).mp ⟨not_commutes, ops_ne⟩ with h' | h' <;>
    exact absurd h' (no_rc_edge _ _)

#print axioms no_rc_chain
#print axioms cond_comm
#print axioms not_vc1_merge_comm

end LeanProofs.NoSpecNonComm.Implementations.AnchoredQueue
