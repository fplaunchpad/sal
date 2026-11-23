import LeanProofs1.Implementations.MVRegister.Definition

/-!
# The multi-value register: the sequential specification

The independent specification of the row, following
`Sal/MRDTs/Instances/MVRContract.lean`. Its state is the live tagged writes,
its step is the same effect the implementation applies, and it admits a
history only when that history is **legal**: identities are distinct, and a
write supersedes only identities already allocated.

```
  Phi  = live tagged writes, beside the identities ever allocated
  phi0 = (empty, empty)
  (s, born) --(t,r,write v O)--> (clientStep s (t,r,write v O), born ∪ {t})
        when  t ∉ born  and  O ⊆ born
  (s, born) --read => V-->      (s, born)      when V = values of s
```

Overwrite targets must have been **born**, not still be live: two concurrent
writes may supersede the same earlier write, and both are legal.

## Why this is an event specification, not an operation one

`Soundness.Spec type` is `HistorySpec type.OType …`, over **operations**,
because Definition 4 hands the specification `projectedUpdates`, which keeps
only each event's label. This row cannot be specified that way: the identity
a write allocates is its **timestamp**, so the step below reads `e.time`, and
an operation does not carry it.

That is the same gap `Negative.lean` turns into a theorem. There it says no
`rc` can satisfy RC-NON-COMM; here it says the specification does not fit the
alphabet Definition 4 provides. One cause, two symptoms.
-/

namespace LeanProofs1.Implementations.MVRegister

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-- The specification's state: the live tagged writes, and every identity
ever allocated. -/
abbrev SpecState := St × Finset Nat

/-- `q(s)`: the surviving values, identities discarded. -/
def queryValues (s : St) : Finset Nat := s.image Prod.snd

/-- The specification as a machine over events. A write is admitted when its
own identity is fresh and every identity it supersedes was already
allocated. -/
def specMachine : HistoryMachine (Op AppOp) Unit (Finset Nat) where
  State := SpecState
  initial := (∅, ∅)
  transition s label t :=
    match label with
    | .update e =>
        e.time ∉ s.2 ∧ (∀ n ∈ overwrites e.op, n ∈ s.2)
          ∧ t = (step s.1 e, insert e.time s.2)
    | .query _ answer => t = s ∧ answer = queryValues s.1

/-- `Spec` as a language of histories. -/
def eventSpec : HistorySpec (Op AppOp) Unit (Finset Nat) := specMachine.toSpec

/-! ## What the specification does

Two concurrent writes survive together; a write that supersedes them both
collapses them. The companion facts below pin the tempting degenerate
readings: the register does **not** keep one value, and legality is **not**
vacuous. -/

/-- Replica 0 writes `10` at time 1, replica 1 writes `20` at time 2, neither
having seen the other. -/
def w1 : Op AppOp := (1, 0, .write 10 [])
def w2 : Op AppOp := (2, 1, .write 20 [])
/-- A later write that supersedes both. -/
def w3 : Op AppOp := (3, 0, .write 30 [1, 2])
/-- A write naming an identity nobody allocated. -/
def wBad : Op AppOp := (4, 0, .write 40 [9])

/-- **Both concurrent writes survive.** -/
theorem concurrent_keeps_both :
    queryValues (step (step ∅ w1) w2) = {10, 20} := by decide

/-- And it does **not** collapse to the later write alone. -/
theorem concurrent_not_single :
    queryValues (step (step ∅ w1) w2) ≠ {20} := by decide

/-- **A superseding write collapses them.** -/
theorem supersede_collapses :
    queryValues (step (step (step ∅ w1) w2) w3) = {30} := by decide

/-- And it does **not** leave the superseded values behind. -/
theorem supersede_not_all :
    queryValues (step (step (step ∅ w1) w2) w3) ≠ {10, 20, 30} := by decide

/-- **The order of two concurrent writes does not matter.** -/
theorem concurrent_order_free :
    queryValues (step (step ∅ w1) w2) = queryValues (step (step ∅ w2) w1) := by
  decide

/-- **Legality is not vacuous**: a write may not supersede an identity that
was never allocated. -/
theorem illegal_unborn :
    ¬ ∃ t, specMachine.transition (∅, ∅) (.update wBad) t := by
  rintro ⟨t, -, hborn, -⟩
  exact absurd (hborn 9 (by decide)) (by decide)

/-- **Freshness is not vacuous either**: an identity may not be reused. -/
theorem illegal_reuse :
    ¬ ∃ t, specMachine.transition (step ∅ w1, {1}) (.update w1) t := by
  rintro ⟨t, hfresh, -, -⟩
  exact hfresh (by decide)

/-- **Superseding a dead identity is legal.** Two concurrent writes may
supersede the same earlier write, so the target must be born, not live. -/
theorem legal_dead_target :
    ∃ t, specMachine.transition (step (step ∅ w1) w3, {1, 3})
      (.update (5, 1, .write 50 [1])) t :=
  ⟨_, by decide, by decide, rfl⟩

end LeanProofs1.Implementations.MVRegister
