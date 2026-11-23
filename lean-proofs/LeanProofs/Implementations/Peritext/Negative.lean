import LeanProofs1.Implementations.Peritext.Definition
import LeanProofs1.Interface.Laws

/-!
# Embedded Peritext's empty `rc` does not satisfy RC-NON-COMM

The appendix sets `rc` empty for this row and adds that the update and merge
laws hold "for the states and event prefixes arising in guarded executions".
`Commutes` in Section 4 quantifies over **every** state of `Sigma`, not the
reachable ones, and over every state an insertion and a deletion do not
commute.

```
  e1 = (5, 0, ins (char 65) [] 0)      e2 = (6, 1, del 5)
```

At `sigma0 = []` the insertion allocates identity `5`, which is the identity
the deletion names. Insert then delete leaves `[]`; delete then insert
leaves one record. The two events have distinct timestamps, distinct
replicas and different operations, so neither exemption in RC-NON-COMM
applies, and the law then demands an `rc` edge between the two operations.
The empty `rc` has none.

This is the anchored FIFO queue's obstruction, and for the same reason: both
rows are Embedded RGA, whose insertion takes the event's timestamp as the
identity it allocates.

## What this does and does not say

It refutes the appendix's own choice of `rc`, not every choice. An `rc`
ordering `del` before `ins` supplies the missing edge, and NO-RC-CHAIN
survives it because a `del` only ever starts an edge and an `ins` only ever
ends one. Whether that `rc` satisfies RC-NON-COMM in the other direction,
which asks every pair of insertions carrying different operations to commute
at **every** state, and whether it satisfies COND-COMM, is not settled here.
-/

namespace LeanProofs1.Implementations.Peritext

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-! ## The witness -/

/-- The insertion label: the character `A`, anchored at the root. -/
def oIns : AppOp := .ins (.char 65) [] 0
/-- The deletion label. It names identity `5`. -/
def oDel : AppOp := .del 5

/-- The insertion, whose timestamp `5` is the identity it allocates. -/
def e1 : Op AppOp := (5, 0, oIns)
/-- The deletion, which names identity `5`. -/
def e2 : Op AppOp := (6, 1, oDel)

/-- At the initial state the two orders differ. -/
theorem step_ne : step (step ([] : St) e1) e2 ≠ step (step ([] : St) e2) e1 := by
  decide

theorem not_commutes : ¬ Dp.Commutes e1 e2 :=
  fun hc => step_ne (hc ([] : St))

theorem ops_ne : e1.op ≠ e2.op := by
  show oIns ≠ oDel
  decide

theorem times_ne : Dp.time e1 ≠ Dp.time e2 := by
  show (5 : Nat) ≠ 6; decide

theorem reps_ne : Dp.rep e1 ≠ Dp.rep e2 := by
  show (0 : Nat) ≠ 1; decide

theorem no_rc_edge (a b : Dp.Event) : ¬ Dp.EventRcBefore a b := by
  simp [Impl.EventRcBefore, Impl.RcBefore, Dp, D, rcOf]

/-! ## The result -/

/-- **RC-NON-COMM fails for the appendix's empty `rc`.** -/
theorem no_laws : ¬ Laws Dp := by
  intro h
  rcases (h.rc_non_comm e1 e2 times_ne reps_ne).mp ⟨not_commutes, ops_ne⟩ with h' | h' <;>
    exact absurd h' (no_rc_edge _ _)

/-- So the row has no obligation bundle at that `rc`, and does not reach
Definition 4 through `Soundness/`. -/
theorem no_obligations : ¬ Obligations Dp := fun h => no_laws h.laws

end LeanProofs1.Implementations.Peritext
