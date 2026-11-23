import LeanProofs1.Implementations.AnchoredQueue.Definition
import LeanProofs1.Interface.Laws

/-!
# The anchored FIFO queue's empty `rc` does not satisfy RC-NON-COMM

The appendix sets `rc` empty for this row and adds that the update and merge
laws hold "for the states and event prefixes arising in guarded executions".
That qualification is load-bearing. `Commutes` in Section 4 quantifies over
**every** state of `Sigma`, not over the reachable ones, and over every state
an enqueue and a dequeue do not commute.

```
  e1 = (5, 0, ins 9 [] 0)      e2 = (6, 1, del 5)
```

At `sigma0 = []` the enqueue allocates identity `5`, which is the identity
the dequeue names. Enqueue then dequeue leaves `[]`; dequeue then enqueue
leaves one record. The two events have distinct timestamps, distinct
replicas and different operations, so neither exemption in RC-NON-COMM
applies, and the law then demands an `rc` edge between the two operations.
The empty `rc` has none.

## What this does and does not say

It refutes the appendix's own choice of `rc` for this row, not every choice.
An `rc` ordering `del` before `ins` would supply the missing edge, and
NO-RC-CHAIN would survive it because a `del` only ever starts an edge and an
`ins` only ever ends one. Whether that `rc` satisfies RC-NON-COMM in the
other direction, which asks every `ins`/`ins` pair carrying different
operations to commute at **every** state, and whether it satisfies
COND-COMM, is not settled here.

The lesson is the same one the row's own prose records: this datatype's
commutation is a fact about guarded states, and `Laws(D_type)` asks for a
fact about all of them.
-/

namespace LeanProofs1.Implementations.AnchoredQueue

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-! ## The witness -/

/-- The enqueue label. -/
def oIns : AppOp := .ins 9 [] 0
/-- The dequeue label. It names identity `5`. -/
def oDel : AppOp := .del 5

/-- The enqueue, whose timestamp `5` is the identity it allocates. -/
def e1 : Op AppOp := (5, 0, oIns)
/-- The dequeue, which names identity `5`. -/
def e2 : Op AppOp := (6, 1, oDel)

/-- At the initial state the two orders differ: performed first, the
enqueued record is dropped by the dequeue; performed second it survives. -/
theorem step_ne : step (step ([] : St) e1) e2 ≠ step (step ([] : St) e2) e1 := by
  decide

theorem not_commutes : ¬ Dq.Commutes e1 e2 :=
  fun hc => step_ne (hc ([] : St))

theorem ops_ne : e1.op ≠ e2.op := by
  show oIns ≠ oDel
  decide

theorem times_ne : Dq.time e1 ≠ Dq.time e2 := by
  show (5 : Nat) ≠ 6; decide

theorem reps_ne : Dq.rep e1 ≠ Dq.rep e2 := by
  show (0 : Nat) ≠ 1; decide

/-! ## `rc` is empty -/

theorem no_rc_edge (a b : Dq.Event) : ¬ Dq.EventRcBefore a b := by
  simp [Impl.EventRcBefore, Impl.RcBefore, Dq, D, rcOf]

/-! ## The result -/

/-- **RC-NON-COMM fails for the appendix's empty `rc`.** The enqueue and the
dequeue do not commute and carry different operations, so the law demands an
edge, and there is none. -/
theorem no_laws : ¬ Laws Dq := by
  intro h
  rcases (h.rc_non_comm e1 e2 times_ne reps_ne).mp ⟨not_commutes, ops_ne⟩ with h' | h' <;>
    exact absurd h' (no_rc_edge _ _)

/-- So the row has no obligation bundle at that `rc`, and does not reach
Definition 4 through `Soundness/`. -/
theorem no_obligations : ¬ Obligations Dq := fun h => no_laws h.laws

end LeanProofs1.Implementations.AnchoredQueue
