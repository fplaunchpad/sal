import LeanProofs1.Implementations.FugueMax.Definition
import LeanProofs1.Interface.Laws

/-!
# FugueMax's empty `rc` does not satisfy RC-NON-COMM

The appendix sets `rc` empty and adds that the update and merge laws hold
"on states arising in guarded executions". `Commutes` in Section 4 quantifies
over **every** state of `Sigma`, and over every state an insertion and a
deletion of the identity it allocates do not commute.

```
  e1 = (5, 0, ins 0 right ...)      e2 = (6, 1, del 5)
```

The identity an insertion allocates is the event's own timestamp, so at
`sigma0 = ([], empty)` this insertion allocates `5`, which is what the
deletion names. Insert then delete leaves the live list empty; delete then
insert leaves one record. Distinct timestamps, distinct replicas, different
operations, so neither exemption in RC-NON-COMM applies and the law demands
an `rc` edge. The empty `rc` has none.

Immutable births do not repair this. The birth store is grow-only and both
orders end with the same birth in it, so the two components have to be
compared together. They differ in the **live list**, which is the component
the query reads.

## What this does and does not say

It refutes the appendix's own choice of `rc`, not every choice, exactly as
in Embedded RGA. An `rc` ordering `del` before `ins` supplies the missing
edge. Whether that `rc` satisfies RC-NON-COMM in the other direction and
COND-COMM is not settled here.
-/

namespace LeanProofs1.Implementations.FugueMax

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-- An insertion as a right child of the root, with an empty chain. -/
def oIns : AppOp := ⟨5, .ins 0 .right, 0, none, []⟩
/-- A deletion naming identity `5`. -/
def oDel : AppOp := ⟨6, .del 5, 0, none, []⟩

/-- The insertion, whose timestamp `5` is the identity it allocates. -/
def e1 : Event := (5, 0, oIns)
/-- The deletion, which names identity `5`. -/
def e2 : Event := (6, 1, oDel)

/-- The two orders differ in the live list: insert then delete leaves it
empty, delete then insert leaves the record `(5, 5, [])`. -/
theorem step_ne : (step (step (([], ∅) : St) e1) e2).1 ≠ (step (step (([], ∅) : St) e2) e1).1 := by
  decide

theorem not_commutes : ¬ Df.Commutes e1 e2 := fun hc =>
  step_ne (congrArg Prod.fst (hc (([], ∅) : St)))

theorem ops_ne : e1.op ≠ e2.op := by
  show oIns ≠ oDel
  decide

theorem times_ne : Df.time e1 ≠ Df.time e2 := by
  show (5 : Nat) ≠ 6; decide

theorem reps_ne : Df.rep e1 ≠ Df.rep e2 := by
  show (0 : Nat) ≠ 1; decide

theorem no_rc_edge (a b : Df.Event) : ¬ Df.EventRcBefore a b := by
  simp [Impl.EventRcBefore, Impl.RcBefore, Df, D, rcOf]

/-- **RC-NON-COMM fails for the appendix's empty `rc`.** -/
theorem no_laws : ¬ Laws Df := by
  intro h
  rcases (h.rc_non_comm e1 e2 times_ne reps_ne).mp ⟨not_commutes, ops_ne⟩ with h' | h' <;>
    exact absurd h' (no_rc_edge _ _)

/-- So the row has no obligation bundle at that `rc`. -/
theorem no_obligations : ¬ Obligations Df := fun h => no_laws h.laws

end LeanProofs1.Implementations.FugueMax
