import LeanProofs1.Implementations.SidedRGA.Definition
import LeanProofs1.Interface.Laws

/-!
# Sided Embedded RGA's empty `rc` does not satisfy RC-NON-COMM

The same obstruction as the embedded row, and for the same reason: an
insertion takes the event's **timestamp** as the identity it allocates,
while `Commutes` quantifies over every state of `Sigma`, not the reachable
ones.

```
  e1 = (5, 0, ins 7 [] 0 right)      e2 = (6, 1, del 5)
```

At `sigma0 = []` the insertion allocates identity `5`, which the deletion
names. Insert then delete leaves `[]`; delete then insert leaves one record.
Distinct timestamps, distinct replicas, different operations, so RC-NON-COMM
demands an `rc` edge and the empty `rc` has none.

Sidedness is irrelevant to the failure: the witness uses one side, and the
left side gives the same thing. What fails is the identity's residence in
the timestamp, which both sides share.

## What this does and does not say

It refutes the appendix's own choice of `rc`, not every choice, exactly as
for the embedded row. An `rc` ordering `del` before `ins` supplies the
missing edge and survives NO-RC-CHAIN; whether it satisfies the other
direction of RC-NON-COMM, and COND-COMM, is not settled here.
-/

namespace LeanProofs1.Implementations.SidedRGA

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

def oIns : AppOp := .ins 7 [] 0 .right
def oDel : AppOp := .del 5

/-- The insertion, whose timestamp `5` is the identity it allocates. -/
def e1 : Op AppOp := (5, 0, oIns)
/-- The deletion, which names identity `5`. -/
def e2 : Op AppOp := (6, 1, oDel)

theorem step_ne : step (step ([] : St) e1) e2 ≠ step (step ([] : St) e2) e1 := by
  decide

theorem not_commutes : ¬ Ds.Commutes e1 e2 :=
  fun hc => step_ne (hc ([] : St))

theorem ops_ne : e1.op ≠ e2.op := by
  show oIns ≠ oDel
  decide

theorem times_ne : Ds.time e1 ≠ Ds.time e2 := by
  show (5 : Nat) ≠ 6; decide

theorem reps_ne : Ds.rep e1 ≠ Ds.rep e2 := by
  show (0 : Nat) ≠ 1; decide

theorem no_rc_edge (a b : Ds.Event) : ¬ Ds.EventRcBefore a b := by
  simp [Impl.EventRcBefore, Impl.RcBefore, Ds, D, rcOf]

/-- **RC-NON-COMM fails for the appendix's empty `rc`.** -/
theorem no_laws : ¬ Laws Ds := by
  intro h
  rcases (h.rc_non_comm e1 e2 times_ne reps_ne).mp ⟨not_commutes, ops_ne⟩ with h' | h' <;>
    exact absurd h' (no_rc_edge _ _)

/-- So the row has no obligation bundle at that `rc`. -/
theorem no_obligations : ¬ Obligations Ds := fun h => no_laws h.laws

/-- The left side gives the same witness. -/
theorem no_laws_left_side :
    ¬ Ds.Commutes (5, 0, .ins 7 [] 0 .left) (6, 1, oDel) := by
  intro hc
  have h := hc ([] : St)
  exact absurd h (by decide)

end LeanProofs1.Implementations.SidedRGA
