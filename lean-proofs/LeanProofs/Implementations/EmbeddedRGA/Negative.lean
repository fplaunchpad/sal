import LeanProofs_no_spec_non_comm.Implementations.EmbeddedRGA.Definition
import LeanProofs_no_spec_non_comm.Interface.Laws

/-!
# Embedded RGA's empty `rc` does not satisfy RC-NON-COMM

The appendix sets `rc` empty and adds that the update and merge laws hold
"for the states and event prefixes arising in guarded executions".
`Commutes` in Section 4 quantifies over **every** state of `Sigma`, and over
every state an insertion and a deletion do not commute.

```
  e1 = (5, 0, ins 7 [] 0)      e2 = (6, 1, del 5)
```

An insertion takes the event's timestamp as the identity it allocates, so at
`sigma0 = []` this insertion allocates `5`, which is what the deletion
names. Insert then delete leaves `[]`; delete then insert leaves one record.
Distinct timestamps, distinct replicas, different operations, so neither
exemption in RC-NON-COMM applies, and the law demands an `rc` edge. The
empty `rc` has none.

The anchored FIFO queue and Embedded Peritext inherit this, being this row
with a different query and a different payload type.

## What this does and does not say

It refutes the appendix's own choice of `rc`, not every choice. An `rc`
ordering `del` before `ins` supplies the missing edge, and NO-RC-CHAIN
survives it because a `del` only starts an edge and an `ins` only ends one.
Whether that `rc` satisfies RC-NON-COMM in the other direction, which asks
every pair of insertions carrying different operations to commute at **every**
state, and whether it satisfies COND-COMM, is not settled here.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

def oIns : AppOp unaryScheme Nat := .ins 7 [] 0 ()
def oDel : AppOp unaryScheme Nat := .del 5

/-- The insertion, whose timestamp `5` is the identity it allocates. -/
def e1 : Op (AppOp unaryScheme Nat) := (5, 0, oIns)
/-- The deletion, which names identity `5`. -/
def e2 : Op (AppOp unaryScheme Nat) := (6, 1, oDel)

theorem step_ne : step (step ([] : St unaryScheme Nat) e1) e2 ≠ step (step ([] : St unaryScheme Nat) e2) e1 := by
  decide

theorem not_commutes : ¬ De.Commutes e1 e2 :=
  fun hc => step_ne (hc ([] : St unaryScheme Nat))

theorem ops_ne : e1.op ≠ e2.op := by
  show oIns ≠ oDel
  decide

theorem times_ne : De.time e1 ≠ De.time e2 := by
  show (5 : Nat) ≠ 6; decide

theorem reps_ne : De.rep e1 ≠ De.rep e2 := by
  show (0 : Nat) ≠ 1; decide

theorem no_rc_edge (a b : De.Event) : ¬ De.EventRcBefore a b := by
  simp [Impl.EventRcBefore, Impl.RcBefore, De, Dα, D, rcOf]

/-- **RC-NON-COMM fails for the appendix's empty `rc`.** -/
theorem no_laws : ¬ Laws De := by
  intro h
  rcases (h.rc_non_comm e1 e2 times_ne reps_ne).mp ⟨not_commutes, ops_ne⟩ with h' | h' <;>
    exact absurd h' (no_rc_edge _ _)

/-- So the row has no obligation bundle at that `rc`. -/
theorem no_obligations : ¬ Obligations De := fun h => no_laws h.laws

end LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA
