import LeanProofs1.Implementations.SidedPeritext.Definition
import LeanProofs1.Interface.Laws

/-!
# Sided Peritext's empty `rc` does not satisfy RC-NON-COMM

The appendix sets `rc` empty and adds that the update and merge laws hold
"for the states and event prefixes arising in guarded executions".
`Commutes` in Section 4 quantifies over **every** state of `Sigma`.

For this row the qualification costs more than it does for the rest of the
family, and the reason is worth stating separately.

## Two insertions already fail

The other embedded rows are refuted by an insertion against a deletion of
the identity it allocates. That witness is available here too, but it uses
`Text(Del)`, which `issuance` forbids outright: logical deletion goes to the
store `D`, and native text deletion "exists as a total raw effect but cannot
be issued". A refutation resting on it would be answered by saying no
replica can perform it.

So the witness here uses **two insertions**:

```
  e1 = (5, 0, Text (Ins 5 7 [] 0 right))      coordinate h_R 5
  e2 = (6, 1, Text (Ins 6 8 [] 1 right))      coordinate h_R 5
```

An insertion's coordinate is `p ++ h_s (t - a)`, so it depends on the
**difference** between the clock and the anchor, not on the clock. Two
insertions with different timestamps and different anchors can therefore
land on the same coordinate, and then the descending insertion `J` keeps
whichever arrived first. The two orders give the records in opposite order,
so the operations do not commute.

Distinct timestamps, distinct replicas, different operations, so neither
exemption in RC-NON-COMM applies and the law demands an `rc` edge between
two insertions. The empty `rc` has none.

## What this does and does not say

It refutes the appendix's own choice of `rc`, not every choice. But note
what an `rc` would have to do here: order one *insertion* before another,
by an operation-level relation that cannot see which coordinate each lands
on until the clocks are fixed.

The pair is **not** special to this row. A coordinate is `p ++ h_s (t - a)`
in every embedded row, so the same two insertions refute Embedded RGA, Sided
Embedded RGA, the anchored FIFO queue and Embedded Peritext as well; only
the payload type differs. An `rc` ordering `del` before `ins` therefore does
not repair any of them, which is what the inherited witness below might
otherwise suggest. Whatever `rc` those rows need has to order one insertion
against another.

The second witness below is the family's inherited one, recorded so that the
comparison with the other four rows is explicit.
-/

namespace LeanProofs1.Implementations.SidedPeritext

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-! ## The two insertions -/

/-- An insertion at the root, stamped `5`: coordinate `h_R 5`. -/
def oIns1 : AppOp := .text (.ins 5 7 [] 0 .right)
/-- An insertion anchored at `1`, stamped `6`: coordinate `h_R 5` as well. -/
def oIns2 : AppOp := .text (.ins 6 8 [] 1 .right)

def e1 : Event := (5, 0, oIns1)
def e2 : Event := (6, 1, oIns2)

/-- The two insertions land on the same coordinate. -/
theorem coords_collide :
    ([] ++ SidedRGA.hSide .right (5 - 0)) = ([] ++ SidedRGA.hSide .right (6 - 1)) := by
  decide

/-- So the descending insertion keeps them in arrival order, and the two
orders differ. -/
theorem step_ne :
    step (step (([], ∅, ∅) : St) e1) e2 ≠ step (step (([], ∅, ∅) : St) e2) e1 := by
  decide

theorem not_commutes : ¬ Dsp.Commutes e1 e2 :=
  fun hc => step_ne (hc (([], ∅, ∅) : St))

theorem ops_ne : e1.op ≠ e2.op := by
  show oIns1 ≠ oIns2
  decide

theorem times_ne : Dsp.time e1 ≠ Dsp.time e2 := by
  show (5 : Nat) ≠ 6; decide

theorem reps_ne : Dsp.rep e1 ≠ Dsp.rep e2 := by
  show (0 : Nat) ≠ 1; decide

theorem no_rc_edge (a b : Dsp.Event) : ¬ Dsp.EventRcBefore a b := by
  simp [Impl.EventRcBefore, Impl.RcBefore, Dsp, D, rcOf]

/-- **RC-NON-COMM fails for the appendix's empty `rc`**, on a pair of
insertions. -/
theorem no_laws : ¬ Laws Dsp := by
  intro h
  rcases (h.rc_non_comm e1 e2 times_ne reps_ne).mp ⟨not_commutes, ops_ne⟩ with h' | h' <;>
    exact absurd h' (no_rc_edge _ _)

/-- So the row has no obligation bundle at that `rc`. -/
theorem no_obligations : ¬ Obligations Dsp := fun h => no_laws h.laws

/-! ## The family's inherited witness

An insertion against a native text deletion of the identity it allocates.
`issuance` forbids `Text(Del)`, so this pair cannot arise in any certified
execution; it is recorded only to place this row beside Embedded RGA, Sided
RGA and Embedded Peritext, which are refuted by exactly this pair. -/

/-- A native text deletion, which `issuance` never admits. -/
def oDel : AppOp := .text (.del 5)

theorem inherited_step_ne :
    step (step (([], ∅, ∅) : St) e1) (6, 1, oDel)
      ≠ step (step (([], ∅, ∅) : St) (6, 1, oDel)) e1 := by
  decide

theorem inherited_not_commutes : ¬ Dsp.Commutes e1 ((6, 1, oDel) : Event) :=
  fun hc => inherited_step_ne (hc (([], ∅, ∅) : St))

/-! ## The stores are not the problem

Logical deletion and mark recording are set insertions into components that
`do` never reads, so they commute with everything, including with each other
and with text. The failure above is entirely in the insertion shadow. -/

/-- A logical deletion commutes with the insertion whose identity it
names. -/
theorem recordDeletion_commutes :
    Dsp.Commutes e1 ((6, 1, AppOp.recordDeletion 5) : Event) := by
  intro s
  rcases s with ⟨S, Dl, F⟩
  rfl

/-- Two mark records commute. -/
theorem recordMark_commutes (m n : Mark) :
    Dsp.Commutes ((5, 0, AppOp.recordMark m) : Event)
      ((6, 1, AppOp.recordMark n) : Event) := by
  intro s
  rcases s with ⟨S, Dl, F⟩
  show (S, Dl, insert n (insert m F)) = (S, Dl, insert m (insert n F))
  rw [Finset.insert_comm]

end LeanProofs1.Implementations.SidedPeritext
