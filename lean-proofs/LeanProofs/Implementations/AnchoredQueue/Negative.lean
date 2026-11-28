import LeanProofs_no_spec_non_comm.Implementations.AnchoredQueue.Definition
import LeanProofs_no_spec_non_comm.Interface.Laws

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

## No choice of `rc` repairs it

Adding an `rc` edge between `del` and `ins` supplies the missing edge, and
on its own it survives NO-RC-CHAIN, because a `del` only ever starts such an
edge and an `ins` only ever ends one. It does not survive the rest of
RC-NON-COMM. `enc` is applied to `t - a` and `recKey` reads the coordinate
alone, so two enqueues with **different anchors** can produce the same
coordinate, and at such a state they do not commute either. That forces a
third edge, on a pair of enqueues.

Three operations pairwise demanding an edge orient a triangle, and every
orientation of a triangle contains a directed path of length two, which
NO-RC-CHAIN forbids. So `no_laws_any_rc` below refutes **every** `rc`, not
just the appendix's, and the row cannot reach Definition 4 through any
bundle whose `Laws` quantifies `Commutes` over all of `Sigma`. There is
therefore no `VCs.lean` for this row and cannot be one.

The lesson is the one the row's own prose records: this datatype's
commutation is a fact about guarded states, and `Laws(D_type)` asks for a
fact about all of them. What is left is the invariant-scoped reading, where
`Commutes` is asked only at the states an execution produces.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.AnchoredQueue

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface
open LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA

/-! ## The witness -/

/-- The enqueue label. -/
def oIns : AppOp := .ins 9 [] 0 ()
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
  simp [Impl.EventRcBefore, Impl.RcBefore, Dq, Dα, EmbeddedRGA.D, EmbeddedRGA.rcOf]

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

/-- A second enqueue label. Its anchor is `1`, not the root, so it is a
different operation from `oIns`. -/
def oIns2 : AppOp := .ins 8 [] 1 ()

/-! ## Two enqueues need not commute either

`enc` is applied to `t - a` and `recKey` reads the coordinate alone, so two
enqueues with **different anchors** can produce the same coordinate. At a
state where that happens the later enqueue lands on whichever side the
replay order put it, and the record list differs. -/

/-- `(1, 0, oIns)` allocates identity `1` with coordinate `enc 1`, and
`(2, 1, oIns2)` allocates identity `2` with coordinate `enc (2 - 1)`, which
is the same coordinate. -/
theorem coord_collision :
    step (step ([] : St) (1, 0, oIns)) (2, 1, oIns2)
      ≠ step (step ([] : St) (2, 1, oIns2)) (1, 0, oIns) := by
  decide

/-- The second enqueue does not commute with the dequeue either. -/
theorem ins2_del_ne :
    step (step ([] : St) (5, 0, oIns2)) (6, 1, oDel)
      ≠ step (step ([] : St) (6, 1, oDel)) (5, 0, oIns2) := by
  decide

theorem ops_ne_ins : oIns ≠ oIns2 := by decide
theorem ops_ne_ins2_del : oIns2 ≠ oDel := by decide

/-! ## No choice of `rc` satisfies the laws

The three operations `oIns`, `oIns2` and `oDel` pairwise fail to commute, so
RC-NON-COMM demands an `rc` edge on each of the three pairs. Three edges on
three operations orient a triangle, and every orientation of a triangle
contains a directed path of length two, which NO-RC-CHAIN forbids.

The deeper reason no `rc` can work: `rc` is a function of **operations**,
and the identity an enqueue allocates is the **event's timestamp**, which
the operation does not carry. So `rc` cannot tell the `del x` that names
this enqueue's identity from the `del x` that names another's, and must
relate the pair either always or never. Both are wrong. -/

/-- **The row's laws fail at every `rc`, not only at the appendix's empty
one.** `no_laws` above refutes the appendix's choice; this refutes the
quantifier, which is what the certificate needs in order to call the
invariant-scoped reading the only route. -/
theorem no_laws_any_rc : ¬ ∃ rc, Laws (D rc) := by
  rintro ⟨rc, h⟩
  have hA : (D rc).RcBefore oIns oDel ∨ (D rc).RcBefore oDel oIns :=
    (h.rc_non_comm (5, 0, oIns) (6, 1, oDel)
        (by show (5 : Nat) ≠ 6; decide) (by show (0 : Nat) ≠ 1; decide)).mp
      ⟨fun hc => step_ne (hc ([] : St)), by show oIns ≠ oDel; decide⟩
  have hB : (D rc).RcBefore oIns2 oDel ∨ (D rc).RcBefore oDel oIns2 :=
    (h.rc_non_comm (5, 0, oIns2) (6, 1, oDel)
        (by show (5 : Nat) ≠ 6; decide) (by show (0 : Nat) ≠ 1; decide)).mp
      ⟨fun hc => ins2_del_ne (hc ([] : St)), ops_ne_ins2_del⟩
  have hC : (D rc).RcBefore oIns oIns2 ∨ (D rc).RcBefore oIns2 oIns :=
    (h.rc_non_comm (1, 0, oIns) (2, 1, oIns2)
        (by show (1 : Nat) ≠ 2; decide) (by show (0 : Nat) ≠ 1; decide)).mp
      ⟨fun hc => coord_collision (hc ([] : St)), ops_ne_ins⟩
  -- The eight orientations, each with the chain it forces, written out.
  rcases hA with hA | hA <;> rcases hB with hB | hB <;> rcases hC with hC | hC
  -- oIns→oDel, oIns2→oDel, oIns→oIns2
  · exact h.no_rc_chain oIns oIns2 oDel ⟨hC, hB⟩
  -- oIns→oDel, oIns2→oDel, oIns2→oIns
  · exact h.no_rc_chain oIns2 oIns oDel ⟨hC, hA⟩
  -- oIns→oDel, oDel→oIns2, oIns→oIns2
  · exact h.no_rc_chain oIns oDel oIns2 ⟨hA, hB⟩
  -- oIns→oDel, oDel→oIns2, oIns2→oIns
  · exact h.no_rc_chain oIns oDel oIns2 ⟨hA, hB⟩
  -- oDel→oIns, oIns2→oDel, oIns→oIns2
  · exact h.no_rc_chain oDel oIns oIns2 ⟨hA, hC⟩
  -- oDel→oIns, oIns2→oDel, oIns2→oIns
  · exact h.no_rc_chain oIns2 oDel oIns ⟨hB, hA⟩
  -- oDel→oIns, oDel→oIns2, oIns→oIns2
  · exact h.no_rc_chain oDel oIns oIns2 ⟨hA, hC⟩
  -- oDel→oIns, oDel→oIns2, oIns2→oIns
  · exact h.no_rc_chain oDel oIns2 oIns ⟨hB, hC⟩

/-- **So no choice of `rc` gives this row an obligation bundle**, and there
is no `VCs.lean` to write: VC1 to VC5 are conditions on `lo^C_E`, which is
built from an `rc` that cannot exist. -/
theorem no_obligations_any_rc : ¬ ∃ rc, Obligations (D rc) := by
  rintro ⟨rc, h⟩
  exact no_laws_any_rc ⟨rc, h.laws⟩

#print axioms no_laws_any_rc

end LeanProofs.NoSpecNonComm.Implementations.AnchoredQueue
