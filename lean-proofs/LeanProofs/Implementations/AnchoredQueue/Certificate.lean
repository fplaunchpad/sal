import LeanProofs_no_spec_non_comm.Implementations.AnchoredQueue.Negative
import LeanProofs_no_spec_non_comm.Implementations.EmbeddedRGA.Certificate

/-!
# The anchored FIFO queue: RA-linearizability

`Negative.lean` shows that no `rc` at all, empty or otherwise, satisfies
`Laws(D_type)` for this row: Section 4's `Commutes` quantifies over every
state of `Sigma`, and the row's prose says what the appendix says, that its
commutation is a fact about guarded states. So the row goes through the
invariant-scoped reading of
`Artifact/MRDTs/Paper1/InvariantOrder.lean`.

Everything that costs anything is in `EmbeddedRGA/` beside this folder's own
copy of it. This row's own contributions are its query, the head rather than
the payload list, and `canIssue_core`, which says its stricter discipline,
anchoring on the live tail and dequeuing the observed head, implies the
core's.

The folder is a standalone duplicate, so `EmbeddedRGA/` and the two files
beside this one are this folder's, not the main tree's.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.AnchoredQueue

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface
open LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA

/-- The state invariant: strictly descending in key order, every record
traceable to an enqueue the context observes. -/
abbrev Valid (C : Ctx Dq) : St → Prop := EmbeddedRGA.Valid C

/-- The sequential specification over the event alphabet, reading the
head. -/
abbrev historySpec : HistorySpec (Op AppOp) Unit (Option (Nat × Nat)) :=
  EmbeddedRGA.historySpec unaryScheme Nat headQuery

/-- **The invariant is closed along every certified execution.** -/
theorem closedInvariant {C : Configuration Dq.toMRDTSig}
    (reach : MintCertifiedReachV Dq.toMRDTSig
      (canonicalVirtualMergeBase Dq.toMRDTSig) (issuance rcOf) C) :
    InvariantOrder.Closed Dq.toMRDTSig C.replayContext (Valid C.replayContext) :=
  EmbeddedRGA.closedInvariant canIssue_core reach

/-- **Every stored version holds a causal replay of its event set.** -/
theorem representedVersions {C : Configuration Dq.toMRDTSig}
    (reach : MintCertifiedReachV Dq.toMRDTSig
      (canonicalVirtualMergeBase Dq.toMRDTSig) (issuance rcOf) C)
    {v : Version} {s : St} {E : Set (Op AppOp)} (hv : C.ver v = some (s, E)) :
    EmbeddedRGA.Replay C.replayContext E s :=
  EmbeddedRGA.representedVersions canIssue_core reach hv

/-- **RA-linearizability for the anchored FIFO queue**, at the
invariant-scoped reading. -/
theorem raLinearizable {C : Configuration Dq.toMRDTSig}
    (reach : MintCertifiedReachV Dq.toMRDTSig
      (canonicalVirtualMergeBase Dq.toMRDTSig) (issuance rcOf) C) :
    InvariantOrder.VersionsRA Dq.toMRDTSig (Valid C.replayContext)
      (commutingPolicy AppOp) historySpec C :=
  EmbeddedRGA.raLinearizable canIssue_core reach

/-! # Where this row stands in the folder

**Nothing here needed repair.** The criterion this row reaches,
`InvariantOrder.VersionsRA`, already carries the specification-visibility
clause as one of its four conjuncts, and `raLinearizable` above discharges
it from `respects ρ C.vis` and nothing else. That is the folder's own
argument, stated in `Soundness.lean`: every specification-visibility arrow
runs along `vis`, so a history respecting `vis` respects all of them,
whatever the specification thinks conflicts. SPEC-NON-COMM appears nowhere
in this row or in the `EmbeddedRGA/` core it rests on.

So the row is duplicated to record that it already belongs here, not to fix
it. Two facts below keep that from being vacuous.

* The clause has content: the specification does see a conflict, so there
  is an arrow to respect. `not_spec_commutes` exhibits one, at the same
  enqueue and dequeue that `Negative.lean` uses.
* The SPEC-NON-COMM route is closed for this row for a reason that precedes
  the law. `no_specObligations` says no specification at all supplies the
  bundle, because `Laws(D_type)` already fails at every `rc`. A row cannot
  drop a premise of a theorem it could never have called.

That is the difference between this row and the fifteen others. They reach
`SpecCertifiedRA` while leaving SPEC-NON-COMM out of the adequacy theorem;
this one reaches a different criterion whose specification clause never
asked for the law in the first place.
-/

/-- **The enqueue and the dequeue do not commute in the specification
either.** The specification's updates are the implementation's `step`, so
the two orders reach the states `Negative.lean` separates, and the head
query tells them apart: empty after the dequeue sees the enqueue, occupied
after it does not. -/
theorem not_spec_commutes : ¬ historySpec.Commutes e1 e2 := by
  intro h
  have lhs : historySpec.admits
      ([SeqLabel.update e1, .update e2] ++ [.query () none]) := by
    refine ((EmbeddedRGA.specMachine unaryScheme Nat headQuery).updates_query_iff
      [e1, e2] () none).mpr ?_
    show (none : Option (Nat × Nat)) = readHead (step (step ([] : St) e1) e2)
    decide
  have rhs := (h [] [SeqLabel.query () (none : Option (Nat × Nat))]).mp (by simpa using lhs)
  have key := ((EmbeddedRGA.specMachine unaryScheme Nat headQuery).updates_query_iff
    [e2, e1] () none).mp (by simpa using rhs)
  have key' : (none : Option (Nat × Nat)) = readHead (step (step ([] : St) e2) e1) := key
  exact absurd key' (by decide)

/-- **No specification gives this row the obligation bundle.** SPEC-NON-COMM
is the second field of `SpecObligations`, and the first already fails:
`no_laws` refutes `Laws(D_type)` at every `rc`. So the question of whether
this row can drop the fourth law does not arise, because the theorem that
takes it is out of reach. -/
theorem no_specObligations (S : Soundness.Spec type) : ¬ SpecObligations Dq S :=
  fun h => no_laws h.toObligationsOn.laws

#print axioms raLinearizable
#print axioms not_spec_commutes

end LeanProofs.NoSpecNonComm.Implementations.AnchoredQueue
