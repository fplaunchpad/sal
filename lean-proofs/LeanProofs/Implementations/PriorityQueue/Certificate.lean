import LeanProofs1.Implementations.PriorityQueue.VCs
import LeanProofs1.Soundness.RALinearizability

/-!
# The priority queue: Definition 4

RA-linearizability from the verification conditions, through the
execution-scoped premise.

Clause 1 is free: all three stores are grow-only, so every pair of events
commutes, `rc` is empty, `lo^C_E` has no edges and any enumeration of the
version's event set is a linear extension.

Clause 2 needs the scoped premise rather than `SpecSound`. The
specification is a finite partial priority map with no insertion
identities, no attachment store and no timestamp order, so it resolves two
additions of one element by the later one in the history, while the
implementation takes the greater insertion timestamp. An arbitrary replay
therefore does not explain the answers.

`historySound` chooses the replay that does. Every operation names one
element and the specification's transitions at different elements do not
interfere, so the history splits per element: each element's removals, then
its losing additions and the increments attached to older insertions, then
the winning addition, which overwrites all of that, then exactly the
increments attached to that same insertion. An element with no surviving
insertion puts its removals last and ends absent.
-/

namespace LeanProofs1.Implementations.PriorityQueue

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-- **RA-linearizability.** Every certified execution of the priority queue
satisfies Definition 4 against `Spec`. -/
theorem raLinearizable : Soundness.CertifiedRA D historySpec issuance :=
  Soundness.certifiedRA_scoped obligations historySound

end LeanProofs1.Implementations.PriorityQueue
