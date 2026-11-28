import LeanProofs_no_spec_non_comm.Implementations.PriorityQueue.VCs

/-!
# The add-wins priority queue: the specification-visibility criterion

RA-linearizability **with specification visibility**, from the premise in
`VCs.lean` and from nothing else. SPEC-NON-COMM appears nowhere, and the row
refutes it: every pair of events commutes in the implementation, all three
stores being grow-only, while in `Spec` two additions of one element do not,
because the specification overwrites. `not_spec_non_comm` is that
refutation.

This row needed a second order, not a copy of the one Definition 4 uses.
`rank` sorts a deletion before the addition it disabled, and a deletion
disables an addition only by observing it, so that order inverts a `vis`
arrow which `Spec` separates. `srank` replaces it: chronological inside
each element, with the winning addition and its own increments moved to the
end. `cell_sarrange` reproves the answer at that order and
`sarrange_respects_spec` proves the new clause, the one from issuance
rather than from a law.

The folder is a standalone duplicate of the row, so `Definition.lean` and
`VCs.lean` beside this file are the row's own, not the main tree's.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.PriorityQueue

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

/-- **RA-linearizability with specification visibility.** -/
theorem specRaLinearizable : Soundness.SpecCertifiedRA D historySpec issuance :=
  Soundness.certifiedSpecRA_scoped_on obligations (fun _ _ => trivial)
    specChosenOrderSound

/-- Definition 4 follows, as it does for every row on the specification
route. -/
theorem raLinearizable : Soundness.CertifiedRA D historySpec issuance :=
  Soundness.certifiedRA_of_spec specRaLinearizable

#print axioms specRaLinearizable

end LeanProofs.NoSpecNonComm.Implementations.PriorityQueue
