import LeanProofs_no_spec_non_comm.Implementations.RGA.VCs

/-!
# RGA: the specification-visibility criterion

RA-linearizability **with specification visibility**, from the premise in
`VCs.lean` and from nothing else. SPEC-NON-COMM appears nowhere, and the row
refutes it: every pair of events commutes in the implementation, while in
`Spec` two insertions after the root do not, one order reading `[2, 1]` and
the other `[1, 2]`.

This is the first ported row where the clause is not free. The chosen
history puts every deletion after every insertion, so it does invert `vis`
arrows. `VCs.lean` shows the inverted arrows are not specification
conflicts.

The folder is a standalone duplicate of the row, so `Definition.lean` and
`VCs.lean` beside this file are the row's own, not the main tree's.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.RGA

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

end LeanProofs.NoSpecNonComm.Implementations.RGA
