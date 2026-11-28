import LeanProofs_no_spec_non_comm.Implementations.MVRegisterHistorical.VCs

/-!
# The historical MV register: the specification-visibility criterion

RA-linearizability **with specification visibility**, from the premise in
`VCs.lean` and from nothing else. SPEC-NON-COMM appears nowhere, and the row
refutes it: every pair of events commutes in the implementation, while in
`Spec` a write that supersedes an identity does not commute with the write
that allocated it.

The folder is a standalone duplicate of the row, so `Definition.lean` and
`VCs.lean` beside this file are the row's own, not the main tree's.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.MVRegisterHistorical

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

end LeanProofs.NoSpecNonComm.Implementations.MVRegisterHistorical
