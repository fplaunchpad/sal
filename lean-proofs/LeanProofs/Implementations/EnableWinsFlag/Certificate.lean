import LeanProofs_no_spec_non_comm.Implementations.EnableWinsFlag.VCs

/-!
# The enable-wins flag: the specification-visibility criterion

RA-linearizability **with specification visibility**, from the obligations
and `AnyOrderSound`, the unrestricted sequential premise. SPEC-NON-COMM is
never consulted, although the row proves that law.

The main tree reaches Definition 4 here with
`certifiedRA_of_spec (certifiedSpecRA obligations anyOrderSound)`. This
folder reaches the stronger criterion with the same two inputs, minus the
fourth law inside the bundle, plus the one fact `VCs.lean` adds about
`joint`.

The folder is a standalone duplicate of the row, so `Definition.lean` and
`VCs.lean` beside this file are the row's own, not the main tree's.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.EnableWinsFlag

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

/-- **RA-linearizability with specification visibility.** -/
theorem specRaLinearizable :
    Soundness.SpecCertifiedRA D historySpec issuance :=
  Soundness.certifiedSpecRA_any obligations.toObligationsOn joint_acyclic anyOrderSound

/-- Definition 4 follows, as it does for every row on the specification
route. -/
theorem raLinearizable :
    Soundness.CertifiedRA D historySpec issuance :=
  Soundness.certifiedRA_of_spec specRaLinearizable

#print axioms specRaLinearizable

end LeanProofs.NoSpecNonComm.Implementations.EnableWinsFlag
