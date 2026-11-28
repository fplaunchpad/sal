import LeanProofs_no_spec_non_comm.Implementations.OptionalRegister.VCs

/-!
# The optional register: the specification-visibility criterion

RA-linearizability **with specification visibility**, from the premise in
`VCs.lean` and from nothing else. SPEC-NON-COMM appears nowhere, and the
main tree proves it false for this row.

An experiment beside the development. The main tree reaches Definition 4
here through `certifiedRA_scoped_of_join_strict`, which does not carry the
specification-visibility clause at all. This folder shows the clause is
reachable anyway, by choosing a history that respects `vis`.

The folder is a standalone duplicate of the row, so `Definition.lean` and
`VCs.lean` beside this file are the row's own, not the main tree's.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.OptionalRegister

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

/-- **RA-linearizability with specification visibility, and no
SPEC-NON-COMM.** The row refutes that law, and reaches the stronger
criterion anyway. -/
theorem specRaLinearizable : Soundness.SpecCertifiedRA D historySpec issuance :=
  Soundness.certifiedSpecRA_scoped_on obligations monotone_of_mintHonest
    specChosenOrderSound

/-- Definition 4 follows, as it does for every row on the specification
route. -/
theorem raLinearizable : Soundness.CertifiedRA D historySpec issuance :=
  Soundness.certifiedRA_of_spec specRaLinearizable

#print axioms specRaLinearizable

end LeanProofs.NoSpecNonComm.Implementations.OptionalRegister
