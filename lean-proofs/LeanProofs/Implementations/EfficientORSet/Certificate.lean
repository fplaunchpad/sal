import LeanProofs_no_spec_non_comm.Implementations.EfficientORSet.VCs

/-!
# The efficient OR-set: the specification-visibility criterion

RA-linearizability **with specification visibility**, from the obligations
and `AnyOrderSound`, the unrestricted sequential premise. The main tree
reaches Definition 4 here with
`certifiedRA_of_spec (certifiedSpecRA obligations anyOrderSound)`; this
folder reaches the stronger criterion with the same two inputs, minus the
fourth law inside the bundle, plus the one fact `VCs.lean` adds about
`joint`.

Unlike the commuting rows and the flags, this row's `rc` is indexed, so its
`VCs.lean` does use the row's own SPEC-NON-COMM to get there. What is
dropped is the law as a **premise of the adequacy theorem**, not the law.

The folder is a standalone duplicate of the row, so `Definition.lean` and
`VCs.lean` beside this file are the row's own, not the main tree's.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.EfficientORSet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

/-- **RA-linearizability with specification visibility.** -/
theorem specRaLinearizable {α : Type} [DecidableEq α] :
    Soundness.SpecCertifiedRA (D α) (historySpec α) (issuance α) :=
  Soundness.certifiedSpecRA_any obligations.toObligationsOn joint_acyclic anyOrderSound

/-- Definition 4 follows, as it does for every row on the specification
route. -/
theorem raLinearizable {α : Type} [DecidableEq α] :
    Soundness.CertifiedRA (D α) (historySpec α) (issuance α) :=
  Soundness.certifiedRA_of_spec specRaLinearizable

#print axioms specRaLinearizable

end LeanProofs.NoSpecNonComm.Implementations.EfficientORSet
