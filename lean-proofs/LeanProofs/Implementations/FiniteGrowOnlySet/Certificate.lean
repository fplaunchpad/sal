import LeanProofs_no_spec_non_comm.Implementations.FiniteGrowOnlySet.VCs

/-!
# The finite grow-only set: the specification-visibility criterion

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

namespace LeanProofs.NoSpecNonComm.Implementations.FiniteGrowOnlySet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

/-- **RA-linearizability with specification visibility.** -/
theorem specRaLinearizable {A : Type} [DecidableEq A] :
    Soundness.SpecCertifiedRA (D A) (historySpec A) (issuance A) :=
  Soundness.certifiedSpecRA_any obligations.toObligationsOn joint_acyclic anyOrderSound

/-- Definition 4 follows, as it does for every row on the specification
route. -/
theorem raLinearizable {A : Type} [DecidableEq A] :
    Soundness.CertifiedRA (D A) (historySpec A) (issuance A) :=
  Soundness.certifiedRA_of_spec specRaLinearizable

#print axioms specRaLinearizable

end LeanProofs.NoSpecNonComm.Implementations.FiniteGrowOnlySet
