import LeanProofs1.Implementations.LWWRegister.VCs
import LeanProofs1.Soundness.RALinearizability

/-!
# The LWW register: Definition 4

RA-linearizability from the verification conditions, through the
execution-scoped premise.

This is the one row here that does **not** satisfy SPEC-NON-COMM. Every pair
of its events commutes in the implementation, since `do` keeps the write with
the greatest key whatever order the two arrive in, while in `Spec` two writes
of different values do not commute: the second overwrites the first. So the
implementation does erase a specification conflict, which is exactly what
SPEC-NON-COMM forbids, and `certifiedSpecRA` is unavailable.

What the row supplies instead is `historySound`, in which it chooses the
explaining history itself, namely the key-sorted one. That reaches Definition
4 but not the stronger criterion with specification visibility.
-/

namespace LeanProofs1.Implementations.LWWRegister

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-- **RA-linearizability.** Every certified execution of the LWW register
satisfies Definition 4 against `Spec`. -/
theorem raLinearizable :
    Soundness.CertifiedRA D historySpec issuance :=
  Soundness.certifiedRA_scoped obligations historySound

end LeanProofs1.Implementations.LWWRegister
