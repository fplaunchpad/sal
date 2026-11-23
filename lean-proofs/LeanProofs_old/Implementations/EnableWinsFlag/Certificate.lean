import LeanProofs.Implementations.EnableWinsFlag.SequentialSpec
import LeanProofs.Soundness.RALinearizability

/-!
# The flag core: Definition 4

The two clauses combined. Both flag rows instantiate this.
-/

namespace LeanProofs.Implementations.EnableWinsFlag

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

/-- **RA-linearizability.** Every certified execution of the flag satisfies
Definition 4 against `Spec`, at the implementation's own nonempty `rc`. -/
theorem raLinearizable :
    Soundness.CertifiedRA D historySpec
      issuance :=
  Soundness.certifiedRA obligations specSound

#print axioms joinLemma

end LeanProofs.Implementations.EnableWinsFlag
