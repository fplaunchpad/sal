import LeanProofs.Implementations.LWWRegister.SequentialSpec
import LeanProofs.Soundness.RALinearizability

/-!
# The LWW register: Definition 4

The two clauses combined, through the scoped adequacy theorem.
-/

namespace LeanProofs.Implementations.LWWRegister

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

/-- **RA-linearizability.** Every certified execution of the LWW register
satisfies Definition 4 against `Spec`. -/
theorem raLinearizable :
    Soundness.CertifiedRA D historySpec issuance :=
  Soundness.certifiedRA_scoped obligations historySound

end LeanProofs.Implementations.LWWRegister
