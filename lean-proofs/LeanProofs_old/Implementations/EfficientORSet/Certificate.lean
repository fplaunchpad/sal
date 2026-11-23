import LeanProofs.Implementations.EfficientORSet.SequentialSpec
import LeanProofs.Soundness.RALinearizability

/-!
# The efficient OR-set: Definition 4

The two clauses combined, on the route of `Interface/PaperRoute.lean`.
`Laws(D_type)` holds only at concurrent events here, so the conditions are
read at `lo^C_E` itself. `Soundness.certifiedRA` is the same adequacy
theorem every other row uses.
-/

namespace LeanProofs.Implementations.EfficientORSet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {α : Type} [DecidableEq α]

/-- **RA-linearizability.** Every certified execution of the efficient
OR-set satisfies Definition 4 against `Spec`, at the implementation's own
nonempty `rc`. -/
theorem raLinearizable :
    Soundness.CertifiedRA (D α) (historySpec α) (issuance α) :=
  Soundness.certifiedRA obligations specSound

#print axioms raLinearizable

end LeanProofs.Implementations.EfficientORSet
