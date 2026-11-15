import LeanProofs.Implementations.SetWinsMap.SequentialSpec
import LeanProofs.Soundness.RALinearizability

/-!
# The set-wins multimap: Definition 4

The two clauses combined.
-/

namespace LeanProofs.Implementations.SetWinsMap

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {K V : Type} [DecidableEq K] [DecidableEq V]

/-- **RA-linearizability.** Every certified execution of the set-wins
multimap satisfies Definition 4 against `Spec`, at its own nonempty `rc`. -/
theorem raLinearizable :
    Soundness.CertifiedRA (D K V) (historySpec K V) (issuance K V) :=
  Soundness.certifiedRA_direct directObligations specSound

#print axioms joinLemma
#print axioms raLinearizable

end LeanProofs.Implementations.SetWinsMap
