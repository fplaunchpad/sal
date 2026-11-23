import LeanProofs1.Implementations.SetWinsMap.VCs
import LeanProofs1.Soundness.RALinearizability

/-!
# The set-wins map: Definition 4

RA-linearizability from the verification conditions, and from nothing else.
`certifiedSpecRA` consumes `specObligations` and the sequential premise, so
all four laws of Section 4, all five conditions of Section 5 and the
sequential premise are load-bearing here. SPEC-NON-COMM travels inside the
bundle rather than beside it, because this row satisfies it.
-/

namespace LeanProofs1.Implementations.SetWinsMap

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

variable {K V : Type} [DecidableEq K] [DecidableEq V]

/-- **RA-linearizability.** Definition 4 of Section 4: every certified
execution of this row satisfies it against `Spec`.

The proof runs through `certifiedSpecRA`, which asks for SPEC-NON-COMM as
well, so all four laws of Section 4 and all five conditions of Section 5 are
load-bearing here. The witness it builds respects specification conflicts
too; Definition 4 does not ask for that, so the extra clause is dropped at
the last step. -/
theorem raLinearizable :
    Soundness.CertifiedRA (D K V) (historySpec K V) (issuance K V) :=
  Soundness.certifiedRA_of_spec
    (Soundness.certifiedSpecRA specObligations specSound)

end LeanProofs1.Implementations.SetWinsMap
