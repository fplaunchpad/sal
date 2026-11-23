import LeanProofs1.Implementations.RemoveWinsSet.VCs
import LeanProofs1.Soundness.RALinearizability

/-!
# The remove-wins set: Definition 4

RA-linearizability from the verification conditions, and from nothing else.
This row carries an issuance guard, so its obligations hold only at the
contexts `Positive` admits and `certifiedSpecRA_on` is the form that
consumes them. `positive_of_mintHonest` is the step from a mint-honest
configuration to such a context.
-/

namespace LeanProofs1.Implementations.RemoveWinsSet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

variable {A : Type} [DecidableEq A] [Fintype A]

/-- **RA-linearizability.** Definition 4 of Section 4: every certified
execution of this row satisfies it against `Spec`.

The proof runs through `certifiedSpecRA`, which asks for SPEC-NON-COMM as
well, so all four laws of Section 4 and all five conditions of Section 5 are
load-bearing here. The witness it builds respects specification conflicts
too; Definition 4 does not ask for that, so the extra clause is dropped at
the last step. -/
theorem raLinearizable :
    Soundness.CertifiedRA (D A) (historySpec A) (issuance A) :=
  Soundness.certifiedRA_of_spec_on
    (Soundness.certifiedSpecRA_on specObligations positive_of_mintHonest specSound)

end LeanProofs1.Implementations.RemoveWinsSet
