import LeanProofs.Implementations.FlatCounter.LinearExtension
import LeanProofs.Soundness.SequentialSpec

/-!
# The counter: clause 2

The independent sequential specification of Appendix `app:dt-counter`, the
abstraction function of Section 6, and the sequential premise. Nothing here
mentions `merge`.
-/

namespace LeanProofs.Implementations.FlatCounter

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1 LeanProofs.Interface

/-! ## RA-linearizability

`Spec` as a language of histories, which is the form Definition 4
uses. -/

/-- The specification as a deterministic machine. -/
def specMachine : DeterministicSpec type.OType type.QType type.ValType where
  State := Int
  initial := 0
  update z o := z + delta o
  query z _ := z

/-- `Spec` as a history language. -/
def historySpec : Soundness.Spec type := specMachine.toSpec

/-- The abstraction function of Section 6. The counter's state is already
the specification's state, so `alpha` is the identity and conditions (i),
(ii) and (iii) all hold definitionally. -/
def abstraction : Soundness.Abstraction D specMachine where
  alpha := id
  init := rfl
  step := fun _ _ => rfl
  observes := fun _ _ => rfl

/-- The sequential premise: `ops(pi) . (q => b)` is admitted by `Spec`, with
`b` the implementation's own answer. It follows from the three conditions. -/
theorem specSound : Soundness.SpecSound D historySpec :=
  abstraction.specSound

end LeanProofs.Implementations.FlatCounter
