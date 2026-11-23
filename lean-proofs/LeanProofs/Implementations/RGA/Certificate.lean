import LeanProofs1.Implementations.RGA.VCs
import LeanProofs1.Soundness.RALinearizability

/-!
# RGA: Definition 4

RA-linearizability from the verification conditions, through the
execution-scoped premise.

Clause 1 is free here: `rc` is empty and every pair of events commutes, so
`lo^C_E` has no edges and any enumeration of the version's event set is a
linear extension. The content is clause 2, and it needs the scoped premise
rather than `SpecSound`. The specification is the strict identified machine,
which admits an insertion only when its identity is fresh and positive and
its anchor is the root or live, so an arbitrary list of events is not
admitted and `SpecSound` is false.

What the row supplies instead is `historySound`: it chooses the explaining
history itself, putting the insertions first in increasing identity order
and the deletions after them. That is the order the implementation's own
query folds the edges in, which is why the two agree.
-/

namespace LeanProofs1.Implementations.RGA

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-- **RA-linearizability.** Every certified execution of the RGA satisfies
Definition 4 against `Spec`. -/
theorem raLinearizable : Soundness.CertifiedRA D historySpec issuance :=
  Soundness.certifiedRA_scoped obligations historySound

end LeanProofs1.Implementations.RGA
