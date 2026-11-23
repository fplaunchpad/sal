import LeanProofs1.Implementations.TreeMove.VCs
import LeanProofs1.Soundness.RALinearizability

/-!
# Tree move: Definition 4

RA-linearizability from the verification conditions, through the
execution-scoped premise.

Clause 1 is free once `all_commute` is proved: `rc` is empty and every pair
of events commutes on the coherent state space, so `lo^C_E` has no edges and
any enumeration of the version's event set is a linear extension. What makes
`all_commute` true here, where the embedded RGA family's version of it is
false, is that `Sigma` is the coherent state space, so the appendix's "on the
coherent state space" is a restriction of the quantifier and not a caveat
outside it.

The content is clause 2, and it needs the scoped premise rather than
`SpecSound`. The specification admits only key-sorted histories, so an
arbitrary list of events is not admitted and `SpecSound` is false. What the
row supplies instead is `historySound`: it chooses the key-ascending
enumeration, which is the order the implementation's undo/insert/redo fold
replays in. The two agree because of `candidate_safe_iff`, which says the
implementation's ancestor test and the specification's acyclicity test are
complements on an acyclic tree, and acyclicity is preserved from `T0`.
-/

namespace LeanProofs1.Implementations.TreeMove

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-- **RA-linearizability.** Every certified execution of the Tree move row
satisfies Definition 4 against `Spec`. -/
theorem raLinearizable : Soundness.CertifiedRA D historySpec issuance :=
  Soundness.certifiedRA_scoped obligations historySound

end LeanProofs1.Implementations.TreeMove
