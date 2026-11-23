import LeanProofs1.Implementations.MVRegisterHistorical.VCs
import LeanProofs1.Soundness.RALinearizability

/-!
# The grow-only multi-value register: Definition 4

RA-linearizability from the verification conditions, through the
execution-scoped premise.

Clause 1 is free: both stores are grow-only, so every pair of events
commutes, `rc` is empty, `lo^C_E` has no edges and any enumeration of the
version's event set is a linear extension.

Clause 2 needs the scoped premise rather than `SpecSound`. The specification
keeps a **compact** live set, dropping the entries a write names, and admits
a history only when it is legal: identities distinct, and a write
superseding only identities already allocated. An arbitrary replay is not
legal, so `SpecSound` is false.

`historySound` chooses the replay in timestamp order. A configuration's
`causal_mono` says visibility increases the timestamp, so that order is
causal, and a write then names only identities already allocated. That is
exactly the specification's legality, and it is also what makes "dropped by
a later write" and "named by any write at all" the same condition, which is
why the compact fold agrees with the grow-only query.
-/

namespace LeanProofs1.Implementations.MVRegisterHistorical

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-- **RA-linearizability.** Every certified execution of the multi-value
register satisfies Definition 4 against `Spec`. -/
theorem raLinearizable : Soundness.CertifiedRA D historySpec issuance :=
  Soundness.certifiedRA_scoped obligations historySound

end LeanProofs1.Implementations.MVRegisterHistorical
