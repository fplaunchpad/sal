import LeanProofs.Metatheory.Adequacy
import Artifact.MRDTs.Paper1.RALinearizability
import Artifact.MRDTs.Paper1.EventBridge

/-!
# Definition 4, and the vocabulary its two clauses share

Definition (RA-linearizability) of Section 4 reads: for every stored version
`v` with `S(v) = (s, E)` and every query `q`, with `b` the implementation's
answer, there exists a `pi` such that

1. `pi` is a linear extension of `(E, lo^C_E)`, and
2. `ops(pi) . (q => b)` is in `Spec`.

The two clauses are proved in separate files and combined in
`Soundness/RALinearizability.lean`:

```
  Soundness/Common.lean            this file: the definition and the shared names
      |                      |
      v                      v
  LinearExtension.lean    SequentialSpec.lean      clause 1        clause 2
      |                      |
      +----------+-----------+
                 v
       RALinearizability.lean       the adequacy theorems, which need both
```

Clause 1 is the convergence side and rests on the join lemma of
`Metatheory/Adequacy.lean`. Clause 2 is the conformance side and never
mentions `merge`. As the paper says, the canonical join laws alone do not
establish conformance, which is why the two never meet before the last file.
-/

namespace LeanProofs.Soundness

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {type : MRDTType} {D : Impl type}

/-- `rc` as an operation policy. Definition 4 is indexed by it, so every
statement in these files is relative to the implementation's own `rc`. -/
abbrev policy (D : Impl type) : OperationPolicy type.OType :=
  Interface.policy D

/-- `Spec` as a language of histories, which is the form Definition 4 uses. -/
abbrev Spec (type : MRDTType) : Type :=
  HistorySpec type.OType type.QType type.ValType

/-- Definition 4 at every configuration reachable by a certified execution,
ordinary or with recursively computed merge bases. -/
abbrev CertifiedRA (D : Impl type) (S : Spec type)
    (I : Issuance D.toMRDTSig) : Prop :=
  CertifiedRAV D.toMRDTSig (policy D) S I

end LeanProofs.Soundness
