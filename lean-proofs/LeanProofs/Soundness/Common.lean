import LeanProofs.Metatheory.Adequacy
import Artifact.MRDTs.Paper1.RALinearizability
import Artifact.MRDTs.Paper1.EventBridge
import LeanProofs.Interface.SpecLaws

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

/-! ## The join lemma at a configuration

Section 5 indexes every obligation by a configuration. `can_C(E)` is the
canonical state of `E` at `C`, and the join lemma reads "let `C` be a
configuration, then for all weakly closed `E1, E2` of `E_C`". The two
definitions below are that statement, carrying `C` as the paper does, and
they are what the adequacy theorems of `RALinearizability.lean` consume.

A configuration contributes its visibility relation and the events it
observes, and nothing else. That pair is `C.replayContext`, which
`Interface.Ctx` names and which every row's own conditions are stated at.
Weak closure is the hypothesis `JoinAt` already carries, `vis`-predecessors
that do not commute, and is the paper's `WeakClosed_C(E)`. -/

/-- **Lemma (Join)** at one configuration. For weakly closed `E1, E2` of
`E_C`, merging `can_C(E1 n E2)`, `can_C(E1)` and `can_C(E2)` gives
`can_C(E1 u E2)`. -/
abbrev JoinAtConfig (D : Impl type) (C : Configuration D.toMRDTSig) : Prop :=
  @JoinAt D.toMRDTSig (Interface.rcOrder D) C.replayContext

/-- **Lemma (Join)**: the obligation at every configuration. -/
abbrev JoinConfig (D : Impl type) : Prop :=
  ∀ C : Configuration D.toMRDTSig, JoinAtConfig D C

/-- The vendored all-context join supplies the paper's statement. The
converse is not available. -/
theorem joinConfig_of_join (h : @Join D.toMRDTSig (Interface.rcOrder D)) :
    JoinConfig D :=
  fun C => h C.replayContext

end LeanProofs.Soundness
