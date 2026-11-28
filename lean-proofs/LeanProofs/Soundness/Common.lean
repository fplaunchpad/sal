import LeanProofs_no_spec_non_comm.Metatheory.Adequacy
import Artifact.MRDTs.Paper1.RALinearizability
import Artifact.MRDTs.Paper1.EventBridge
import LeanProofs_no_spec_non_comm.Interface.SpecLaws

/-!
# Definition 4, and the vocabulary its two clauses share

Definition (RA-linearizability) of Section 4 reads: for every stored version
`v` with `S(v) = (s, E)` and every query `q`, with `b` the implementation's
answer, there exists a `pi` such that

1. `pi` is a linear extension of `(E, lo^C_E)`, and
2. `ops(pi) . (q => b)` is in `Spec`.

The two clauses are proved apart and combined in
`Soundness/RALinearizability.lean`:

```
  Soundness/Common.lean            this file: the definition and the shared names
      |                      |
      v                      v
  Metatheory/              SequentialSpec.lean
  Adequacy.lean                |                clause 1        clause 2
      |                        |
      +----------+-------------+
                 v
       RALinearizability.lean       the adequacy theorems, which need both
```

Clause 1 is the convergence side and rests on the join lemma of
`Metatheory/Adequacy.lean`. Clause 2 is the conformance side and never
mentions `merge`. As the paper says, the canonical join laws alone do not
establish conformance, which is why the two never meet before the last file.
-/

namespace LeanProofs.NoSpecNonComm.Soundness

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

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

/-- `lo^C_E` has no edges when every pair of events commutes. The
non-commuting disjunct fails by `hcomm`; so does the `rc` disjunct, because
RC-NON-COMM read right to left turns an `rc` edge into a non-commuting
pair. Clause 1 is then satisfied by any enumeration. -/
theorem paperOrder_false (hru : UniformRcNonComm D)
    (hcomm : ∀ e₁ e₂ : D.Event, D.Commutes e₁ e₂) (C : Configuration D.toMRDTSig)
    (E : Set D.Event) (a b : D.Event) :
    ¬ paperOrder (policy D) C.replayContext E a b := by
  rintro (⟨-, hnc⟩ | ⟨-, -, hb, -⟩)
  · exact hnc (hcomm a b)
  · exact (hru a b).mpr (Or.inl hb) (hcomm a b)

end LeanProofs.NoSpecNonComm.Soundness
