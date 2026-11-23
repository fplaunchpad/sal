import LeanProofs.Interface.Laws
import Artifact.MRDTs.Paper1.SpecificationVisibility

/-!
# `Laws(D_type, Spec)`: the fourth law, and the four together

`Interface/Laws.lean` carries the three conditions of Section 4 that
constrain `rc` alone. This file adds the fourth, SPEC-NON-COMM, which is the
only one of the four that mentions `Spec`. `Laws` and `spec_non_comm` together
are the paper's `Laws(D_type, Spec)`. There is no structure bundling the
pair, because nothing consumes one.

```
  SPEC-NON-COMM(D_type, Spec)
    = forall o1 o2. not (o1 <->_Spec o2) ==> not (o1 <-> o2)
```

Two operations commute **in `Spec`** when swapping them never changes
whether a history is admitted. A query label may sit in the suffix, so two
updates that drive the specification to different states do not commute in
`Spec`: the query that tells them apart is itself a label of the history.

The law says a conflict the specification has may not be erased by the
implementation. It is what rules out the broken set of Section 6, whose
`rem_a` is the identity: there `add_a` and `rem_a` commute in the
implementation while they do not commute in `Spec`, so an execution that
adds and then removes can be linearized the wrong way round and still agree
with the state.

## Where it is consumed

No part of the convergence chain reads this law, and neither does
`RALinearizable`. What reads it is the stronger criterion of
`Artifact/MRDTs/Paper1/SpecificationVisibility.lean`, which asks the witness
to respect specification conflicts as well as `lo^C_E`. `spec_non_comm.covered`
below is that bridge, and it is a definitional one.
-/

namespace LeanProofs.Interface

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1

variable {type : MRDTType}

/-- `o1 <->_Spec o2`: swapping the two adjacent update labels never changes
whether a history is admitted. -/
abbrev spec_commutes (S : HistorySpec type.OType type.QType type.ValType)
    (o₁ o₂ : type.OType) : Prop :=
  S.Commutes o₁ o₂

/-- **SPEC-NON-COMM**, the fourth law of Section 4.

The paper states it over operations. It is stated here over events, which is
the form the criterion consumes and which says the same thing: the events
carry no information the implementation's `do` can see beyond their
timestamp and replica, and the hypothesis looks only at their labels. -/
def spec_non_comm (D : Impl type)
    (S : HistorySpec type.OType type.QType type.ValType) : Prop :=
  ∀ e₁ e₂ : D.Event, ¬ spec_commutes S e₁.op e₂.op → ¬ D.Commutes e₁ e₂

/-- SPEC-NON-COMM is the framework's `SpecificationConflictsCovered`, which
is what `specificationRA_of_canonical_total` asks for. The two statements
are the same one. -/
theorem spec_non_comm.covered {D : Impl type}
    {S : HistorySpec type.OType type.QType type.ValType} (h : spec_non_comm D S) :
    SpecificationConflictsCovered D.toMRDTSig S := h

/-- **SPEC-NON-COMM for a specification whose updates all commute.** The
hypothesis is then never satisfiable, so the law is immediate. This is the
case for every all-commuting row except the LWW register, whose `Spec`
overwrites. -/
theorem spec_non_comm_of_spec_commutes {D : Impl type}
    {S : HistorySpec type.OType type.QType type.ValType}
    (h : ∀ o₁ o₂ : type.OType, spec_commutes S o₁ o₂) : spec_non_comm D S :=
  fun e₁ e₂ hn => (hn (h e₁.op e₂.op)).elim

end LeanProofs.Interface
