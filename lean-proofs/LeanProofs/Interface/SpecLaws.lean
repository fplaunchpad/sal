import LeanProofs1.Interface.Laws
import LeanProofs1.Interface.VCRoute
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

namespace LeanProofs1.Interface

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
counter's case, whose `Spec` adds. A row whose `Spec` overwrites, or whose
`Spec` distinguishes `add` from `remove`, has to prove the law outright. -/
theorem spec_non_comm_of_spec_commutes {D : Impl type}
    {S : HistorySpec type.OType type.QType type.ValType}
    (h : ∀ o₁ o₂ : type.OType, spec_commutes S o₁ o₂) : spec_non_comm D S :=
  fun e₁ e₂ hn => (hn (h e₁.op e₂.op)).elim

/-! ## The bundle the specification route consumes

`Obligations` is `Spec`-free on purpose. Five rows of the paper prove that
every pair of their events commutes while their specification's updates do
not all commute, and for such a row SPEC-NON-COMM is not merely unproved
but **false**; `Implementations/RGA/SpecNonComm.lean` refutes one case
outright. Those rows reach Definition 4 through `certifiedRA_scoped`, which
never asks for the fourth law, and the join metatheory never sees `Spec`.

A row that does satisfy the fourth law bundles it together with the rest
here, so that the soundness theorem takes one obligation object rather than
two separate arguments.
-/

/-- **Everything the specification route consumes**, at the contexts `Good`
admits: the obligation bundle of Section 5 together with SPEC-NON-COMM, the
one law of Section 4 that mentions `Spec`. -/
structure SpecObligationsOn (D : Impl type) (Good : Ctx D → Prop)
    (S : HistorySpec type.OType type.QType type.ValType) : Prop where
  /-- `Laws(D_type)`, VC1 to VC5, and the execution order. -/
  toObligationsOn : ObligationsOn D Good
  /-- **SPEC-NON-COMM**, the fourth law of Section 4. -/
  spec_non_comm : LeanProofs1.Interface.spec_non_comm D S

/-- **The bundle at every context**, which is what a row with no issuance
guard supplies. -/
abbrev SpecObligations (D : Impl type)
    (S : HistorySpec type.OType type.QType type.ValType) : Prop :=
  SpecObligationsOn D (fun _ => True) S

/-- **The bundle for a guarded row**, from the laws, the five conditions and
SPEC-NON-COMM. The three fields `ObligationsOn` derives are derived here
too, so a row never has to name the intermediate bundle. -/
theorem SpecObligationsOn.ofUniform {D : Impl type} {Good : Ctx D → Prop}
    {S : HistorySpec type.OType type.QType type.ValType}
    (h : Laws D) (hru : UniformRcNonComm D) (hcc : UniformCondComm D)
    (vcs : CanonicalJoinLawsOn D Good) (covered : _root_.LeanProofs1.Interface.spec_non_comm D S) :
    SpecObligationsOn D Good S :=
  ⟨ObligationsOn.ofUniform h hru hcc vcs, covered⟩

/-- The same at every context. -/
theorem SpecObligations.ofUniform {D : Impl type}
    {S : HistorySpec type.OType type.QType type.ValType}
    (h : Laws D) (hru : UniformRcNonComm D) (hcc : UniformCondComm D)
    (vcs : CanonicalJoinLawsOn D (fun _ => True)) (covered : _root_.LeanProofs1.Interface.spec_non_comm D S) :
    SpecObligations D S :=
  ⟨Obligations.ofUniform h hru hcc vcs, covered⟩

/-- **The bundle for a row whose events all commute.** `Laws(D_type)` then
forces `rc` to be empty, so the two cases it leaves open are vacuous. -/
theorem SpecObligations.ofCommuting {D : Impl type}
    {S : HistorySpec type.OType type.QType type.ValType}
    (h : Laws D) (all_comm : ∀ e₁ e₂ : D.Event, D.Commutes e₁ e₂)
    (vcs : CanonicalJoinLawsOn D (fun _ => True)) (covered : _root_.LeanProofs1.Interface.spec_non_comm D S) :
    SpecObligations D S :=
  ⟨Obligations.ofCommuting h all_comm vcs, covered⟩

end LeanProofs1.Interface
