import LeanProofs.Metatheory.Adequacy
import Artifact.MRDTs.Paper1.RALinearizability
import Artifact.MRDTs.Paper1.EventBridge

/-!
# The overall soundness theorem

Definition 4 of Section 4 and the adequacy theorem of Section 5, stated and
proved once for every implementation.

`Metatheory/Adequacy.lean` stops at canonical correctness: every stored
version holds `can(E(v))`. That is convergence, not yet the paper's criterion.
This file closes the remaining gap.

```
  Obligations            VC1..VC5 and all_commute, per implementation
      |
      v
  the join lemma         Metatheory.joinLemma
      |
      v
  canonical correctness  every stored version holds can(E(v))
      |
      +--  + SpecSound  -->  RA-linearizability
```

`SpecSound` is the paper's sequential premise verbatim: for every list of
events and every query, `ops(pi) . (q => b)` is admitted by `Spec`, where `b`
is the implementation's own answer. It compares `do` alone against an
independent language and never mentions `merge`.
-/

namespace LeanProofs.Soundness

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {type : MRDTType} {D : Impl type}

/-- `rc` as an operation policy. Empty for this family, as RC-NON-COMM
requires when every pair of events commutes. -/
abbrev policy (type : MRDTType) : OperationPolicy type.OType :=
  commutingPolicy type.OType

/-- `Spec` as a language of histories, which is the form Definition 4 uses. -/
abbrev Spec (type : MRDTType) : Type :=
  HistorySpec type.OType type.QType type.ValType

/-- The sequential premise. For every `pi` and `q`, the projected history
`ops(pi) . (q => b)` is in `Spec`, with `b` the implementation's answer. -/
abbrev SpecSound (D : Impl type) (S : Spec type) : Prop :=
  FoldHistorySound D.toMRDTSig S

/-- **Definition 4** at one configuration: for every replica's head version
and every query there is a linear extension of the version's events,
respecting `lo^C_E`, whose projected history with the implementation's answer
is admitted by `Spec`. -/
abbrev RALinearizable (D : Impl type) (S : Spec type)
    (C : Configuration D.toMRDTSig) : Prop :=
  Artifact.MRDTs.Paper1.RALinearizable D.toMRDTSig (policy type) S C

/-- The same, at every stored version rather than only at heads. -/
abbrev VersionsRALinearizable (D : Impl type) (S : Spec type)
    (C : Configuration D.toMRDTSig) : Prop :=
  Artifact.MRDTs.Paper1.VersionsRALinearizable D.toMRDTSig (policy type) S C

/-- Definition 4 at every configuration reachable by a certified execution,
ordinary or with recursively computed merge bases. -/
abbrev CertifiedRA (D : Impl type) (S : Spec type)
    (I : Issuance D.toMRDTSig) : Prop :=
  CertifiedRAV D.toMRDTSig (policy type) S I

/-- **The adequacy theorem.** The obligations and the sequential premise give
RA-linearizability of every certified execution.

Convergence comes from the left-hand premise, conformance from the right. The
canonical join laws alone do not establish conformance, which is why `sound`
is a separate hypothesis. -/
theorem certifiedRA (h : Obligations D) {S : Spec type}
    {I : Issuance D.toMRDTSig} (sound : SpecSound D S) :
    CertifiedRA D S I := by
  refine certifiedRA_of_join_total (restricted_of_all_commute h.all_commute)
    (fun C _ => ?_) sound
  simpa [commutingPolicy, OperationPolicy.lift, EventOrder.unconstrained,
    Metatheory.rcOrder] using Metatheory.joinLemma h C.replayContext

/-! ## The execution-scoped premise

`SpecSound` above quantifies over **every** list of events, which is the
paper's unrestricted sequential premise. Some implementations do not satisfy
it: their answer is explained only by a particular ordering of the events,
not by an arbitrary one. The LWW register is the first such row, where the
explaining history must be sorted by write key.

For those, the premise below lets the implementation **choose** the witness,
given a mint-honest configuration and a supported, causally closed, finite
event set. This is the `E = Y` column of Table 1. -/

/-- The scoped sequential premise: a witness may be selected per event set. -/
abbrev HistorySound (D : Impl type) (S : Spec type)
    (I : Issuance D.toMRDTSig) : Prop :=
  IssuedHistoryAdequacy D.toMRDTSig (policy type) S I

/-- **The adequacy theorem, scoped form.** Identical to `certifiedRA` except
that the sequential premise may pick its own witness. -/
theorem certifiedRA_scoped (h : Obligations D) {S : Spec type}
    {I : Issuance D.toMRDTSig} (history : HistorySound D S I) :
    CertifiedRA D S I := by
  refine certifiedRA_of_join (restricted_of_all_commute h.all_commute)
    (fun C _ => ?_) history
  simpa [commutingPolicy, OperationPolicy.lift, EventOrder.unconstrained,
    Metatheory.rcOrder] using Metatheory.joinLemma h C.replayContext

/-- The unrestricted premise implies the scoped one: any enumeration works. -/
theorem historySound_of_specSound (h : Obligations D) {S : Spec type}
    {I : Issuance D.toMRDTSig} (sound : SpecSound D S) : HistorySound D S I := by
  rintro C _ E _ _ ⟨pi, hpi⟩ q
  exact ⟨pi, hpi, hpi.1.imp (fun {_ _} _ =>
    paperOrder_false_of_all_commute h.all_commute _ _ _ _), sound pi q⟩

/-- The criterion at a single certified configuration. -/
theorem raLinearizable (h : Obligations D) {S : Spec type}
    {I : Issuance D.toMRDTSig} (sound : SpecSound D S)
    {C : Configuration D.toMRDTSig}
    (reach : MintCertifiedReachV D.toMRDTSig
      (canonicalVirtualMergeBase D.toMRDTSig) I C) :
    RALinearizable D S C :=
  certifiedRA h sound C reach

end LeanProofs.Soundness
