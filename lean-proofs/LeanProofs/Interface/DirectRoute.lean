import LeanProofs.Interface.Laws
import Artifact.MRDTs.Metatheory.Correctness

/-!
# The direct route: the join lemma itself

What a row takes on when the arbitrary-state VCs of `Interface/VCRoute.lean`
are unavailable. Five rows of Table 1 take this route, all of them with `rc`
nonempty.

Section 5 indexes every obligation by a configuration. `can_C(E)` is the
canonical state of `E` at `C`, and the join lemma reads "let `C` be a
configuration, then for all weakly closed `E1, E2` of `E_C`". The
definitions below are those statements, carrying `C` as the paper does.

A configuration's replay context, `C.replayContext`, is the projection the
vendored proof layer runs on. It is `<L, vis>` with `L = headEvents`, and the
paper has no name for it. It is an implementation detail of the proofs here
and appears in no statement this development owns.

Weak closure is the hypothesis `JoinAt` already carries: `vis`-predecessors
that do not commute. The paper's `WeakClosed_C(E)` is the same condition.

Both routes end at the same statement, `Join` at `rcOrder`, so nothing
downstream can tell them apart.
-/

namespace LeanProofs.Interface

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1

variable {type : MRDTType} {D : Impl type}

/-- The replay order the argument runs at: `rc`, lifted from operations to
the events that carry them. `lo^C_E` is built from this together with `vis`. -/
noncomputable abbrev rcOrder (D : Impl type) : EventOrder D.toMRDTSig.toUpdateSig :=
  (policy D).lift

/-! ## The configuration-indexed statements

Section 5 indexes every obligation by a configuration. `can_C(E)` is the
canonical state of `E` at `C`, and the join lemma reads "let `C` be a
configuration, then for all weakly closed `E1, E2` of `E_C`". The four
definitions below are those statements, carrying `C` as the paper does.

A configuration's replay context, `C.replayContext`, is the projection the
vendored proof layer runs on. It is `<L, vis>` with `L = headEvents`, and the
paper has no name for it. It is an implementation detail of the proofs here
and appears in no statement this development owns.

Weak closure is the hypothesis `JoinAt` already carries: `vis`-predecessors
that do not commute. The paper's `WeakClosed_C(E)` is the same condition. -/

/-- `IsCan_C(E, s)`: `s` is the canonical state of `E` at the configuration
`C`, the fold of any enumeration of `E` respecting `lo^C_E`. Written
`can_C(E) = s` in Section 5, which is well defined by determinacy. -/
abbrev IsCan (D : Impl type) (C : Configuration D.toMRDTSig)
    (E : Set D.Event) (s : D.Sigma) : Prop :=
  @IsCanonicalState D.toMRDTSig.toUpdateSig (rcOrder D) C.replayContext E s

/-- **Lemma (Join)** at one configuration. For weakly closed `E1, E2` of
`E_C`, merging `can_C(E1 n E2)`, `can_C(E1)` and `can_C(E2)` gives
`can_C(E1 u E2)`. -/
abbrev JoinAtConfig (D : Impl type) (C : Configuration D.toMRDTSig) : Prop :=
  @JoinAt D.toMRDTSig (rcOrder D) C.replayContext

/-- **Lemma (Join)**: the obligation at every configuration. -/
abbrev JoinConfig (D : Impl type) : Prop :=
  ∀ C : Configuration D.toMRDTSig, JoinAtConfig D C

/-- The vendored all-context join supplies the paper's statement. The
converse is not available. -/
theorem joinConfig_of_join (h : @Join D.toMRDTSig (rcOrder D)) : JoinConfig D :=
  fun C => h C.replayContext

/-- **What a direct-route row supplies.** `Laws(D_type)`, proved by hand
rather than derived, and the join lemma at every configuration the row's
issuance guard admits. The two fields are exactly the two hypotheses
`Soundness.certifiedRA_of_laws` consumes.

An unscoped row passes `fun C _ => joinLemma C`; a row with a guard, such as
the remove-wins set, uses the `MintHonest` hypothesis. -/
structure DirectObligations (D : Impl type) (I : Issuance D.toMRDTSig) : Prop where
  /-- RC-NON-COMM, NO-RC-CHAIN and COND-COMM, proved by the row. -/
  laws : Laws D
  /-- **Lemma (Join)**, proved by the row at every mint-honest configuration. -/
  join : ∀ C : Configuration D.toMRDTSig,
    MintHonest D.toMRDTSig I.CanIssue C → JoinAtConfig D C

end LeanProofs.Interface
