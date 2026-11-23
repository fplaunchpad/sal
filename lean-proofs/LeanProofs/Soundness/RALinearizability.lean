import LeanProofs1.Soundness.SequentialSpec
import LeanProofs1.Metatheory.Adequacy

/-!
# The overall soundness theorem

The adequacy theorem of Section 5: the obligations and the sequential premise
give RA-linearizability of every certified execution. This is the only file
that uses both clauses of Definition 4, so it is the only one that reads both
`Metatheory/Adequacy.lean` and `Soundness/SequentialSpec.lean`.

```
  Laws + VC1..VC5        per implementation, at every context or at the
      |                  contexts an issuance guard admits
      v
  the join lemma         Metatheory.joinLemma
      |
      v
  canonical correctness  every stored version holds can(E(v))        clause 1
      |
      +--  + SpecSound  -->  RA-linearizability                       clause 2
```

Convergence comes from the left-hand premise, conformance from the right. As
the paper says, the canonical join laws alone do not establish conformance,
which is why the sequential premise is a separate hypothesis everywhere below.
-/

namespace LeanProofs1.Soundness

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

variable {type : MRDTType} {D : Impl type}

/-! ## The adequacy theorem

Every row reaches Definition 4 through `ObligationsOn` and nothing else. The
contract underneath is the framework's **guarded** one, so `rc` is consulted
only about pairs carrying distinct timestamps and issued by different
replicas, which is exactly the domain the paper's RC-NON-COMM speaks about.
-/

/-- Definition 4 strengthened with specification visibility, at every
certified execution. -/
abbrev SpecCertifiedRA (D : Impl type) (S : Spec type) (I : Issuance D.toMRDTSig) :
    Prop :=
  ∀ C : Configuration D.toMRDTSig,
    MintCertifiedReachV D.toMRDTSig (canonicalVirtualMergeBase D.toMRDTSig) I C →
    SpecificationRALinearizable D.toMRDTSig (policy D) S C

/-- **The adequacy theorem with all four laws.** The witness clause 1
produces already respects `lo^C_E`, and SPEC-NON-COMM says every
specification conflict is an `lo^C_E` edge, so the same witness respects
specification visibility too. -/
theorem certifiedSpecRA {S : Spec type} {I : Issuance D.toMRDTSig}
    (h : SpecObligations D S) (sound : SpecSound D S) :
    SpecCertifiedRA D S I := by
  obtain ⟨X⟩ := h.toObligationsOn.executionOrder
  have join :=
    Metatheory.representationJoin_of_paperJoin (Metatheory.joinLemma h.toObligationsOn)
  intro C reach r v s E _ hv q
  obtain ⟨π, hp, hr, hf⟩ :=
    Metatheory.paperCanonicalVersions X join (fun _ _ => trivial) reach v s E hv
  refine ⟨π, hp, hr, ?_, by simpa only [hf] using sound π q⟩
  exact hr.imp (fun {_ _} hno hedge =>
    hno (specVisibility_sub_paperOrder h.spec_non_comm.covered _ E _ _ hedge))

/-- Definition 4 itself follows, so a row proving the fourth law need not
prove the criterion twice. -/
theorem certifiedRA_of_spec {S : Spec type} {I : Issuance D.toMRDTSig}
    (h : SpecCertifiedRA D S I) : CertifiedRA D S I :=
  fun C reach => (h C reach).active

/-! ## With an issuance guard

A row whose join lemma is false without its guard states its conditions at
the contexts the guard admits, and discharges that side condition from
`MintHonest`, which is what a certified execution gives it. -/

/-- Definition 4 strengthened with specification visibility, at every
certified execution, for a row whose obligations hold only at the contexts
`Good` admits. -/
abbrev SpecCertifiedRAOn (D : Impl type) (_Good : Interface.Ctx D → Prop)
    (S : Spec type) (I : Issuance D.toMRDTSig) : Prop :=
  ∀ C : Configuration D.toMRDTSig,
    MintCertifiedReachV D.toMRDTSig (canonicalVirtualMergeBase D.toMRDTSig) I C →
    SpecificationRALinearizable D.toMRDTSig (policy D) S C

/-- **The adequacy theorem under an issuance guard.** Identical to
`certifiedSpecRA` except that the obligations are asked only of `Good`
contexts, and `good` says every mint-honest configuration induces one. -/
theorem certifiedSpecRA_on {Good : Interface.Ctx D → Prop} {S : Spec type}
    (h : SpecObligationsOn D Good S) {I : Issuance D.toMRDTSig}
    (good : ∀ C : Configuration D.toMRDTSig,
      MintHonest D.toMRDTSig I.CanIssue C → Good C.replayContext)
    (sound : SpecSound D S) :
    SpecCertifiedRAOn D Good S I := by
  obtain ⟨X⟩ := h.toObligationsOn.executionOrder
  have join :=
    Metatheory.representationJoin_of_paperJoin (Metatheory.joinLemma h.toObligationsOn)
  intro C reach r v s E _ hv q
  obtain ⟨π, hp, hr, hf⟩ :=
    Metatheory.paperCanonicalVersions X join good reach v s E hv
  refine ⟨π, hp, hr, ?_, by simpa only [hf] using sound π q⟩
  exact hr.imp (fun {_ _} hno hedge =>
    hno (specVisibility_sub_paperOrder h.spec_non_comm.covered _ E _ _ hedge))

/-- Definition 4 itself follows, as before. -/
theorem certifiedRA_of_spec_on {Good : Interface.Ctx D → Prop} {S : Spec type}
    {I : Issuance D.toMRDTSig} (h : SpecCertifiedRAOn D Good S I) :
    CertifiedRA D S I :=
  fun C reach => (h C reach).active

/-! ## With the execution-scoped premise

A row that cannot satisfy `SpecSound` supplies `HistorySound` instead. This
route reaches Definition 4 but not specification visibility, because the
witness is the row's own history rather than the one clause 1 built, so
`certifiedSpecRA` does not apply to it. -/

/-- **The adequacy theorem with the execution-scoped premise.** Clause 1
still comes from the obligations; clause 2 comes from the history the row
chooses, and canonical uniqueness identifies the two. -/
theorem certifiedRA_scoped (h : Obligations D) {S : Spec type}
    {I : Issuance D.toMRDTSig} (history : HistorySound D S I) :
    CertifiedRA D S I := by
  obtain ⟨X⟩ := h.executionOrder
  have hl := guardedLaws h.laws h.equal_op_commutes h.same_rep_cond_comm
  have join := Metatheory.representationJoin_of_paperJoin (Metatheory.joinLemma h)
  intro C reach r v s E _ hv q
  letI : EventOrder D.toMRDTSig.toUpdateSig := X.order
  have cfg := Metatheory.paperCanonicalConfig X join (fun _ _ => trivial) reach
  have hsup := cfg.version_events_supported v s E hv
  have hcan := Metatheory.paperCanonicalVersions X join (fun _ _ => trivial)
    reach v s E hv
  obtain ⟨ρ, hρ, -, -⟩ := id hcan
  obtain ⟨π, hp, hr, hadm⟩ := history C reach.mintHonest E hsup
    (cfg.version_events_causal v s E hv) ⟨ρ, hρ⟩ q
  have heq : applySeq D.toMRDTSig.toUpdateSig D.toMRDTSig.init π = s :=
    ConcreteMRDT.canonical_unique hl C.replayContext E hsup ⟨π, hp, hr, rfl⟩ hcan
  exact ⟨π, hp, hr, by simpa only [heq] using hadm⟩

/-! ## With both the issuance guard and the execution-scoped premise

A row may need each for a different reason: a guard because its conditions
hold only at the contexts an execution produces, and the scoped premise
because its `Spec` is order-sensitive. The optional register is such a row. -/

/-- **The adequacy theorem with a guard and the execution-scoped premise.**
Identical to `certifiedRA_scoped` except that the obligations are asked only
of `Good` contexts, and `good` says every mint-honest configuration induces
one. -/
theorem certifiedRA_scoped_on {Good : Interface.Ctx D → Prop}
    (h : ObligationsOn D Good) {S : Spec type} {I : Issuance D.toMRDTSig}
    (good : ∀ C : Configuration D.toMRDTSig,
      MintHonest D.toMRDTSig I.CanIssue C → Good C.replayContext)
    (history : HistorySound D S I) : CertifiedRA D S I := by
  obtain ⟨X⟩ := h.executionOrder
  have hl := guardedLaws h.laws h.equal_op_commutes h.same_rep_cond_comm
  have join := Metatheory.representationJoin_of_paperJoin (Metatheory.joinLemma h)
  intro C reach r v s E _ hv q
  letI : EventOrder D.toMRDTSig.toUpdateSig := X.order
  have cfg := Metatheory.paperCanonicalConfig X join good reach
  have hsup := cfg.version_events_supported v s E hv
  have hcan := Metatheory.paperCanonicalVersions X join good reach v s E hv
  obtain ⟨ρ, hρ, -, -⟩ := id hcan
  obtain ⟨π, hp, hr, hadm⟩ := history C reach.mintHonest E hsup
    (cfg.version_events_causal v s E hv) ⟨ρ, hρ⟩ q
  have heq : applySeq D.toMRDTSig.toUpdateSig D.toMRDTSig.init π = s :=
    ConcreteMRDT.canonical_unique hl C.replayContext E hsup ⟨π, hp, hr, rfl⟩ hcan
  exact ⟨π, hp, hr, by simpa only [heq] using hadm⟩
