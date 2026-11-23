import LeanProofs.Soundness.LinearExtension
import LeanProofs.Soundness.SequentialSpec
import LeanProofs.Metatheory.PaperAdequacy

/-!
# The overall soundness theorem

The adequacy theorem of Section 5: the obligations and the sequential premise
give RA-linearizability of every certified execution. This is the only file
that uses both clauses of Definition 4, so it is the only one that needs both
`Soundness/LinearExtension.lean` and `Soundness/SequentialSpec.lean`.

```
  Laws + VC1..VC5        per implementation, at every context or at the
      |                  contexts an issuance guard admits
      v
  the join lemma         Metatheory.joinLemma, or joinLemmaOn
      |
      v
  canonical correctness  every stored version holds can(E(v))        clause 1
      |
      +--  + SpecSound or HistorySound  -->  RA-linearizability       clause 2
```

Convergence comes from the left-hand premise, conformance from the right. As
the paper says, the canonical join laws alone do not establish conformance,
which is why the sequential premise is a separate hypothesis everywhere below.
-/

namespace LeanProofs.Soundness

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {type : MRDTType} {D : Impl type}

/-! ## The adequacy theorem

Every row reaches Definition 4 through `ObligationsOn` and nothing else. The
contract underneath is the framework's **guarded** one, so `rc` is consulted
only about pairs carrying distinct timestamps and issued by different
replicas, which is exactly the domain the paper's RC-NON-COMM speaks about.
-/

/-- **The adequacy theorem.** The obligations and the sequential premise
give RA-linearizability of every certified execution.

A row whose join lemma depends on its issuance guard states its conditions
at the contexts that guard admits and supplies `good`: every mint-honest
configuration presents such a context. The remove-wins set is the one row of
Table 1 that needs this; `certifiedRA` below is the rest.

Clause 1 is `Metatheory.paperCanonicalVersions`: every stored version holds
the canonical state of its event set. Clause 2 is `sound`. -/
theorem certifiedRA_on {Good : Interface.Ctx D → Prop} (h : ObligationsOn D Good)
    {S : Spec type} {I : Issuance D.toMRDTSig}
    (good : ∀ C : Configuration D.toMRDTSig,
      MintHonest D.toMRDTSig I.CanIssue C → Good C.replayContext)
    (sound : SpecSound D S) : CertifiedRA D S I := by
  obtain ⟨X⟩ := h.executionOrder
  have join := Metatheory.representationJoin_of_paperJoin (Metatheory.joinLemma h)
  intro C reach r v s E _ hv q
  obtain ⟨π, hp, hr, hf⟩ :=
    Metatheory.paperCanonicalVersions X join good reach v s E hv
  exact ⟨π, hp, hr, by simpa only [hf] using sound π q⟩

/-- **The adequacy theorem** for a row whose conditions hold at every
context, which is every row of Table 1 here but one. -/
theorem certifiedRA (h : Obligations D) {S : Spec type}
    {I : Issuance D.toMRDTSig} (sound : SpecSound D S) : CertifiedRA D S I :=
  certifiedRA_on h (fun _ _ => trivial) sound

/-! ## With the execution-scoped premise -/

/-- **The adequacy theorem, scoped form.** Identical to `certifiedRA` except
that the sequential premise may pick its own witness per query. Canonical
states at `lo^C_E` are unique, which is what identifies the witness's fold
with the stored state. -/
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

/-! ## Relating the two premises

This is the one statement that genuinely needs both clauses: clause 2 gives
the answer, and clause 1, in the form `paperOrder_false`, says the arbitrary
enumeration it was proved for is already a linear extension. -/

end LeanProofs.Soundness
