import LeanProofs.Soundness.LinearExtension
import LeanProofs.Soundness.SequentialSpec

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

/-! ## With the unrestricted premise -/

/-- **The adequacy theorem.** The obligations and the sequential premise give
RA-linearizability of every certified execution. -/
theorem certifiedRA_of_laws (laws : Laws D) (rc_non_comm : UniformRcNonComm D)
    (cond_comm : UniformCondComm D) {S : Spec type} {I : Issuance D.toMRDTSig}
    (join : ∀ C : Configuration D.toMRDTSig,
      MintHonest D.toMRDTSig I.CanIssue C → JoinAtConfig D C)
    (sound : SpecSound D S) : CertifiedRA D S I :=
  certifiedRA_of_join_total (laws.toRestricted rc_non_comm cond_comm) join sound

/-- **The adequacy theorem on the VC route**, for any row. `Laws` and the
five conditions are fields of `Obligations`; only the join lemma comes from
the metatheory. -/
theorem certifiedRA (h : Obligations D) {S : Spec type}
    {I : Issuance D.toMRDTSig} (sound : SpecSound D S) :
    CertifiedRA D S I :=
  certifiedRA_of_laws h.laws h.rc_non_comm h.cond_comm
    (fun C _ => joinConfig_of_join (Metatheory.joinLemma h) C) sound

/-- **The adequacy theorem on the guarded VC route.** A row whose issuance
guard its join lemma depends on states the five conditions at the contexts
that guard admits, and supplies `good`: every mint-honest configuration
presents such a context. The remove-wins set is the one row of Table 1 that
needs this, and `Obligations.toOn` lets any other row use it too. -/
theorem certifiedRA_on {Good : Interface.Ctx D → Prop} (h : ObligationsOn D Good)
    {S : Spec type} {I : Issuance D.toMRDTSig}
    (good : ∀ C : Configuration D.toMRDTSig,
      MintHonest D.toMRDTSig I.CanIssue C → Good C.replayContext)
    (sound : SpecSound D S) : CertifiedRA D S I :=
  certifiedRA_of_laws h.laws h.rc_non_comm h.cond_comm
    (fun C hm => Metatheory.joinLemmaOn h C.replayContext (good C hm)) sound

/-! ## With the execution-scoped premise -/

/-- **The adequacy theorem, scoped form.** Identical to `certifiedRA` except
that the sequential premise may pick its own witness. -/
theorem certifiedRA_scoped_of_laws (laws : Laws D) (rc_non_comm : UniformRcNonComm D)
    (cond_comm : UniformCondComm D) {S : Spec type} {I : Issuance D.toMRDTSig}
    (join : ∀ C : Configuration D.toMRDTSig,
      MintHonest D.toMRDTSig I.CanIssue C → JoinAtConfig D C)
    (history : HistorySound D S I) : CertifiedRA D S I :=
  certifiedRA_of_join (laws.toRestricted rc_non_comm cond_comm) join history

/-- The all-commuting specialisation of the scoped theorem. -/
theorem certifiedRA_scoped (h : Obligations D) {S : Spec type}
    {I : Issuance D.toMRDTSig} (history : HistorySound D S I) :
    CertifiedRA D S I :=
  certifiedRA_scoped_of_laws h.laws h.rc_non_comm h.cond_comm
    (fun C _ => joinConfig_of_join (Metatheory.joinLemma h) C) history

/-! ## Relating the two premises

This is the one statement that genuinely needs both clauses: clause 2 gives
the answer, and clause 1, in the form `paperOrder_false`, says the arbitrary
enumeration it was proved for is already a linear extension. -/

end LeanProofs.Soundness
