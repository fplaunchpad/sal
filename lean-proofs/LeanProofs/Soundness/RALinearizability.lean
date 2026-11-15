import LeanProofs.Soundness.LinearExtension
import LeanProofs.Soundness.SequentialSpec

/-!
# The overall soundness theorem

The adequacy theorem of Section 5: the obligations and the sequential premise
give RA-linearizability of every certified execution. This is the only file
that uses both clauses of Definition 4, so it is the only one that needs both
`Soundness/LinearExtension.lean` and `Soundness/SequentialSpec.lean`.

```
  Laws + VC1..VC5        per implementation, or a direct Join
      |
      v
  the join lemma         Metatheory.joinLemma, or supplied by the row
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
theorem certifiedRA_of_laws (laws : Laws D) {S : Spec type}
    {I : Issuance D.toMRDTSig}
    (join : ∀ C : Configuration D.toMRDTSig,
      MintHonest D.toMRDTSig I.CanIssue C → Interface.JoinAtConfig D C)
    (sound : SpecSound D S) : CertifiedRA D S I :=
  certifiedRA_of_join_total laws.toRestricted join sound

/-- The all-commuting specialisation, where `Laws` and the join lemma both
come from `Obligations`. -/
theorem certifiedRA (h : Obligations D) {S : Spec type}
    {I : Issuance D.toMRDTSig} (sound : SpecSound D S) :
    CertifiedRA D S I :=
  certifiedRA_of_laws (Metatheory.laws h)
    (fun C _ => Interface.joinConfig_of_join (Metatheory.joinLemma h) C) sound

/-- **The adequacy theorem, as a direct-route row states it.** The same as
`certifiedRA_of_laws`, with the two convergence hypotheses taken as the one
bundle `Interface/DirectRoute.lean` defines. This is the direct route's
counterpart of `certifiedRA`. -/
theorem certifiedRA_direct {S : Spec type} {I : Issuance D.toMRDTSig}
    (h : DirectObligations D I) (sound : SpecSound D S) : CertifiedRA D S I :=
  certifiedRA_of_laws h.laws h.join sound

/-! ## With the execution-scoped premise -/

/-- **The adequacy theorem, scoped form.** Identical to `certifiedRA` except
that the sequential premise may pick its own witness. -/
theorem certifiedRA_scoped_of_laws (laws : Laws D) {S : Spec type}
    {I : Issuance D.toMRDTSig}
    (join : ∀ C : Configuration D.toMRDTSig,
      MintHonest D.toMRDTSig I.CanIssue C → Interface.JoinAtConfig D C)
    (history : HistorySound D S I) : CertifiedRA D S I :=
  certifiedRA_of_join laws.toRestricted join history

/-- The all-commuting specialisation of the scoped theorem. -/
theorem certifiedRA_scoped (h : Obligations D) {S : Spec type}
    {I : Issuance D.toMRDTSig} (history : HistorySound D S I) :
    CertifiedRA D S I :=
  certifiedRA_scoped_of_laws (Metatheory.laws h)
    (fun C _ => Interface.joinConfig_of_join (Metatheory.joinLemma h) C) history

/-! ## Relating the two premises

This is the one statement that genuinely needs both clauses: clause 2 gives
the answer, and clause 1, in the form `paperOrder_false`, says the arbitrary
enumeration it was proved for is already a linear extension. -/

end LeanProofs.Soundness
