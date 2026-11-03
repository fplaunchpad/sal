import LeanProofs.Interface.Laws
import Artifact.MRDTs.Metatheory.Correctness

/-!
# Adequacy: the obligations imply RA-linearizability

Proved once, for every implementation. No datatype is named here and no
implementation may add to this file.

The chain follows Section 5 of the paper:

```
  Obligations                     supplied per implementation
      |
      v
  Laws(D_type)  +  VC1..VC5        VC4 derived here for this family
      |
      v
  the join lemma                  merging canonical states is canonical
      |
      v
  canonical correctness           every stored version holds can(E(v))
      |
      +--  + Conformance  -->     RA-linearizability
```

The last arrow is the only one that consults `Spec`. As the paper says, the
canonical join laws alone do not establish conformance.
-/

namespace LeanProofs.Metatheory

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

variable {type : MRDTType} {D : Impl type}

/-- The replay order the argument runs at. `rc_either` says the
implementation's own `rc` agrees with it on every pair. -/
abbrev rcOrder (D : Impl type) : EventOrder D.toMRDTSig.toUpdateSig :=
  EventOrder.unconstrained D.toMRDTSig.toUpdateSig

/-- NO-RC-CHAIN gives acyclicity of `rc`, which Lemma `cor:lo-agree` needs
so that `lo^C_E` admits a linear extension. -/
theorem rcAcyclic : @ReplayAcyclic D.toMRDTSig.toUpdateSig (rcOrder D) := by
  apply replayAcyclic_of_noReplayChain
  intro a b c h
  exact OrderResult.noConfusion h.1

/-- `Laws(D_type)` is free for this family. RC-NON-COMM holds vacuously
because every pair commutes, and COND-COMM never has an `rc` edge to remove. -/
theorem laws (h : Obligations D) : Laws D := by
  refine ⟨fun e₁ e₂ hn => (hn (h.all_commute e₁ e₂)).elim, ?_, ?_⟩
  · intro e₁ e₂ e₃ hc
    exact OrderResult.noConfusion ((h.rc_either e₁ e₂).symm.trans hc.1)
  · intro sigma e e' e'' pi _ _ _ hb _
    exact OrderResult.noConfusion ((h.rc_either e e').symm.trans hb)

theorem replayLaws (h : Obligations D) :
    @ReplayLaws D.toMRDTSig.toUpdateSig (rcOrder D) :=
  ReplayLaws.of_all_comm h.all_commute rcAcyclic

theorem mergeLaws (h : Obligations D) : @MergeLaws D.toMRDTSig (rcOrder D) :=
  ⟨replayLaws h, h.joinLaws.vc1_merge_comm, h.joinLaws.vc2_merge_init⟩

theorem deltaLaws (h : Obligations D) : DeltaLaws D.toMRDTSig :=
  ⟨h.joinLaws.vc5_redistribute, h.joinLaws.vc3_local_redistribute⟩

theorem commutingPeelLaw (h : Obligations D) : CommutingPeelLaw D.toMRDTSig :=
  ⟨h.joinLaws.commuting_peel⟩

/-- **VC4** CAUSAL-DELTA, `merge(B, A, e(B)) = e(A)`, derived rather than
assumed. This is the step that is available only because every pair of
events commutes. -/
theorem vc4_causal_delta (h : Obligations D) : CausalDeltaLaw D.toMRDTSig :=
  causalDeltaLaw_of_all_comm (mergeLaws h) (commutingPeelLaw h) h.all_commute

/-- **The join lemma**: merging canonical states produces the canonical
state of the union of their event sets. The implementation never proves this. -/
theorem joinLemma (h : Obligations D) : @Join D.toMRDTSig (rcOrder D) :=
  JoinProof.ofArbitraryStateLaws (mergeLaws h) (deltaLaws h) (vc4_causal_delta h)

/-- Canonical correctness: every stored version of a reachable configuration
holds `can(E(v))`. -/
def canonicalCorrectness (h : Obligations D) (I : Issuance D.toMRDTSig) :
    @ReplayAdequacyCertificate D.toMRDTSig I (rcOrder D) :=
  ReplayAdequacyCertificate.ofJoin I (joinLemma h)

/-- **RA-linearizability.** Convergence comes from the canonical join laws,
conformance from `Conformance`. -/
noncomputable def raLinearizable (h : Obligations D) (I : Issuance D.toMRDTSig)
    (Spec : SequentialSpec D.toMRDTSig) (Rel : D.Sigma → Spec.State → Prop)
    (hc : Conformance D Spec Rel) : VerifiedMRDT D.toMRDTSig where
  issuance := I
  replayOrder := rcOrder D
  replayAdequacy := canonicalCorrectness h I
  Spec := Spec
  Rel := Rel
  sequentialCorrectness := SequentialCorrectnessCertificate.ofTotal
    (fun C _ => joinLemma h C.replayContext)
    h.all_commute
    (fun _ _ => rfl)
    hc.legal
    hc.refines
    hc.observes

end LeanProofs.Metatheory
