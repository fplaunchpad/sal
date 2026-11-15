import LeanProofs.Interface.VCRoute
import LeanProofs.Interface.DirectRoute
import Artifact.MRDTs.Metatheory.Correctness

/-!
# Adequacy: the obligations imply the join lemma

Proved once, for every implementation. No datatype is named here and no
implementation may add to this file.

The chain follows Section 5 of the paper:

```
  Laws(D_type)  +  VC1..VC5        per implementation
      |
      v
  the join lemma                  merging canonical states is canonical
```

`Soundness` carries the chain further, to canonical correctness and then,
with `SpecSound`, to RA-linearizability. Nothing here consults `Spec`: as
the paper says, the canonical join laws alone do not establish conformance.

## Two routes to the join lemma

`joinLemma_of_vcs` is the route of Section 5: discharge the five VCs and the
lemma follows. `Obligations` below is the special case in which every pair of
events commutes, where `Laws` is free and VC4 is derived.

Not every row satisfies the arbitrary-state VCs of `CanonicalJoinLaws`. An
implementation outside that family proves `Join` directly, at `rcOrder`, and
passes it to `Soundness` itself. Both routes end at the same statement, so
nothing downstream can tell them apart.
-/

namespace LeanProofs.Metatheory

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1 LeanProofs.Interface

variable {type : MRDTType} {D : Impl type}

/-! ## The general route

Everything in this section holds for an arbitrary `rc`. -/

/-- `Laws(D_type)` is the framework's replay contract. RC-NON-COMM supplies
`noncomm_covered`, NO-RC-CHAIN supplies acyclicity, COND-COMM supplies the
absorber clause. -/
theorem replayLaws (h : Laws D) (hp : PayloadDetermined D) :
    @ReplayLaws D.toMRDTSig.toUpdateSig (rcOrder D) :=
  (h.toRestricted hp).replayLaws

theorem mergeLaws (h : Laws D) (hp : PayloadDetermined D) (vcs : CanonicalJoinLaws D) :
    @MergeLaws D.toMRDTSig (rcOrder D) :=
  letI : EventOrder D.toMRDTSig.toUpdateSig := rcOrder D
  ⟨replayLaws h hp, vcs.vc1_merge_comm, vcs.vc2_merge_init⟩

theorem deltaLaws (vcs : CanonicalJoinLaws D) : DeltaLaws D.toMRDTSig :=
  ⟨vcs.vc5_redistribute, vcs.vc3_local_redistribute⟩

theorem commutingPeelLaw (vcs : CanonicalJoinLaws D) : CommutingPeelLaw D.toMRDTSig :=
  ⟨vcs.commuting_peel⟩

/-- **The join lemma** from the five VCs: merging canonical states produces
the canonical state of the union of their event sets. -/
theorem joinLemma_of_vcs (h : Laws D) (hp : PayloadDetermined D)
    (vcs : CanonicalJoinLaws D)
    (vc4 : @CausalDeltaLaw D.toMRDTSig (rcOrder D)) : @Join D.toMRDTSig (rcOrder D) :=
  letI : EventOrder D.toMRDTSig.toUpdateSig := rcOrder D
  JoinProof.ofArbitraryStateLaws (mergeLaws h hp vcs) (deltaLaws vcs) vc4

/-! ## The all-commuting family

`Obligations` asserts that every pair of events commutes and that `rc` is
accordingly empty. `Laws` and VC4 both come for free. -/

/-- `Laws(D_type)` is free for this family. RC-NON-COMM holds because both
sides are false, and COND-COMM never has an `rc` edge to remove. -/
theorem laws (h : Obligations D) : Laws D := by
  have hno : ∀ e₁ e₂ : D.Event, ¬ D.EventRcBefore e₁ e₂ := fun e₁ e₂ hb =>
    OrderResult.noConfusion ((h.rc_either e₁.op e₂.op).symm.trans hb)
  refine ⟨fun e₁ e₂ _ _ => ⟨fun hn => (hn (h.all_commute e₁ e₂)).elim, ?_⟩, ?_, ?_⟩
  · rintro (hb | hb)
    · exact (hno _ _ hb).elim
    · exact (hno _ _ hb).elim
  · exact fun o₁ o₂ o₃ hc =>
      OrderResult.noConfusion ((h.rc_either o₁ o₂).symm.trans hc.1)
  · exact fun _ e e' _ _ hb _ => (hno e e' hb).elim

/-- Payload determinacy is free for this family: every pair commutes, so
both sides of the equivalence are always true. -/
theorem payloadDetermined (h : Obligations D) : PayloadDetermined D :=
  fun e₁ e₂ f₁ f₂ _ _ =>
    ⟨fun _ => h.all_commute f₁ f₂, fun _ => h.all_commute e₁ e₂⟩

/-- **VC4** CAUSAL-DELTA, `merge(B, A, e(B)) = e(A)`, derived rather than
assumed. This is the step that is available only because every pair of
events commutes. -/
theorem vc4_causal_delta (h : Obligations D) :
    @CausalDeltaLaw D.toMRDTSig (rcOrder D) :=
  letI : EventOrder D.toMRDTSig.toUpdateSig := rcOrder D
  causalDeltaLaw_of_all_comm (mergeLaws (laws h) (payloadDetermined h) h.joinLaws)
    (commutingPeelLaw h.joinLaws) h.all_commute

/-- The join lemma for the all-commuting family. -/
theorem joinLemma (h : Obligations D) : @Join D.toMRDTSig (rcOrder D) :=
  joinLemma_of_vcs (laws h) (payloadDetermined h) h.joinLaws (vc4_causal_delta h)

end LeanProofs.Metatheory
