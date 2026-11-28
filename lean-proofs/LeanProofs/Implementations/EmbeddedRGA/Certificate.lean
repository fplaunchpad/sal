import LeanProofs_no_spec_non_comm.Implementations.EmbeddedRGA.Honesty
import Artifact.MRDTs.Paper1.EventBridge

/-!
# Embedded RGA: RA-linearizability

The row reaches the criterion through the invariant-scoped reading of
`Artifact/MRDTs/Paper1/InvariantOrder.lean`, and `Negative.lean` proves
that it cannot reach the unscoped one through any `rc`. So the invariant
reading is not a convenience here but the only route.

The chain, with nothing left implicit.

```
  issuance                                      Honesty.lean
      |
      v   CoordHonest, DelBorn
  concurrent events commute at valid states     Commutation.lean
      |
      v
  convergence, and the join                     Replay.lean, Join.lean
      |
      v
  every stored version is a causal replay       representedVersions
      |
      v
  InvariantOrder.VersionsRA                     raLinearizable
```

The sequential specification is the row's own sequential semantics over
the event alphabet, through the identity abstraction of Section 6. The
paper's artifact additionally proves that this agrees with an independent
editor semantics, splicing after an anchor and deleting by identifier;
that correspondence is not proved here.

**A duplicate.** This is `Implementations/EmbeddedRGA/` with the namespace
changed, carried into this folder because `AnchoredQueue/` rests on it. No
proof here changes, and none needs to: the criterion this family reaches,
`InvariantOrder.VersionsRA`, already carries the specification-visibility
clause, and `raLinearizable` below discharges it from `respects ρ C.vis`
alone. SPEC-NON-COMM appears nowhere in the family.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

variable {Γ : Scheme} {α : Type} [DecidableEq α] {Q : QueryOf Γ α}

attribute [local instance] birthEventOrder

/-- `Issued` is what `MintHonest` says for this row.

The guard is a parameter, asked only to imply the core's. A row may ask for
more than the core does and still use everything below: the anchored FIFO
queue asks an enqueue to anchor on the **live tail** and a dequeue to name
the **observed head**, both of which imply the core's conditions. -/
theorem issued_of_mintHonest {G : Op (AppOp Γ α) → St Γ α → Prop}
    (hG : ∀ e s, G e s → CoreGuard e s)
    {C : Configuration (Dα Γ α Q).toMRDTSig}
    (hm : MintHonest (Dα Γ α Q).toMRDTSig G C) :
    Issued C.replayContext := by
  intro f hf
  obtain ⟨π, hp, -, hguard⟩ := hm f hf
  exact ⟨π, fun u hu => ((hp.2 u).mp hu).1, fun u hu => ((hp.2 u).mp hu).2,
    hG _ _ hguard⟩

/-- **The canonical configuration**, at the birth order. -/
theorem canonicalConfig {I : Issuance (Dα Γ α Q).toMRDTSig}
    (hG : ∀ e s, I.CanIssue e s → CoreGuard e s)
    {C : Configuration (Dα Γ α Q).toMRDTSig}
    (reach : MintCertifiedReachV (Dα Γ α Q).toMRDTSig
      (canonicalVirtualMergeBase (Dα Γ α Q).toMRDTSig) I C) :
    @CanonicalConfig (Dα Γ α Q).toMRDTSig birthEventOrder C :=
  CertifiedClosedExecution.canonicalConfig_of_mintCertifiedV
    (fun C' hm => closedJoinAt (coordHonest_of_issued (issued_of_mintHonest hG hm))
      (delBorn_of_issued (issued_of_mintHonest hG hm))) reach

/-- **Every stored version holds a causal replay of its event set.** -/
theorem representedVersions {I : Issuance (Dα Γ α Q).toMRDTSig}
    (hG : ∀ e s, I.CanIssue e s → CoreGuard e s)
    {C : Configuration (Dα Γ α Q).toMRDTSig}
    (reach : MintCertifiedReachV (Dα Γ α Q).toMRDTSig
      (canonicalVirtualMergeBase (Dα Γ α Q).toMRDTSig) I C)
    {v : Version} {s : St Γ α} {E : Set (Op (AppOp Γ α))} (hv : C.ver v = some (s, E)) :
    Replay C.replayContext E s := by
  have cfg := canonicalConfig hG reach
  have hi := issued_of_mintHonest hG reach.mintHonest
  exact replay_of_canonical (coordHonest_of_issued hi) (delBorn_of_issued hi)
    ⟨fun hab hbc => cfg.vis_trans hab hbc, cfg.vis_irrefl⟩
    (cfg.version_events_supported v s E hv) (cfg.canonical v s E hv)

/-! ## The sequential specification

The row's own sequential semantics, over the event alphabet: splice the
record in coordinate order, delete by identity. This is the identity
abstraction of Section 6, which several rows here use, and it makes the
sequential premise `EventSequentialSimulation.sound`. -/

def specMachine (Γ : Scheme) (α : Type) (Q : QueryOf Γ α) :
    DeterministicSpec (Op (AppOp Γ α)) Q.QType Q.VType where
  State := St Γ α
  initial := []
  update := step
  query := Q.read

def historySpec (Γ : Scheme) (α : Type) (Q : QueryOf Γ α) :
    HistorySpec (Op (AppOp Γ α)) Q.QType Q.VType := (specMachine Γ α Q).toSpec

def abstraction : EventSequentialSimulation (Dα Γ α Q).toMRDTSig (specMachine Γ α Q) where
  Rel := Eq
  initial := rfl
  update := fun s a h e => by rw [h]; rfl
  observes := fun s a h q => by rw [h]; rfl

theorem foldSound : EventFoldHistorySound (Dα Γ α Q).toMRDTSig (historySpec Γ α Q) :=
  abstraction.sound

/-! ## RA-linearizability -/

/-- **The invariant is closed along every certified execution.** -/
theorem closedInvariant {I : Issuance (Dα Γ α Q).toMRDTSig}
    (hG : ∀ e s, I.CanIssue e s → CoreGuard e s)
    {C : Configuration (Dα Γ α Q).toMRDTSig}
    (reach : MintCertifiedReachV (Dα Γ α Q).toMRDTSig
      (canonicalVirtualMergeBase (Dα Γ α Q).toMRDTSig) I C) :
    InvariantOrder.Closed (Dα Γ α Q).toMRDTSig C.replayContext (Valid C.replayContext) :=
  closed C.replayContext
    (coordHonest_of_issued (issued_of_mintHonest hG reach.mintHonest))

/-- **RA-linearizability, at the invariant-scoped reading.**

Every version a certified execution stores is explained by one history of
its own event set that respects the invariant-scoped order and
specification visibility at once, and that the sequential specification
admits with the implementation's own answer.

`Negative.lean` proves this row cannot reach the unscoped criterion through
any `rc`, so the invariant reading is not a convenience here but the only
route. -/
theorem raLinearizable {I : Issuance (Dα Γ α Q).toMRDTSig}
    (hG : ∀ e s, I.CanIssue e s → CoreGuard e s)
    {C : Configuration (Dα Γ α Q).toMRDTSig}
    (reach : MintCertifiedReachV (Dα Γ α Q).toMRDTSig
      (canonicalVirtualMergeBase (Dα Γ α Q).toMRDTSig) I C) :
    InvariantOrder.VersionsRA (Dα Γ α Q).toMRDTSig (Valid C.replayContext)
      (commutingPolicy (AppOp Γ α)) (historySpec Γ α Q) C := by
  intro v s E hv q
  obtain ⟨hsup, ρ, hpρ, hrρ, hfρ⟩ := representedVersions hG reach hv
  refine ⟨ρ, hpρ, ?_, ?_, ?_⟩
  · refine hrρ.imp (fun {a b} hno hedge => ?_)
    rcases hedge with ⟨hvis, -⟩ | ⟨-, -, hpol, -⟩
    · exact hno hvis
    · exact hpol
  · exact hrρ.imp (fun {a b} hno hedge => hno hedge.1)
  · rw [← hfρ]
    exact foldSound ρ q

#print axioms raLinearizable

end LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA
