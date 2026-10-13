import Sal.MRDTs.Paper1.SelfCommutationInstances
import Sal.MRDTs.Paper1.CertifiedRGAInvariantReplay
import Sal.MRDTs.Paper1.CertifiedSidedInvariantReplay
import Sal.MRDTs.Paper1.CertifiedFugueInvariantReplay
import Sal.MRDTs.Paper1.CertifiedRGAProducts
import Sal.MRDTs.Paper1.AnchoredQueue

namespace Sal.MRDTs.Paper1.SelfCommutationInstances
open Foundation Sal.EmbedRGA
open SplitPolicy

/-- Any guarded raw theorem restricts to every represented ready prefix. -/
theorem certified_of_guarded {D : UpdateSig} (h : SplitPolicy.EqualOperationCommutes D)
    (S : CertifiedReplay.Scope D) : Certified.SelfCommutes S := by
  intro a b _ _ distinct replica _ _ same H s _ _ _
  exact h a b distinct replica same s

/-- The unrestricted commuting families and ordinary OR-set apply to every scope. -/
theorem certified_of_unrestricted {D : UpdateSig} (h : Unrestricted D)
    (S : CertifiedReplay.Scope D) : Certified.SelfCommutes S :=
  certified_of_guarded (guarded_of_unrestricted h) S

/-- Efficient OR-set needs replica separation, already supplied by the scoped predicate. -/
theorem efficient_certified {A : Type} [DecidableEq A]
    (S : CertifiedReplay.Scope (Instances.EfficientORSet.D A).toUpdateSig) : Certified.SelfCommutes S :=
  certified_of_guarded efficient_guarded S

/-- A represented-prefix diamond with empty policy proves scoped self-commutation.
It does not prove arbitrary-state commutation. -/
theorem certified_empty {D : UpdateSig} {S : CertifiedReplay.Scope D}
    (L : CertifiedReplay.Laws S (commutingPolicy D.AppOp)) : Certified.SelfCommutes S := by
  intro a b _ _ _ _ notab notba _ H s rep readyA readyB
  apply L.diamond H s a b rep readyA readyB notab notba
  · simp [paperOrder, commutingPolicy, notab]
  · simp [paperOrder, commutingPolicy, notba]

theorem invariant_empty {D : UpdateSig} {S : CertifiedReplay.Scope D} {Inv : D.State → Prop}
    (L : InvariantReplay.Laws S Inv (commutingPolicy D.AppOp)) : Certified.SelfCommutes S := by
  intro a b _ _ _ _ notab notba _ H s rep readyA readyB
  apply L.diamond H s a b rep readyA readyB notab notba
  · simp [InvariantOrder.order, commutingPolicy, notab]
  · simp [InvariantOrder.order, commutingPolicy, notba]

/-- The roster's MVR is the compact live implementation. -/
theorem mvr_certified {C : Configuration Instances.MVRLive.D}
    (execution : CertifiedExecution Instances.MVRLive.D Instances.MVRLive.issuance C)
    (E : Set Instances.MVRLive.Event) (supported : E ⊆ C.events) :
    Certified.SelfCommutes (CertifiedQueueMVR.MVR.scopeC C E) :=
  certified_empty (CertifiedQueueMVR.MVR.scope_laws execution E supported)

section Embedded
variable {A : Type} [DecidableEq A] [Inhabited A]
theorem embedded_certified (Γ : OrderedPrefixCode) {C : Configuration (Instances.EmbedRGA.E Γ A)}
    (execution : CertifiedExecution (Instances.EmbedRGA.E Γ A) (Instances.EmbedRGA.generation Γ) C)
    {v s H} (stored : C.ver v = some (s,H)) :
    Certified.SelfCommutes (CertifiedRGAInvariantReplay.scope Γ C H) :=
  invariant_empty (CertifiedRGAInvariantReplay.laws Γ execution stored).replay
end Embedded

/-- Peritext's fused element payload instantiates the same embedded effector. -/
abbrev peritext_certified := @embedded_certified Instances.Peritext.Element inferInstance inferInstance

theorem sided_certified (Γ : OrderedPrefixCode) {C : Configuration (Instances.SidedEmbedRGA.S Γ)}
    (execution : CertifiedExecution (Instances.SidedEmbedRGA.S Γ) (Instances.SidedEmbedRGA.generation Γ) C)
    {v s H} (stored : C.ver v = some (s,H)) :
    Certified.SelfCommutes (CertifiedSidedInvariantReplay.scope Γ C H) :=
  invariant_empty (CertifiedSidedInvariantReplay.laws Γ execution stored).replay

/-- Honesty is explicit; the represented prefix scope is the existing one. -/
theorem core_certified (Γ : OrderedPrefixCode)
    (C : ReplayContext (Instances.SidedPeritext.Core Γ).toUpdateSig)
    (honest : Instances.SidedEmbedRGA.SHonestCore Γ (projReplayContext₁ C))
    (domain : ∀ a b, C.vis a b → a ∈ C.events) :
    Certified.SelfCommutes (CertifiedPrefixScope.scope (Instances.SidedPeritext.Core Γ) C) :=
  certified_empty (CertifiedRGAProducts.SidedPeritext.laws Γ C honest domain _)

theorem rich_certified (Γ : OrderedPrefixCode)
    (C : ReplayContext (Instances.SidedPeritext.RichCore Γ).toUpdateSig)
    (honest : Instances.SidedEmbedRGA.SHonestCore Γ (projReplayContext₁ C))
    (domain : ∀ a b, C.vis a b → a ∈ C.events) :
    Certified.SelfCommutes (CertifiedPrefixScope.scope (Instances.SidedPeritext.RichCore Γ) C) :=
  certified_empty (CertifiedRGAProducts.SidedPeritext.rich_laws Γ C honest domain _)

theorem anchored_queue_certified {C : Configuration AnchoredQueue.Q}
    (execution : CertifiedExecution AnchoredQueue.Q AnchoredQueue.issuance C)
    {v s H} (stored : C.ver v = some (s,H)) :
    Certified.SelfCommutes (CertifiedRGAInvariantReplay.scope unaryCode C H) :=
  invariant_empty (AnchoredQueue.scoped_laws execution stored).replay

/-- This scoped algebraic consequence makes no RA-linearizability claim. -/
theorem fugue_certified (Γ : OrderedPrefixCode)
    {C : Configuration (Instances.SidedEmbedRGA.FugueMax.datatype Γ)}
    (execution : CertifiedExecution (Instances.SidedEmbedRGA.FugueMax.datatype Γ) (Instances.SidedEmbedRGA.FugueMax.generation Γ) C)
    {v s H} (stored : C.ver v = some (s,H)) :
    Certified.SelfCommutes (CertifiedFugueInvariantReplay.scope Γ C H) :=
  invariant_empty (CertifiedFugueInvariantReplay.laws Γ execution stored).replay

/-- Stronger variants retain each production policy's entire invariant domain. -/
theorem embedded_invariant (Γ : OrderedPrefixCode) {A : Type} [DecidableEq A] [Inhabited A]
    {C : Configuration (Instances.EmbedRGA.E Γ A)}
    (execution : CertifiedExecution (Instances.EmbedRGA.E Γ A) (Instances.EmbedRGA.generation Γ) C)
    {v s H} (stored : C.ver v = some (s,H)) :
    Invariant.SelfCommutes (CertifiedRGAInvariantReplay.scope Γ C H)
      (CertifiedRGAInvariant.Valid Γ C.replayContext) :=
  Invariant.existing_self_commutation (CertifiedRGAInvariantReplay.laws Γ execution stored).policy

abbrev peritext_invariant (Γ : OrderedPrefixCode) :=
  @embedded_invariant Γ Instances.Peritext.Element inferInstance inferInstance

theorem sided_invariant (Γ : OrderedPrefixCode) {C : Configuration (Instances.SidedEmbedRGA.S Γ)}
    (execution : CertifiedExecution (Instances.SidedEmbedRGA.S Γ) (Instances.SidedEmbedRGA.generation Γ) C)
    {v s H} (stored : C.ver v = some (s,H)) :
    Invariant.SelfCommutes (CertifiedSidedInvariantReplay.scope Γ C H)
      (CertifiedSidedInvariant.Valid Γ C.replayContext) :=
  Invariant.existing_self_commutation (CertifiedSidedInvariantReplay.laws Γ execution stored).policy

theorem anchored_queue_invariant {C : Configuration AnchoredQueue.Q}
    (execution : CertifiedExecution AnchoredQueue.Q AnchoredQueue.issuance C)
    {v s H} (stored : C.ver v = some (s,H)) :
    Invariant.SelfCommutes (CertifiedRGAInvariantReplay.scope unaryCode C H) (AnchoredQueue.Valid C) :=
  Invariant.existing_self_commutation (AnchoredQueue.scoped_laws execution stored).policy

theorem fugue_invariant (Γ : OrderedPrefixCode)
    {C : Configuration (Instances.SidedEmbedRGA.FugueMax.datatype Γ)}
    (execution : CertifiedExecution (Instances.SidedEmbedRGA.FugueMax.datatype Γ)
      (Instances.SidedEmbedRGA.FugueMax.generation Γ) C)
    {v s H} (stored : C.ver v = some (s,H)) :
    Invariant.SelfCommutes (CertifiedFugueInvariantReplay.scope Γ C H)
      (CertifiedFugueInvariant.Valid Γ C.replayContext) :=
  Invariant.existing_self_commutation (CertifiedFugueInvariantReplay.laws Γ execution stored).policy

#print axioms certified_of_unrestricted
#print axioms efficient_certified
#print axioms mvr_certified
#print axioms embedded_certified
#print axioms sided_certified
#print axioms core_certified
#print axioms rich_certified
#print axioms anchored_queue_certified
#print axioms fugue_certified
#print axioms embedded_invariant
#print axioms sided_invariant
#print axioms anchored_queue_invariant
#print axioms fugue_invariant
/-- The existing replay diamond and combined policy adapt as a split certificate. -/
theorem mvr_split {C : Configuration Instances.MVRLive.D}
    (execution : CertifiedExecution Instances.MVRLive.D Instances.MVRLive.issuance C)
    (E : Set Instances.MVRLive.Event) (supported : E ⊆ C.events) :
    Certified.RestrictedLaws (CertifiedQueueMVR.MVR.scopeC C E)
      (commutingPolicy Instances.MVRLive.D.AppOp) :=
  Certified.RestrictedLaws.ofExisting
    (CertifiedReplay.restrictedEmpty _ (CertifiedQueueMVR.MVR.scope_laws execution E supported))

section EmbeddedSplit
variable {A : Type} [DecidableEq A] [Inhabited A]
theorem embedded_split (Γ : OrderedPrefixCode) {C : Configuration (Instances.EmbedRGA.E Γ A)}
    (execution : CertifiedExecution (Instances.EmbedRGA.E Γ A) (Instances.EmbedRGA.generation Γ) C)
    {v s H} (stored : C.ver v = some (s,H)) :
    Invariant.RestrictedLaws (CertifiedRGAInvariantReplay.scope Γ C H)
      (CertifiedRGAInvariant.Valid Γ C.replayContext)
      (commutingPolicy (Instances.EmbedRGA.E Γ A).AppOp) :=
  Invariant.RestrictedLaws.ofExisting (CertifiedRGAInvariantReplay.laws Γ execution stored)
end EmbeddedSplit

abbrev peritext_split := @embedded_split Instances.Peritext.Element inferInstance inferInstance

theorem sided_split (Γ : OrderedPrefixCode) {C : Configuration (Instances.SidedEmbedRGA.S Γ)}
    (execution : CertifiedExecution (Instances.SidedEmbedRGA.S Γ) (Instances.SidedEmbedRGA.generation Γ) C)
    {v s H} (stored : C.ver v = some (s,H)) :
    Invariant.RestrictedLaws (CertifiedSidedInvariantReplay.scope Γ C H)
      (CertifiedSidedInvariant.Valid Γ C.replayContext)
      (commutingPolicy (Instances.SidedEmbedRGA.S Γ).AppOp) :=
  Invariant.RestrictedLaws.ofExisting (CertifiedSidedInvariantReplay.laws Γ execution stored)

theorem core_split (Γ : OrderedPrefixCode)
    (C : ReplayContext (Instances.SidedPeritext.Core Γ).toUpdateSig)
    (honest : Instances.SidedEmbedRGA.SHonestCore Γ (projReplayContext₁ C))
    (domain : ∀ a b, C.vis a b → a ∈ C.events) :
    Certified.RestrictedLaws (CertifiedPrefixScope.scope (Instances.SidedPeritext.Core Γ) C)
      (commutingPolicy (Instances.SidedPeritext.Core Γ).AppOp) :=
  Certified.RestrictedLaws.ofExisting
    (CertifiedReplay.restrictedEmpty _ (CertifiedRGAProducts.SidedPeritext.laws Γ C honest domain _))

theorem rich_split (Γ : OrderedPrefixCode)
    (C : ReplayContext (Instances.SidedPeritext.RichCore Γ).toUpdateSig)
    (honest : Instances.SidedEmbedRGA.SHonestCore Γ (projReplayContext₁ C))
    (domain : ∀ a b, C.vis a b → a ∈ C.events) :
    Certified.RestrictedLaws (CertifiedPrefixScope.scope (Instances.SidedPeritext.RichCore Γ) C)
      (commutingPolicy (Instances.SidedPeritext.RichCore Γ).AppOp) :=
  Certified.RestrictedLaws.ofExisting
    (CertifiedReplay.restrictedEmpty _ (CertifiedRGAProducts.SidedPeritext.rich_laws Γ C honest domain _))

theorem anchored_queue_split {C : Configuration AnchoredQueue.Q}
    (execution : CertifiedExecution AnchoredQueue.Q AnchoredQueue.issuance C)
    {v s H} (stored : C.ver v = some (s,H)) :
    Invariant.RestrictedLaws (CertifiedRGAInvariantReplay.scope unaryCode C H)
      (AnchoredQueue.Valid C) (commutingPolicy AnchoredQueue.Q.AppOp) :=
  Invariant.RestrictedLaws.ofExisting (AnchoredQueue.scoped_laws execution stored)

/-- FugueMax's split algebraic certificate retains the existing invariant.
This statement does not claim its sequential criterion or RA-linearizability. -/
theorem fugue_split (Γ : OrderedPrefixCode)
    {C : Configuration (Instances.SidedEmbedRGA.FugueMax.datatype Γ)}
    (execution : CertifiedExecution (Instances.SidedEmbedRGA.FugueMax.datatype Γ)
      (Instances.SidedEmbedRGA.FugueMax.generation Γ) C)
    {v s H} (stored : C.ver v = some (s,H)) :
    Invariant.RestrictedLaws (CertifiedFugueInvariantReplay.scope Γ C H)
      (CertifiedFugueInvariant.Valid Γ C.replayContext)
      (commutingPolicy (Instances.SidedEmbedRGA.FugueMax.datatype Γ).AppOp) :=
  Invariant.RestrictedLaws.ofExisting (CertifiedFugueInvariantReplay.laws Γ execution stored)

end Sal.MRDTs.Paper1.SelfCommutationInstances
