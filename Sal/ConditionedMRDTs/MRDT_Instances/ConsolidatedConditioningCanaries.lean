import Sal.ConditionedMRDTs.Metatheory.ConditioningIntentAudit
import Sal.ConditionedMRDTs.MRDT_Instances.ProductionGenerationContracts
import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Embed.PeritextEmbed_SeqSpec

/-!
# Consolidated conditioning canaries

This module tests the Priority-7A candidate boundary without replacing the
existing API. A certificate keeps four concerns explicit:

* the corrected Join/RA and independent sequential package;
* the issuer generation contract and its configuration-history bridge;
* client safety; and
* the bridge from a guarded, clocked sequential client history to the exact
  history premise consumed by the sequential theorem.

The algebra certificate deliberately omits `Inv` and `applicable`: the audited
production Join proofs do not consume either field. `OperationalConditioning`
retains the initial-state witness required by the current legacy
`Configuration` representation. `toUnified` is a lossless compatibility
adapter. The canaries therefore test API organization, not a weaker theorem.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode)

/-- The paper-facing algebra and intent certificate. Its fields state Join
correctness and sequential refinement directly; no state invariant or
generation-time applicability predicate appears in this layer. -/
structure AlgebraVerifiedMRDT (D : ConditionedMRDTSig) where
  Honest : Sal.Emulation.Configuration D.toCRDTSig → Prop
  join : ∀ C, Honest C → JoinKitAt D (plainDoctrine D) C
  Spec : SequentialSpec (Op D.AppOp)
  seq : HistorySequentialRefinement D Spec

/-- Compatibility evidence required only because the existing configuration
type stores `D.Inv` proofs. It is not a premise of the algebraic Join field.
Future flat operational semantics can remove this adapter. -/
structure OperationalConditioning (D : ConditionedMRDTSig) where
  initInv : D.Inv D.init

namespace AlgebraVerifiedMRDT

def ofVerified {D : ConditionedMRDTSig} (V : VerifiedMRDT D) :
    AlgebraVerifiedMRDT D where
  Honest := V.Honest
  join := V.join
  Spec := V.Spec
  seq := V.seq

def toVerified {D : ConditionedMRDTSig} (A : AlgebraVerifiedMRDT D)
    (O : OperationalConditioning D) : VerifiedMRDT D where
  Honest := A.Honest
  initInv := O.initInv
  join := A.join
  Spec := A.Spec
  seq := A.seq

end AlgebraVerifiedMRDT

/-- Candidate paper-facing certificate. Distributed correctness and local
sequential intent remain distinct conclusions because a concurrent execution
does not in general admit one globally applicable sequential history. -/
structure GenerationVerifiedMRDT (D : ConditionedMRDTSig) where
  algebra : AlgebraVerifiedMRDT D
  operational : OperationalConditioning D
  generation : GenerationContract D
  history_entails_honest : ∀ C, generation.History C →
    algebra.Honest (Configuration.core C)
  safety : SafetyCertificate D generation
  sequential_of_mint : ∀ ops,
    LinearMintHistory D generation.Guard ops → algebra.seq.Honest ops

namespace GenerationVerifiedMRDT

variable {D : ConditionedMRDTSig} (V : GenerationVerifiedMRDT D)

/-- Lossless reconstruction of the established package. Signature-level
conditioning is confined to this compatibility boundary. -/
def verified : VerifiedMRDT D := V.algebra.toVerified V.operational

/-- The candidate package preserves the established unified certificate
definitionally; no correctness assumption is dropped. -/
def toUnified : UnifiedVerifiedMRDT D where
  verified := V.verified
  generation := V.generation
  history_entails_honest := V.history_entails_honest
  safety := V.safety

theorem distributedRA {C : Configuration D}
    (h : MintCertifiedReach3 D V.generation V.verified.initInv C) :
    IsRALinearizable3 C :=
  V.toUnified.ra_linearizable h

theorem distributedRAV {C : Configuration D}
    (h : MintCertifiedReach3V D V.generation V.verified.initInv C) :
    IsRALinearizable3 C :=
  V.toUnified.ra_linearizableV h

theorem distributedSafe {C : Configuration D}
    (h : MintCertifiedReach3 D V.generation V.verified.initInv C) :
    VersionsSafe V.safety C :=
  V.toUnified.safe h

/-- Local sequential intent follows from the same public issuer guard plus the
explicit local Lamport-clock discipline. -/
theorem sequential (ops : List (Op D.AppOp))
    (h : LinearMintHistory D V.generation.Guard ops) :
    V.verified.seq.Rel (applySeq D.toCRDTSig D.init ops)
      (V.verified.Spec.run ops) :=
  V.verified.sequential ops (V.sequential_of_mint ops h)

end GenerationVerifiedMRDT

noncomputable def embedGenerationVerified {α : Type}
    [DecidableEq α] [Inhabited α] (Γ : OrderedPrefixCode) :
    GenerationVerifiedMRDT (E Γ α) where
  algebra := AlgebraVerifiedMRDT.ofVerified (embedVerified Γ)
  operational := ⟨(embedVerified Γ).initInv⟩
  generation := embedGeneration Γ
  history_entails_honest := fun _ h => eHonest_core h
  safety := SafetyCertificate.trivial (embedGeneration Γ)
  sequential_of_mint := fun _ h => eSeqOK_of_linearMintHistory h

noncomputable def sidedGenerationVerified (Γ : OrderedPrefixCode) :
    GenerationVerifiedMRDT (S Γ) where
  algebra := AlgebraVerifiedMRDT.ofVerified (sidedVerified Γ)
  operational := ⟨(sidedVerified Γ).initInv⟩
  generation := sidedGeneration Γ
  history_entails_honest := fun _ h => sHonest_core h
  safety := SafetyCertificate.trivial (sidedGeneration Γ)
  sequential_of_mint := fun _ h => sSeqOK_of_linearMintHistory h

noncomputable def peritextEmbedGenerationVerified (Γ : OrderedPrefixCode) :
    GenerationVerifiedMRDT
      (E Γ Sal.ConditionedMRDTs.Peritext.PeritextElt) :=
  embedGenerationVerified Γ

/-- Render-level Peritext intent from the same local guard-and-clock policy,
not merely the payload-level EmbedRGA relation. -/
theorem peritextEmbedRenderedSequential_of_linearMintHistory
    {Γ : OrderedPrefixCode}
    {ops : List (Op (EOp Sal.ConditionedMRDTs.Peritext.PeritextElt))}
    (h : LinearMintHistory
      (E Γ Sal.ConditionedMRDTs.Peritext.PeritextElt) eApplicable ops) :
    PeritextEmbed.renderRichText (eFold Γ ops) =
      PeritextEmbed.editorRender (PeritextEmbed.editorFold ops) :=
  PeritextEmbed.peritextEmbed_seq_sound (eSeqOK_of_linearMintHistory h)

/-- A clocked queue client mints fresh enqueue tags, and `qApplicable` supplies
the exact dequeue-at-head premise consumed by `queue_seq_sound`. -/
theorem qOK_of_linearMintHistory {ops : List (Op QOp)}
    (h : LinearMintHistory Q qApplicable ops) : qOK ops := by
  intro pre e post heq
  constructor
  · intro v hop hmem
    obtain ⟨old, hold, _henq, htime⟩ := qTags_fold_sub pre e.1 hmem
    have hlt := h.clocked pre e post heq old hold
    rw [htime] at hlt
    exact Nat.lt_irrefl _ hlt
  · intro t hop
    have hg := h.guarded pre e post heq
    obtain ⟨v, hv⟩ : ∃ v,
        (applySeq Q.toCRDTSig Q.init pre).head? = some (t, v) := by
      simpa [qApplicable, hop] using hg
    cases hs : applySeq Q.toCRDTSig Q.init pre with
    | nil => simp [hs] at hv
    | cons p rest =>
        have hp : p = (t, v) := by simpa [hs] using hv
        subst p
        exact ⟨v, rest, hs⟩

noncomputable def queueGenerationVerified : GenerationVerifiedMRDT Q where
  algebra := AlgebraVerifiedMRDT.ofVerified queueVerified
  operational := ⟨queueVerified.initInv⟩
  generation := queueGeneration
  history_entails_honest := fun _ h => qHonest_core h
  safety := SafetyCertificate.trivial queueGeneration
  sequential_of_mint := fun _ h => qOK_of_linearMintHistory h

/-- The bounded-counter guard preserves `BCInv` at every sequential prefix.
The clock component is carried uniformly by `LinearMintHistory` but safety
needs only the guard component. -/
theorem BCSequentialHonest_of_linearMintHistory {ops : List (Op BCOp)}
    (h : LinearMintHistory BC bcApplicable ops) : BCSequentialHonest ops := by
  intro pre suf hops
  induction pre using List.reverseRecOn generalizing suf with
  | nil => exact bc_inv_init
  | append_singleton pre e ih =>
      rw [applySeq_append_single]
      apply bcApplicable_inv_pres
      · apply ih (e :: suf)
        simpa [List.append_assoc] using hops
      · apply h.guarded pre e suf
        simpa [List.append_assoc] using hops

noncomputable def boundedCounterGenerationVerified :
    GenerationVerifiedMRDT BC where
  algebra := AlgebraVerifiedMRDT.ofVerified boundedCounterVerified
  operational := ⟨boundedCounterVerified.initInv⟩
  generation := boundedCounterGeneration
  history_entails_honest := fun _ _ => True.intro
  safety := boundedCounterSafety
  sequential_of_mint := fun _ h =>
    BCSequentialHonest_of_linearMintHistory h

-- PASS controls: the adapters recover the established public packages.
example {α : Type} [DecidableEq α] [Inhabited α] (Γ : OrderedPrefixCode) :
    (embedGenerationVerified (α := α) Γ).toUnified.generation.Guard =
      (embedUnified Γ).generation.Guard := rfl

example (Γ : OrderedPrefixCode) :
    (sidedGenerationVerified Γ).toUnified.generation.Guard =
      (sidedUnified Γ).generation.Guard := rfl

-- PASS: splitting and rebuilding does not alter the Join or sequential layers.
example {D : ConditionedMRDTSig} (V : VerifiedMRDT D) :
    (AlgebraVerifiedMRDT.ofVerified V).toVerified ⟨V.initInv⟩ = V := by
  cases V
  rfl

-- FAIL-shaped boundary: algebra alone cannot manufacture the legacy
-- configuration's initial invariant witness. The adapter requires it as a
-- separate argument rather than hiding a proof or default.
example {D : ConditionedMRDTSig} (A : AlgebraVerifiedMRDT D) :
    OperationalConditioning D → VerifiedMRDT D :=
  A.toVerified

#print axioms GenerationVerifiedMRDT.distributedRA
#print axioms GenerationVerifiedMRDT.distributedRAV
#print axioms GenerationVerifiedMRDT.distributedSafe
#print axioms GenerationVerifiedMRDT.sequential
#print axioms embedGenerationVerified
#print axioms sidedGenerationVerified
#print axioms peritextEmbedGenerationVerified
#print axioms peritextEmbedRenderedSequential_of_linearMintHistory
#print axioms qOK_of_linearMintHistory
#print axioms queueGenerationVerified
#print axioms BCSequentialHonest_of_linearMintHistory
#print axioms boundedCounterGenerationVerified
#print axioms AlgebraVerifiedMRDT.ofVerified
#print axioms AlgebraVerifiedMRDT.toVerified

end Sal.ConditionedMRDTs
