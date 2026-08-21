import Sal.ConditionedMRDTs.MRDT_Instances.ConsolidatedConditioningCanaries
import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Embed.PeritextEmbed_MarksGC
import Sal.ConditionedMRDTs.Metatheory.Distributed_GC

/-!
# One-sided EmbedRGA Peritext flagship certificate

This module gives the one-sided `PeritextEmbedRGA` design one public endpoint.
It does not certify the JavaScript default `PeritextSidedEmbedRGA`; see
`Development/SIDED_PERITEXT_FLAGSHIP_AUDIT.md`. It keeps distributed
correctness, local sequential intent, commit-history GC, and datatype-state GC
as separate fields so no theorem silently changes another theorem's scope.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode)
open PeritextEmbed
open PeritextEmbed.MarksGC
open PeritextEmbed.MarkDoc

/-- A factored catalogue entry: payload trace safety uses the pinned-root
semantic prune, while the compression facts apply to the separately supplied
`Keep`. This type does not identify the two carriers. -/
def CommitHistoryGCSafe (D : ConditionedMRDTSig) : Prop :=
  ∀ (C₀ : Configuration D) (hStore : StoreInv C₀.ver C₀.parents)
      (Keep : Set Version),
    PayloadTraceSafe C₀ hStore ∧
    (∀ a ∈ Keep, ∀ b ∈ Keep,
      CompressedReaches C₀.parents Keep a b ↔ Reaches C₀.parents a b) ∧
    (∀ v₁ ∈ Keep, ∀ v₂ ∈ Keep, ∀ vT ∈ Keep,
      IsLCARel (CompressedReaches C₀.parents Keep) v₁ v₂ vT ↔
        IsLCARetained C₀.parents Keep v₁ v₂ vT)

/-- Asynchronous local commit collection behaviorally refines an execution
that never collects. This property is datatype-parametric. -/
def DistributedCommitGCSafe : Prop :=
  ∀ (parents : Version → List Version) {F₀ C₀ C₁ : DistributedWorld},
    WorldSim F₀ C₀ → DistributedSteps parents C₀ C₁ →
      ∃ F₁, NoGCSteps F₀ F₁ ∧ WorldSim F₁ C₁

/-- Peritext state compaction preserves rendered formatting through one epoch
and every legal continuation. The hypotheses expose retention roots,
settled-dead removal, stable-prefix recoding, and Lamport continuation
discipline explicitly. -/
def PeritextStateGCSafe (Γ : OrderedPrefixCode) : Prop :=
  ∀ (F : StablePrefixMap Γ) (s : EState ℕ) (τ : List (Op (EOp ℕ)))
      (kp : ℕ → Bool) (del : List ℕ) (marks : List MarkD) (mt : MType),
    ESorted s → (eIds s).Nodup → ContOK Γ s τ →
    (∀ o ∈ τ, ∀ (e : ℕ) (π : List Bool) (a : ℕ),
      o.2.2 = EOp.ins e π a → kp o.1 = true) →
    (∀ x ∈ s.filter (fun r => kp r.1), F.Dom x.2.2) →
    (∀ o ∈ τ, ∀ (e : ℕ) (π : List Bool) (a : ℕ),
      o.2.2 = EOp.ins e π a → F.MintAt π (o.1 - a)) →
    (∀ r ∈ s, kp r.1 = false → del.contains r.1 = true) →
    (∀ m ∈ marks, kp m.start_id = true ∧ kp m.end_id = true) →
    renderMarksDoc
      (DocD.mk (applySeq (E Γ ℕ).toCRDTSig
        (eRemapSt F.f (s.filter (fun r => kp r.1)))
        (τ.map (eRemapOp F.f))) del) marks mt =
      renderMarksDoc (DocD.mk (applySeq (E Γ ℕ).toCRDTSig s τ) del) marks mt

/-- One public result for one-sided EmbedRGA Peritext spanning the corrected
Neem replacement and both GC
layers. The sequential field is intentionally local; it does not claim that a
concurrent distributed history has one global sequential enumeration. -/
structure PeritextFlagshipCertificate (Γ : OrderedPrefixCode) : Prop where
  distributed : ∀ {C : Configuration
      (E Γ Sal.ConditionedMRDTs.Peritext.PeritextElt)},
    MintCertifiedReach3
      (E Γ Sal.ConditionedMRDTs.Peritext.PeritextElt)
      (embedGeneration Γ) (embedVerified Γ).initInv C →
    IsRALinearizable3 C ∧
      VersionsSafe (SafetyCertificate.trivial (embedGeneration Γ)) C
  distributedV : ∀ {C : Configuration
      (E Γ Sal.ConditionedMRDTs.Peritext.PeritextElt)},
    MintCertifiedReach3V
      (E Γ Sal.ConditionedMRDTs.Peritext.PeritextElt)
      (embedGeneration Γ) (embedVerified Γ).initInv C → IsRALinearizable3 C
  sequential : ∀ {ops : List
      (Op (EOp Sal.ConditionedMRDTs.Peritext.PeritextElt))},
    LinearMintHistory
      (E Γ Sal.ConditionedMRDTs.Peritext.PeritextElt) eApplicable ops →
    renderRichText (eFold Γ ops) = editorRender (editorFold ops)
  commitHistoryGC : CommitHistoryGCSafe
    (E Γ Sal.ConditionedMRDTs.Peritext.PeritextElt)
  distributedCommitGC : DistributedCommitGCSafe
  stateGC : PeritextStateGCSafe Γ

/-- The flagship certificate is assembled only from existing public
capstones. No new semantic premise is hidden by the packaging. -/
noncomputable def peritextFlagship (Γ : OrderedPrefixCode) :
    PeritextFlagshipCertificate Γ where
  distributed := by
    intro C h
    exact ⟨(peritextEmbedGenerationVerified Γ).distributedRA h,
      (peritextEmbedGenerationVerified Γ).distributedSafe h⟩
  distributedV := fun h =>
    (peritextEmbedGenerationVerified Γ).distributedRAV h
  sequential := fun h => peritextEmbedRenderedSequential_of_linearMintHistory h
  commitHistoryGC := fun C₀ hStore Keep => gc_safety_compressed C₀ hStore Keep
  distributedCommitGC := fun parents {_ _ _} hSim hRun =>
    distributed_execution_refines_noGC (parents := parents) hSim hRun
  stateGC := fun F s τ kp del marks mt hsort hnd hok hkp hdom hmint hdead hanchor =>
    marksGC_render_congr F s τ kp del marks mt hsort hnd hok hkp hdom hmint hdead hanchor

#print axioms peritextFlagship

end Sal.ConditionedMRDTs
