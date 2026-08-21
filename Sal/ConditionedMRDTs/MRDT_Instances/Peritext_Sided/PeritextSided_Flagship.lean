import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Sided.PeritextSided_SeqSpec
import Sal.ConditionedMRDTs.Metatheory.Distributed_GC_Refinement

/-!
# Sided Peritext: pre-state-GC flagship certificate

This packages the shipped architecture's algebra, generation discipline,
independent rich-text sequential machine, and distributed operational theorem.
The safety component is intentionally neutral: mark-aware per-state GC remains
the final nontrivial safety certificate before this can replace the paper's
one-sided Peritext flagship.
-/

namespace Sal.ConditionedMRDTs.PeritextSided

open Sal.Emulation
open Sal.ConditionedMRDTs

def richHistoryRefinement (Γ : Sal.EmbedRGA.OrderedPrefixCode) :
    HistorySequentialRefinement (Core Γ) (richSequentialSpec Γ) where
  Honest := LinearMintHistory (Core Γ) (coreGuard Γ)
  Rel := richStateRel
  init := by
    change richStateRel (([] : SState),
      ((∅ : OSState ℕ), (∅ : OSState PeritextEmbed.MarkDoc.MarkD)))
      ⟨[(0, 0)], ∅, ∅⟩
    simp [richStateRel, osPayloads]
  sound := fun _ h => richSequentialSound h

noncomputable def coreVerified (Γ : Sal.EmbedRGA.OrderedPrefixCode) :
    VerifiedMRDT (Core Γ) where
  Honest := CoreHonest Γ
  initInv := by
    change True ∧ True ∧ True
    exact ⟨trivial, trivial, trivial⟩
  join := fun C h => (joinKitAt_plain_iff (Core Γ) C).2 (core_join_at h)
  Spec := richSequentialSpec Γ
  seq := richHistoryRefinement Γ

/-- All non-GC obligations for the runtime-shaped sided architecture in one
public certificate.  `SafetyCertificate.trivial` is visible here rather than
being mistaken for the pending mark-aware state-GC result. -/
noncomputable def preGCUnified (Γ : Sal.EmbedRGA.OrderedPrefixCode) :
    UnifiedVerifiedMRDT (Core Γ) where
  verified := coreVerified Γ
  generation := coreGeneration Γ
  history_entails_honest := fun _ h => h
  safety := SafetyCertificate.trivial (coreGeneration Γ)

theorem distributedPreGC (Γ : Sal.EmbedRGA.OrderedPrefixCode) :
    DistributedCorrectness (preGCUnified Γ) :=
  (preGCUnified Γ).distributedCorrectness

theorem localRichIntent {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    {ops : List (Op (Core Γ).AppOp)}
    (h : LinearMintHistory (Core Γ) (coreGuard Γ) ops) :
    richStateRel (applySeq (Core Γ).toCRDTSig (Core Γ).init ops)
      ((richSequentialSpec Γ).run ops) :=
  (preGCUnified Γ).verified.sequential ops h

#print axioms coreVerified
#print axioms preGCUnified
#print axioms distributedPreGC
#print axioms localRichIntent

end Sal.ConditionedMRDTs.PeritextSided
