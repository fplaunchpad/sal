import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Sided.PeritextSided_Interaction

/-!
# Sided Peritext production certificate

This is the public composition point.  The algebraic/distributed certificate
and the mark-aware local-state GC theorem remain separate layers, but clients
no longer have to assemble them by hand.
-/

namespace Sal.ConditionedMRDTs.PeritextSided

open Sal.Emulation
open Sal.ConditionedMRDTs
open StateGC
open Interaction

/-- End-to-end certificate for the shipped SidedEmbedRGA Peritext core. -/
structure ProductionCertificate (Γ : Sal.EmbedRGA.OrderedPrefixCode) where
  unified : UnifiedVerifiedMRDT (Core Γ)
  distributed : DistributedCorrectness unified
  stateGC : ∀ {C : Configuration (Core Γ)} {v : Version}
      (s : CompactState) (p : Plan) (gaps : Finset GapEntry),
      ∀ (cert : FrontierAtomicCertificate C v s p gaps),
      ∀ mt : PeritextEmbed.MarkDoc.MType,
        SettledAt C v cert.cut ∧
          renderCompact (collectStableBase s p gaps) mt = renderCompact s mt
  interactionWF : ∀ {S T : CombinedConfig Γ}
      {labels : List (Option (Label3 (Core Γ)))},
      CombinedSteps Γ S labels T → S.WellFormed → T.WellFormed
  interactionRefines : ∀ {S T : CombinedConfig Γ}
      {labels : List (Option (Label3 (Core Γ)))},
      CombinedSteps Γ S labels T →
        Steps (Core Γ) S.semantic.core
          (eraseCombinedLabels labels) T.semantic.core
  interactionQueries : ∀ {S T : CombinedConfig Γ}
      {labels : List (Option (Label3 (Core Γ)))},
      CombinedSteps Γ S labels T → S.WellFormed →
      ∀ {r : Replica} {v : Version},
        v ∈ (T.semantic.stores r).commits →
        ∀ mt : PeritextEmbed.MarkDoc.MType,
        ∃ full E m, T.semantic.core.ver v = some (full, E) ∧
          T.materialized r v = some m ∧
          renderCompact m.state mt = renderCore m.state.sided.gaps full mt
  interactionRefinesV : ∀ {S T : CombinedConfig Γ}
      {labels : List (Option (Label3 (Core Γ)))},
      CombinedStepsV Γ S labels T →
        StepsV (Core Γ) S.semantic.core
          (eraseCombinedLabels labels) T.semantic.core
  interactionQueriesV : ∀ {S T : CombinedConfig Γ}
      {labels : List (Option (Label3 (Core Γ)))},
      CombinedStepsV Γ S labels T → S.WellFormed →
      ∀ {r : Replica} {v : Version},
        v ∈ (T.semantic.stores r).commits →
        ∀ mt : PeritextEmbed.MarkDoc.MType,
        ∃ full E m, T.semantic.core.ver v = some (full, E) ∧
          T.materialized r v = some m ∧
          renderCompact m.state mt = renderCore m.state.sided.gaps full mt
  virtualRepairReady : ∀ {S : CombinedConfig Γ}, S.WellFormed →
      ∀ {src actor other : Replica},
      MCARepairSource S.semantic src →
      (fetchResult S src actor).semantic.WellFormed →
      StepAvailableV (fetchResult S src actor).semantic (.merge actor other) ∧
        ∀ m, InMcasClosure S.semantic.core m →
          ∃ full E mat,
            (fetchResult S src actor).semantic.core.ver m = some (full, E) ∧
            (fetchResult S src actor).materialized actor m = some mat ∧
            StateRelAt Γ mat.knowledge mat.keep full mat.state
  headOnlyVirtualMerge : ∀ {Km : Know} {keep : ℕ → Bool}
      {full : (Core Γ).State} {out : CompactState},
      HeadOnlyMergeCertificate Km keep full out →
        StateRelAt Γ Km keep full out

/-- The production composition. `unified` supplies ordinary/virtual and
distributed correctness plus the independent rich-text sequential machine;
`stateGC` supplies frontier-backed local collection. -/
noncomputable def productionCertificate
    (Γ : Sal.EmbedRGA.OrderedPrefixCode) : ProductionCertificate Γ where
  unified := preGCUnified Γ
  distributed := distributedPreGC Γ
  stateGC := by
    intro C v s p gaps cert mt
    exact frontier_collectStableBase_safe s p gaps cert mt
  interactionWF := fun run hWF => run.wellFormed hWF
  interactionRefines := fun run => combinedSteps_refines_Step3 run
  interactionQueries := by
    intro S T labels run hWF r v hheld mt
    exact combinedTrace_query_eq run hWF hheld mt
  interactionRefinesV := fun run => combinedStepsV_refines_Step3V run
  interactionQueriesV := by
    intro S T labels run hWF r v hheld mt
    exact combinedTraceV_query_eq run hWF hheld mt
  virtualRepairReady := by
    intro S hWF src actor other hsrc hsem
    exact fetchResult_virtualMerge_ready hWF hsrc hsem
  headOnlyVirtualMerge := fun cert => cert.related

theorem production_localRichIntent {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    {ops : List (Op (Core Γ).AppOp)}
    (h : LinearMintHistory (Core Γ) (coreGuard Γ) ops) :
    richStateRel (applySeq (Core Γ).toCRDTSig (Core Γ).init ops)
      ((richSequentialSpec Γ).run ops) :=
  localRichIntent h

#print axioms productionCertificate
#print axioms production_localRichIntent
#print axioms ProductionCertificate.interactionRefines
#print axioms ProductionCertificate.interactionQueries
#print axioms ProductionCertificate.interactionRefinesV
#print axioms ProductionCertificate.interactionQueriesV
#print axioms ProductionCertificate.virtualRepairReady
#print axioms ProductionCertificate.headOnlyVirtualMerge

end Sal.ConditionedMRDTs.PeritextSided
