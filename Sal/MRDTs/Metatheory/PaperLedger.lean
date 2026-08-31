import Sal.MRDTs.Metatheory.RefactorLedger
import Sal.MRDTs.Metatheory.NegativeLedger

/-!
# Working-paper evidence ledger

This module is the build gate for theorem names used by the two anonymous
working papers in `docs/`.  The papers may explain or abbreviate definitions,
but every machine-checked claim must terminate at one of these declarations or
at the more exhaustive `RefactorLedger` imported above.
-/

namespace Sal.MRDTs

-- Corrected framework and checked failure of the earlier route.
#check Foundation.convergence_over_backward_closed_subsets_false
#check Foundation.binaryLaws_insufficient
#check MRDTSig
#check MRDTSig.merge
#check MRDTSig.historicalBinaryMerge_eq_initialSlice
#check MRDTSig.toUpdateSig_update
#check Foundation.UpdateSig
#check Foundation.HistoricalBinaryMerge
#check Foundation.UpdateSig.historicalMerge
#check MRDTSig.historicalBinaryMerge
#check Configuration
#check Configuration.headState
#check Configuration.headEvents
#check Foundation.ReplayContext
#check Configuration.replayContext
#check Step
#check Step.fork_copies_source
#check Step.fork_head_ne_root
#check StepV
#check Issuance
#check IssuedStep
#check MintCertifiedReach
#check MintCertifiedReachV
#check CanonicalConfig
#check Foundation.loOn
#check Foundation.IsCanonicalState
#check JoinAt
#check Join
#check JoinCoreLaws
#check FeasibleDeltaLaws
#check CanonicalJoinLaws
#check CanonicalJoinLaws.join
#check JoinProof.ofArbitraryStateLaws
#check JoinProof.ofFeasibleStateLaws
#check CausalDeltaLaw
#check replayWitness_of_join
#check replayWitnessV_of_join
#check canonicalVirtualMergeBase
#check virtualMergeBaseState_canonical
#check VerifiedMRDT
#check PackagedMRDT
#check Production.registry
#check VerifiedMRDT.correct
#check VerifiedMRDT.correctV
#check MintCertifiedReach.toV
#check ReplayAdequacyCertificate.sound
#check SafetyCertificate.preservation
#check ReplayAdequateMRDT
#check ReplayAdequateMRDT.sequentially_correct
#check SequentialSpec
#check InteractionSpec
#check interactionLoOn
#check IsSpecLinearizable

-- Countermodels and intentionally incomplete signatures are kept out of the
-- typed production registry and checked by `NegativeLedger`.
#check Foundation.convergence_over_backward_closed_subsets_false
#check Foundation.binaryLaws_insufficient
#check Instances.InteractionSPOT.LWW.old_no_chain_refuted
#check Instances.MVR.concurrentState_no_sequential_register
#check Instances.Queue.ConditioningSPOT.duplicate_dequeue_not_fifo

-- Distributed commit collection and composition with datatype state GC.
#check GC.Local
#check GC.Envelope
#check GC.World
#check GC.StoreSim
#check GC.WorldSim
#check GC.EvidenceComplete
#check GC.EvidenceSPOT.missing_author
#check GC.Certificate
#check GC.Certificate.ofMaximalCommonAncestorClosed
#check GC.compressedReaches_iff
#check GC.root_absent_when_dropped
#check GC.execution_refines_noGC
#check GC.read_preserved
#check GC.NoGCStep
#check GC.RuntimeStep
#check GC.runtime_refines_core
#check GC.runtime_refines_coreV
#check StateGCProtocol
#check StateGCProtocol.refines
#check GC.CombinedStep
#check GC.CombinedSteps.refinesV
#check GC.CombinedSteps.refinesRaw

-- AegisSheet intent semantics, incremental sequential refinement, and GC.
#check Instances.AegisSheet.verified
#check Instances.AegisSheet.spec_linearizable
#check Instances.AegisSheet.spec_linearizableV
#check Instances.AegisSheet.replayAdequate
#check Instances.AegisSheet.Sequential.CausalOriginLegal
#check Instances.AegisSheet.Sequential.canonical_causalOriginLegal
#check Instances.AegisSheet.Sequential.concurrent_origins_causal_legal
#check Instances.AegisSheet.Sequential.unavailable_origin_not_causal_legal
#check Instances.AegisSheet.Sequential.chronological_eq_of_toFinset_eq
#check Instances.AegisSheet.Sequential.inplaceStateRel
#check Instances.AegisSheet.Sequential.concurrent_origins_not_guarded_chronological
#check Instances.AegisSheet.Sequential.materialize_insert
#check Instances.AegisSheet.Sequential.guarded_history_materializes
#check Instances.AegisSheet.Sequential.guarded_history_observes
#check Instances.AegisSheet.Sequential.materializedStateRel
#check Instances.AegisSheet.Sequential.inplaceSequentialSound
#check Instances.AegisSheet.Sequential.Abstraction.token_merged_history_legal
#check Instances.AegisSheet.Sequential.Abstraction.cell_merged_history_legal
#check Instances.AegisSheet.Sequential.Abstraction.range_merged_history_legal
#check Instances.AegisSheet.Sequential.Abstraction.row_tokens_distinguish_future
#check Instances.AegisSheet.Sequential.Abstraction.cell_versions_distinguish_future
#check Instances.AegisSheet.Sequential.Abstraction.range_versions_distinguish_future
#check Instances.AegisSheet.Sequential.Abstraction.no_view_only_step
#check Instances.AegisSheet.sequentially_correct
#check Instances.AegisSheet.observationally_correct
#check Instances.AegisSheet.GC.certificate

-- The three sequence kernels and their intent policies.
#check Instances.RGA.RGAM
#check Instances.RGA.BirthGraveState
#check Instances.RGA.sequence
#check Instances.RGA.birthGraveMachine
#check Instances.RGA.birthGraveRel
#check Instances.RGA.birthGraveSound
#check Instances.RGA.verified
#check Instances.RGA.listSpec
#check Instances.RGA.listRel
#check Instances.RGA.rga_spec_linearizable
#check Instances.RGA.rga_spec_linearizableV
#check Instances.ProductionRGA.replayEmbed
#check Instances.ProductionRGA.replaySided
#check Instances.ProductionRGA.embed
#check Instances.ProductionRGA.sided
#check Instances.ORSet.verified
#check Instances.ORSet.concurrent_remove_add_wins
#check Instances.ORSet.observed_remove_ordinary_spec_absent
#check Instances.ORSet.concurrent_remove_ordinary_spec_add_wins
#check Instances.ORSet.omitted_tag_breaks_ordinary_refinement
#check Instances.SidedEmbedRGA.fugue_forward_ni
#check Instances.SidedEmbedRGA.fugue_not_maximally_noninterleaving_backward
#check Instances.SidedEmbedRGA.fuguemax_forward_ni
#check Instances.SidedEmbedRGA.fuguemax_backward_ni
#check Instances.SidedEmbedRGA.fuguemax_maximally_noninterleaving

-- Peritext semantics, sequential meaning, and state collection.
#check Instances.SidedPeritext.coreHonest_of_mint
#check Instances.SidedPeritext.verified
#check Instances.SidedPeritext.richVerified
#check Instances.SidedPeritext.richReplayAdequate
#check Instances.SidedPeritext.rich_sequentially_correct
#check Instances.SidedPeritext.StateGC.compactInsertOp_exact
#check Instances.SidedPeritext.StateGC.TextPlan.keeps_fresh
#check Instances.SidedPeritext.StateGC.collectText_query_preserved
#check Instances.SidedPeritext.StateGC.trimDeleted_query_preserved
#check Instances.SidedPeritext.StateGC.dropMarkPair_query_preserved
#check Instances.SidedPeritext.StateGC.Interaction.merge_text_after_epoch_translation
#check Instances.SidedPeritext.StateGC.Protocol.Represents
#check Instances.SidedPeritext.StateGC.Protocol.refines

end Sal.MRDTs
