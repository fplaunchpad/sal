import Sal.MRDTs.Metatheory.RefactorLedger
import Sal.MRDTs.Metatheory.Join.Convergence_CounterModel
import Sal.MRDTs.Metatheory.Join.Assoc_CounterModel

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
#check Foundation.coreVCs_lattice_insufficient
#check MRDTSig
#check Configuration
#check Step
#check StepV
#check Issuance
#check IssuedStep
#check MintCertifiedReach
#check MintCertifiedReachV
#check GoodConfig3
#check Foundation.loOn
#check Foundation.IsCanonicalState
#check JoinLemma3At
#check JoinLemma3
#check JoinLemma3F
#check CoreVCs3CD
#check FeasibleDeltaVCs3
#check CDVC3
#check join_lemma3_of_cd_feasible
#check ra_linearizable3_of_join
#check ra_linearizable3V_of_join
#check canonicalVirtualLCA
#check virtualLCAState_canonical
#check VerifiedMRDT
#check VerifiedMRDT.converges
#check VerifiedMRDT.convergesV
#check MintCertifiedReach.toV
#check ConvergenceCertificate.sound
#check SafetyCertificate.preservation
#check ReplayVerifiedMRDT
#check ReplayVerifiedMRDT.sequentially_correct
#check SequentialSpec
#check ArbitrationSpec
#check IsSpecRALinearizable

-- Distributed commit collection and composition with datatype state GC.
#check GC.Local
#check GC.Envelope
#check GC.World
#check GC.StoreSim
#check GC.WorldSim
#check GC.EvidenceComplete
#check GC.EvidenceSPOT.missing_author
#check GC.Certificate
#check GC.Certificate.ofMCAClosed
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
#check Instances.AegisSheet.replayVerified
#check Instances.AegisSheet.Sequential.chronological_eq_of_toFinset_eq
#check Instances.AegisSheet.Sequential.inplaceStateRel
#check Instances.AegisSheet.Sequential.concurrent_origins_not_guarded_chronological
#check Instances.AegisSheet.Sequential.materialize_insert
#check Instances.AegisSheet.Sequential.guarded_history_materializes
#check Instances.AegisSheet.Sequential.guarded_history_observes
#check Instances.AegisSheet.Sequential.materializedStateRel
#check Instances.AegisSheet.Sequential.inplaceSequentialSound
#check Instances.AegisSheet.sequentially_correct
#check Instances.AegisSheet.observationally_correct
#check Instances.AegisSheet.GC.certificate

-- The three sequence kernels and their intent policies.
#check Instances.RGA.RGAM
#check Instances.RGA.RGASeqState
#check Instances.RGA.sequence
#check Instances.RGA.spec
#check Instances.RGA.stateRel
#check Instances.RGA.sequentialSound
#check Instances.RGA.verified
#check Instances.RGA.replayVerified
#check Instances.RGA.listSpec
#check Instances.RGA.listRel
#check Instances.RGA.rga_spec_linearizable
#check Instances.RGA.rga_spec_linearizableV
#check Instances.ProductionRGA.replayEmbed
#check Instances.ProductionRGA.replaySided
#check Instances.ProductionRGA.embed
#check Instances.ProductionRGA.sided
#check Instances.SidedEmbedRGA.fugue_forward_ni
#check Instances.SidedEmbedRGA.fugue_not_maximally_noninterleaving_backward
#check Instances.SidedEmbedRGA.fuguemax_forward_ni
#check Instances.SidedEmbedRGA.fuguemax_backward_ni
#check Instances.SidedEmbedRGA.fuguemax_maximally_noninterleaving
#check Instances.SidedEmbedRGA.fuguemax_ra_linearizable

-- Peritext semantics, sequential meaning, and state collection.
#check Instances.SidedPeritext.coreHonest_of_mint
#check Instances.SidedPeritext.verified
#check Instances.SidedPeritext.richVerified
#check Instances.SidedPeritext.richReplayVerified
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
