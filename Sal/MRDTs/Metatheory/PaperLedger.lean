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
#check GenerationContract
#check GuardedStep
#check MintCertifiedReach
#check MintCertifiedReachV
#check GoodConfig3
#check JoinLemma3At
#check JoinLemma3
#check JoinLemma3F
#check ra_linearizable3_of_join
#check ra_linearizable3V_of_join
#check canonicalVirtualLCA
#check virtualLCAState_canonical
#check VerifiedMRDT
#check VerifiedMRDT.converges
#check VerifiedMRDT.convergesV
#check VerifiedMRDT.sequentially_correct

-- Distributed commit collection and composition with datatype state GC.
#check GC.Local
#check GC.Envelope
#check GC.EvidenceComplete
#check GC.Certificate
#check GC.Certificate.ofMCAClosed
#check GC.compressedReaches_iff
#check GC.root_absent_when_dropped
#check GC.execution_refines_noGC
#check GC.read_preserved
#check GC.runtime_refines_core
#check GC.runtime_refines_coreV
#check StateGCProtocol.refines
#check GC.CombinedSteps.refinesV
#check GC.CombinedSteps.refinesRaw

-- The three sequence kernels and their intent policies.
#check Instances.RGA.RGAM
#check Instances.RGA.sequence
#check Instances.RGA.spec
#check Instances.RGA.verified
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
#check Instances.SidedPeritext.richVerified
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
