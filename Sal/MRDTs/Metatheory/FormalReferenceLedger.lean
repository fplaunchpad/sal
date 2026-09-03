import Sal.MRDTs.Metatheory.RefactorLedger
import Sal.MRDTs.Metatheory.NegativeLedger
import Sal.MRDTs.Metatheory.StateGCCoverage

/-!
# Formal Semantics and Theorem Reference ledger

Build gate for the bottom-up typeset reference under docs/formal-reference.
The document expands these declarations in semantic dependency order; this
file ensures every principal anchor still elaborates.
-/

namespace Sal.MRDTs

-- Public datatype interface, then the internal replay support it projects to.
#check MRDTSig
#check Foundation.Replica
#check Foundation.Timestamp
#check Foundation.Op
#check Foundation.UpdateSig
#check Foundation.HistoricalBinaryMerge
#check Foundation.UpdateSig.historicalMerge
#check Foundation.ReplayPolicy
#check Foundation.UpdateSig.commutes
#check MRDTSig.toUpdateSig
#check MRDTSig.historicalBinaryMerge
#check Foundation.applySeq
#check Foundation.listPermOf
#check Foundation.respects

-- Version-DAG semantics.
#check Version
#check Reaches
#check IsGCA
#check CommonAncestors
#check IsMaximalCommonAncestor
#check CommonAncestorsWithAny
#check IsMaximalCommonAncestorWithAny
#check isMaximalCommonAncestorWithAny_singleton
#check Configuration
#check Configuration.headState
#check Configuration.headEvents
#check initConfig
#check Label
#check Step
#check Step.fork
#check Step.apply
#check Step.query
#check Step.merge
#check Step.fork_copies_source
#check Step.fork_head_ne_root
#check labeledTS
#check StoreInv
#check gca_events_of_storeInv
#check isGCA_unique

-- Replay context, set-relative order, and canonicality.
#check Foundation.ReplayContext
#check Configuration.replayContext
#check Foundation.loOn
#check Foundation.loOn_mono
#check Foundation.loOn_of_lo
#check ReplayLaws
#check loOnNe_acyclic_of_replayLaws
#check exists_loOn_respecting_perm_of_replayLaws
#check Foundation.convergence_on
#check Foundation.IsCanonicalState
#check CanonicalConfig
#check HasReplayWitness
#check hasReplayWitness_of_canonical

-- Join surface and ordinary adequacy.
#check Join
#check JoinAt
#check JoinOn
#check Join.toJoinOn
#check joinOn_true_iff
#check MergeLaws
#check CommutingPeelLaw
#check DeltaLaws
#check CausalDeltaLaw
#check JoinCoreLaws
#check FeasibleDeltaLaws
#check CanonicalJoinLaws
#check CanonicalJoinLaws.ofArbitrary
#check CanonicalJoinLaws.join
#check JoinProof.ofArbitraryStateLaws
#check JoinProof.ofFeasibleStateLaws
#check replayWitness_of_join
#check CommutingPeelLaw.commuting_peel

-- Issuance and client-facing correctness.
#check Issuance
#check MintHonest
#check IssuedStep
#check MintCertifiedReach
#check MintCertifiedReach.toReachable
#check MintCertifiedReachV.toReachable
#check IssuanceEstablishes
#check replayWitness_of_mintCertified
#check ConcurrentOrder
#check Interaction
#check InteractionSpec
#check interactionLoOn
#check SequentialMachine
#check SequentialSpec
#check SequentialSpec.run
#check IsSpecLinearizable
#check ReplayAdequacyCertificate
#check ReplayAdequacyCertificate.ofJoin
#check ReplayAdequacyCertificate.ofJoinOn
#check ReplayAdequacyCertificate.sound
#check SequentialCorrectnessCertificate
#check VerifiedMRDT
#check PackagedMRDT
#check VerifiedMRDT.correct
#check VerifiedMRDT.correctV

-- Released instance profiles and the typed production boundary.
#check Production.registry
#check Production.names
#check Instances.AddStore.D
#check Instances.AddStore.generation
#check Instances.AddStore.spec
#check Instances.AddStore.verified
#check Instances.FlatCounters.D
#check Instances.FlatCounters.generation
#check Instances.FlatCounters.spec
#check Instances.FlatCounters.verified
#check Instances.FlatGrowOnly.verified
#check Instances.BoundedCounter.bcApplicable
#check Instances.BoundedCounter.ClientLegal
#check Instances.BoundedCounter.clientSpec
#check Instances.BoundedCounter.verified
#check Instances.LWWRegister.D
#check Instances.LWWRegister.interaction
#check Instances.LWWRegister.spec
#check Instances.LWWRegister.stateRel
#check Instances.LWWRegister.replay_lo_false
#check Instances.LWWRegister.canonical_respects
#check Instances.LWWRegister.verified
#check Instances.ORSet.canIssue
#check Instances.ORSet.interaction
#check Instances.ORSet.spec
#check Instances.ORSet.stateRel
#check Instances.ORSet.verified
#check Instances.RGA.applicable
#check Instances.RGA.join
#check Instances.RGA.listLegal
#check Instances.RGA.listSpec
#check Instances.RGA.listRel
#check Instances.RGA.verified
#check Instances.TreeMove.applicable
#check Instances.TreeMove.SequentialLegal
#check Instances.TreeMove.sequentialSpec
#check Instances.TreeMove.verified
#check Instances.AegisSheet.applicable
#check Instances.AegisSheet.join
#check Instances.AegisSheet.Sequential.CausalOriginLegal
#check Instances.AegisSheet.Sequential.clientSpec
#check Instances.AegisSheet.verified
#check Instances.EmbedRGA.EHonestCore
#check Instances.EmbedRGA.eApplicable
#check Instances.EmbedRGA.e_join_at
#check Instances.ProductionRGA.embedLegal
#check Instances.ProductionRGA.embedClientSpec
#check Instances.ProductionRGA.embed
#check Instances.Peritext.verified
#check Instances.SidedEmbedRGA.SHonestCore
#check Instances.SidedEmbedRGA.sApplicable
#check Instances.SidedEmbedRGA.s_join_at
#check Instances.SidedPeritext.coreGuard
#check Instances.SidedPeritext.core_join_at
#check Instances.SidedPeritext.clientSpec
#check Instances.SidedPeritext.verified
#check Instances.SidedPeritext.richVerified

-- Virtual merge bases and widened adequacy.
#check VirtualMergeBaseResolver
#check StepV
#check StepV.mergeVirtual
#check maximalCommonAncestorsWithAny
#check mem_maximalCommonAncestorsWithAny_iff
#check maximalCommonAncestorsWithAny_events_cover
#check vfoldAux
#check virtualBaseAux
#check virtualMergeBaseState
#check canonicalVirtualMergeBase
#check unionEvents
#check maximalCommonAncestorsWithAny_unionEvents
#check virtualMergeBaseState_canonical
#check canonicalConfig_reachableV
#check replayWitnessV_of_join
#check replayWitness_of_mintCertifiedV

-- Commit-history and datatype-state collection.
#check GC.Local
#check GC.Envelope
#check GC.advertise
#check GC.receive
#check GC.World
#check GC.Author
#check GC.DerivedEvidence
#check GC.EvidenceComplete
#check GC.Certificate
#check GC.collect
#check GC.compressedEdge
#check GC.CompressedReaches
#check GC.compressedReaches_iff
#check GC.compressed_isGCA_iff_of_maximalCommonAncestorClosed
#check GC.root_absent_when_dropped
#check GC.Certificate.ofMaximalCommonAncestorClosed
#check GC.StoreSim
#check GC.WorldSim
#check GC.execution_refines_noGC
#check GC.Runtime
#check GC.Runtime.WellFormed
#check GC.RuntimeStep
#check GC.eraseLabels
#check GC.runtime_refines_core
#check GC.runtime_refines_coreV
#check StateGCProtocol
#check StateGCProtocol.refines
#check StateGCCertificate
#check StateGCCertificate.exactState
#check StateGCCoverage
#check PackagedStateGC
#check Production.StateGC.registry
#check Production.StateGC.names
#check Instances.TreeMove.GC.collectPrefix
#check Instances.TreeMove.GC.collectTrash
#check Instances.TreeMove.GC.protocol
#check Instances.RGA.GC.pack
#check Instances.RGA.GC.unpack
#check Instances.RGA.GC.packedWords_pack_lt_of_grave
#check Instances.RGA.GC.certificate
#check Instances.RGA.GC.erase_dead_anchor_breaks_future_issuance
#check Instances.AegisSheet.GC.semanticCollect
#check Instances.AegisSheet.GC.certificate
#check Instances.SidedPeritext.StateGC.Protocol.protocol
#check Instances.SidedPeritext.StateGC.Protocol.refines
#check HeadOnlyMergeCapability
#check GC.combinedProtocol
#check GC.CombinedSteps.refinesV
#check GC.CombinedSteps.refinesRaw

-- Negative controls kept outside production packaging.
#check Foundation.convergence_over_backward_closed_subsets_false
#check Foundation.binaryLaws_insufficient

end Sal.MRDTs
