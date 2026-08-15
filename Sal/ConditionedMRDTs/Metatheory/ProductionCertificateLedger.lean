import Sal.ConditionedMRDTs.MRDT_Instances.VerifiedCertificates
import Sal.ConditionedMRDTs.MRDT_Instances.ProductionGenerationContracts
import Sal.ConditionedMRDTs.MRDT_Instances.FlatUnifiedCertificates
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_WithTombstones.RGA_Intent
import Sal.ConditionedMRDTs.MRDT_Instances.MVR.MVR_Unified
import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_WithTombstones.Peritext_Intent
import Sal.ConditionedMRDTs.MRDT_Instances.DistributedUnifiedCertificates
import Sal.ConditionedMRDTs.Metatheory.UnifiedVerifiedMRDT
import Sal.ConditionedMRDTs.Metatheory.Distributed_GC_Refinement
import Sal.ConditionedMRDTs.Metatheory.Distributed_GC_Acknowledgements
import Sal.ConditionedMRDTs.Metatheory.RefactorLedger

/-! Mechanically checked ledger for production `VerifiedMRDT` packages.

It also imports `RefactorLedger`; Shesha's formerly colliding update callback
is now named `sheshaUpdate`, so the production and refactor surfaces coexist in
one Lean environment.
-/

open Sal.ConditionedMRDTs

#check SequentialSpec.run_prod
#check SequentialRefinement.toHistory
#check HistorySequentialRefinement.prod
#check embedVerified
#check embedVerifiedRuntime
#check embedVerifiedRuntime_multiEpoch
#check sidedVerified
#check queueVerified
#check embedQueueVerified
#check VerifiedMRDT.ra_linearizable
#check VerifiedMRDT.sequential
#check VerifiedMRDT.prod
#check VerifiedRuntimeMRDT.compact_continuation

/-! Conditioning is classified by the public generation contract, not by the
legacy signature field.  These checks are a compile-time ledger: removing a
real issuer guard or its guard-to-history bridge breaks this module. -/
#check boundedCounterGeneration.Guard
#check boundedCounterGeneration.history_of_mint
#check bcGenHonest_of_mintHonest
#check boundedCounterSequentialRefinement
#check boundedCounterVerified
#check boundedCounterSafety
#check boundedCounterUnified
#check bcApplicable_inv_pres
#check bc_version_inv
#check bc_version_invV
#check bc_value_nonneg
#check queueGeneration.Guard
#check queueGeneration.history_of_mint
#check qHonest_of_applicable
#check embedGeneration
#check eHonest_of_applicable
#check sidedGeneration
#check sHonest_of_applicable
#check MintCertifiedReach3
#check MintCertifiedReach3V
#check honestReach_of_mintCertified
#check UnifiedVerifiedMRDT.ra_linearizable
#check UnifiedVerifiedMRDT.ra_linearizableV
#check UnifiedVerifiedMRDT.safe
#check UnifiedVerifiedMRDT.safeV
#check UnifiedVerifiedMRDT.observable
#check UnifiedVerifiedMRDT.prod
#check boundedCounter_flagship
#check boundedCounter_guarded_flagship
#check boundedCounterCertificate
#check queueUnified
#check embedUnified
#check sidedUnified
#check peritextEmbedUnified
#check counterUnified
#check iocUnified
#check pnUnified
#check orsetUnified
#check orseteUnified
#check gosetUnified
#check gomapUnified
#check lwwUnified
#check fwwUnified
#check awpqUnified
#check VerifiedMRDTF
#check UnifiedVerifiedMRDTF.ra_linearizable
#check UnifiedVerifiedMRDTF.ra_linearizableV
#check ewflagUnifiedF
#check rgaApplicable
#check RGAHistoryOK
#check rgaSequentialSound
#check rgaHistorySequentialRefinement
#check rgaGeneration
#check rgaUnified
#check mvrApplicable
#check MVRMintHistory
#check mvrGeneration
#check mvrUnified
#check ptApplicable
#check PtHistoryOK
#check ptSequentialSound
#check ptHistorySequentialRefinement
#check ptGeneration
#check ptUnified
#check DerivedEvidence
#check distributed_execution_refines_noGC
#check ValidFetchReceipt
#check acknowledge_erases
#check acknowledgedStep_refines_noGC
#check acknowledged_execution_refines_noGC
#check pruneEvidence_of_receipts
#check no_pruneEvidence_without_authored_or_receipt
#check coordinated_collect_projects_global
#check distributedConfig_refines_Step3
#check query_unavailable_without_head
#check mintCertifiedReach_of_distributed
#check UnifiedVerifiedMRDT.distributed
#check boundedCounterDistributed
#check queueDistributed
#check tombstoneRGADistributed
#check mvrDistributed
#check orsetDistributed
#check peritextTombstoneDistributed
#check peritextEmbedDistributed

/-! Negative controls remain absent from this production package: BudgetCart
has no `VerifiedMRDT` witness, and Shesha's checked refutations live only in
the refutation modules. -/
