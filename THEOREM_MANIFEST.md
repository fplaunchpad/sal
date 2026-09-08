# Stable theorem manifest

The production build gate is `Sal.MRDTs.Metatheory.RefactorLedger`. The names
below are the stable paper-facing API; internal helper names are not part of
the compatibility contract.

## Framework

- `Sal.MRDTs.Issuance`
- `Sal.MRDTs.Foundation.ReplayPolicy`
- `Sal.MRDTs.RcConflicts`
- `Sal.MRDTs.rcOn`
- `Sal.MRDTs.SequentialSpec`
- `Sal.MRDTs.SequentialCorrectnessCertificate`
- `Sal.MRDTs.IsSpecRALinearizable`
- `Sal.MRDTs.VerifiedMRDT`
- `Sal.MRDTs.PackagedMRDT`
- `Sal.MRDTs.Production.registry`
- `Sal.MRDTs.StateGCCertificate.exactState`
- `Sal.MRDTs.StateGCCoverage`
- `Sal.MRDTs.PackagedStateGC`
- `Sal.MRDTs.Production.StateGC.registry`
- `Sal.MRDTs.ConvergenceCertificate.sound`
- `Sal.MRDTs.MintCertifiedReach.toV`
- `Sal.MRDTs.Instances.RcSPOT.LWW.old_no_chain_refuted`

### Optional and migration certificates

- `Sal.MRDTs.SafetyCertificate`
- `Sal.MRDTs.SafetyCertificate.preservation`
- `Sal.MRDTs.SequentialRefinement`
- `Sal.MRDTs.ReplayAdequateMRDT`
- `Sal.MRDTs.StateGCProtocol.refines`
- `Sal.MRDTs.GC.execution_refines_noGC`
- `Sal.MRDTs.GC.runtime_refines_core`
- `Sal.MRDTs.GC.runtime_refines_coreV`
- `Sal.MRDTs.GC.CombinedSteps.refinesV`

## RGA and Peritext

- `Sal.MRDTs.Instances.RGA.verified`
- `Sal.MRDTs.Instances.RGA.rga_spec_linearizable`
- `Sal.MRDTs.Instances.RGA.rga_spec_linearizableV`
- `Sal.MRDTs.Instances.RGA.GC.certificate`
- `Sal.MRDTs.Instances.RGA.GC.packedWords_pack_lt_of_live_lt_grave`
- `Sal.MRDTs.Instances.RGA.GC.future_after_dead_anchor_not_applicable`
- `Sal.MRDTs.Instances.RGA.GC.erase_dead_anchor_rejects_future_issuance`
- `Sal.MRDTs.Instances.EmbedRGA.convergence`
- `Sal.MRDTs.Instances.SidedEmbedRGA.convergence`
- `Sal.MRDTs.Instances.ProductionRGA.embed`
- `Sal.MRDTs.Instances.ProductionRGA.sided`
- `Sal.MRDTs.Instances.ProductionRGA.embedRc`
- `Sal.MRDTs.Instances.ProductionRGA.sidedRc`
- `Sal.MRDTs.Instances.SidedEmbedRGA.fuguemax_maximally_noninterleaving`
- `Sal.MRDTs.Instances.Peritext.verified`
- `Sal.MRDTs.Instances.Peritext.render_sequentially_correct`
- `Sal.MRDTs.Instances.SidedPeritext.verified`
- `Sal.MRDTs.Instances.SidedPeritext.richVerified`
- `Sal.MRDTs.Instances.SidedPeritext.coreRc`
- `Sal.MRDTs.Instances.SidedPeritext.richRc`
- `Sal.MRDTs.Instances.SidedPeritext.rich_sequentially_correct`
- `Sal.MRDTs.Instances.SidedPeritext.StateGC.Protocol.protocol`
- `Sal.MRDTs.Instances.SidedPeritext.StateGC.Protocol.refines`

## Peritext state collection

- `Sal.MRDTs.Instances.SidedPeritext.StateGC.collectText_query_preserved`
- `Sal.MRDTs.Instances.SidedPeritext.StateGC.collectedText_continuation_query`
- `Sal.MRDTs.Instances.SidedPeritext.StateGC.trimDeleted_query_preserved`
- `Sal.MRDTs.Instances.SidedPeritext.StateGC.dropMarkPair_query_preserved`
- `Sal.MRDTs.Instances.SidedPeritext.StateGC.Interaction.merge_text_after_epoch_translation`

## Other production instances

- `Sal.MRDTs.Instances.LWWRegister.verified`
- `Sal.MRDTs.ReplayLaws.of_all_comm`
- `Sal.MRDTs.Instances.LWWRegister.replayLaws`
- `Sal.MRDTs.Instances.LWWRegister.ordered_updates_commute`
- `Sal.MRDTs.Instances.LWWRegister.concrete_noncomm_iff_rc_refuted`
- `Sal.MRDTs.Instances.LWWRegister.reversed_assignments_wrong_winner`
- `Sal.MRDTs.Instances.LWWRegister.canonical_respects`
- `Sal.MRDTs.Instances.LWWRegister.timestamp_chain`
- `Sal.MRDTs.Instances.LWWRegister.chronological_winner`
- `Sal.MRDTs.Instances.LWWRegister.lower_timestamp_does_not_win`
- `Sal.MRDTs.Instances.TreeMove.verified`
- `Sal.MRDTs.Instances.TreeMove.render_safe`
- `Sal.MRDTs.Instances.TreeMove.sequentialSound`
- `Sal.MRDTs.Instances.TreeMove.selfMove_rejected`
- `Sal.MRDTs.Instances.TreeMove.GC.undoRedo_algorithm_refines`
- `Sal.MRDTs.Instances.TreeMove.GC.collectPrefix_exact`
- `Sal.MRDTs.Instances.TreeMove.GC.appendFresh_exact`
- `Sal.MRDTs.Instances.TreeMove.GC.fullyStable_collectTrash_query`
- `Sal.MRDTs.Instances.TreeMove.GC.refines`
- `Sal.MRDTs.Instances.AegisSheet.verified`
- `Sal.MRDTs.Instances.AegisSheet.spec_linearizable`
- `Sal.MRDTs.Instances.AegisSheet.spec_linearizableV`
- `Sal.MRDTs.Instances.AegisSheet.Sequential.canonical_causalOriginLegal`
- `Sal.MRDTs.Instances.AegisSheet.Sequential.concurrent_origins_causal_legal`
- `Sal.MRDTs.Instances.AegisSheet.Sequential.unavailable_origin_not_causal_legal`
- `Sal.MRDTs.Instances.AegisSheet.Sequential.Abstraction.no_view_only_step`
- `Sal.MRDTs.Instances.AegisSheet.Sequential.Abstraction.row_tokens_distinguish_future`
- `Sal.MRDTs.Instances.AegisSheet.Sequential.Abstraction.cell_versions_distinguish_future`
- `Sal.MRDTs.Instances.AegisSheet.Sequential.Abstraction.range_versions_distinguish_future`
- `Sal.MRDTs.Instances.AegisSheet.sequentially_correct`
- `Sal.MRDTs.Instances.AegisSheet.observationally_correct`
- `Sal.MRDTs.Instances.AegisSheet.GC.certificate`
- `Sal.MRDTs.Instances.BoundedCounter.verified`
- `Sal.MRDTs.Instances.FlatCounters.counterVerified`
- `Sal.MRDTs.Instances.FlatCounters.iocVerified`
- `Sal.MRDTs.Instances.FlatCounters.pnVerified`
- `Sal.MRDTs.Instances.FlatGrowOnly.gosetVerified`
- `Sal.MRDTs.Instances.FlatGrowOnly.gomapVerified`
- `Sal.MRDTs.Instances.GSet.verified`
- `Sal.MRDTs.Instances.Queue.verified`
- `Sal.MRDTs.Instances.Queue.queue_correct`
- `Sal.MRDTs.Instances.Queue.queue_spec_linearizable`
- `Sal.MRDTs.Instances.Queue.queue_spec_linearizableV`
- `Sal.MRDTs.Instances.Queue.queue_legal_witness`
- `Sal.MRDTs.Instances.Queue.queue_versions_sorted`
- `Sal.MRDTs.Instances.Queue.issued_dequeue_no_visible_dequeue`
- `Sal.MRDTs.Instances.Queue.duplicate_dequeues_concurrent`
- `Sal.MRDTs.Instances.Queue.queue_version_contents`
- `Sal.MRDTs.Instances.Queue.client_linear_fifo`
- `Sal.MRDTs.Instances.MVRLive.verified`
- `Sal.MRDTs.Instances.MVRLive.mvr_correct`
- `Sal.MRDTs.Instances.MVRLive.version_maximal`
- `Sal.MRDTs.Instances.MVRLive.linear_register`
- `Sal.MRDTs.Instances.MVRLive.issued_overwrite`
- `Sal.MRDTs.Instances.MVRLive.rc_iff_overwrite_of_execution`
- `Sal.MRDTs.Instances.MVRLive.replay_legal`
- `Sal.MRDTs.Instances.MVRLive.represented_of_mintCertifiedV`
- `Sal.MRDTs.Instances.MVRLive.virtualMergeBaseState_represents`

## Non-production and internal evidence

These declarations are checked by `Sal.MRDTs.Metatheory.RefactorLedger` or
`Sal.MRDTs.Metatheory.NegativeLedger` and cannot enter `Production.registry`
without a complete `VerifiedMRDT` for the same signature.

- `Sal.MRDTs.Instances.MVR.replayAdequate`
- `Sal.MRDTs.Instances.MVR.concurrentState_no_sequential_register`
- `Sal.MRDTs.Instances.Queue.queue_replay_witness`
- `Sal.MRDTs.Instances.Queue.replayAdequate`
- `Sal.MRDTs.Instances.Queue.ConditioningSPOT.duplicate_dequeue_not_fifo`
- `Sal.MRDTs.Instances.SidedEmbedRGA.fmGeneration`
- `Sal.MRDTs.Instances.SidedEmbedRGA.fmReplayAdequacy`
- `Sal.MRDTs.Instances.SidedEmbedRGA.fuguemax_replay_witness`
- `Sal.MRDTs.Instances.SidedEmbedRGA.FugueMaxContractSPOT.short_reachable`
- `Sal.MRDTs.Instances.SidedEmbedRGA.FugueMaxContractSPOT.deleted_reachable`
- `Sal.MRDTs.Instances.SidedEmbedRGA.FugueMaxContractSPOT.weak_guard_accepts_wrong`
- `Sal.MRDTs.Instances.SidedEmbedRGA.FugueMaxContractSPOT.exact_issuance_not_state_predicate`

## FugueMax public certificate and supporting proofs

The enriched implementation is registered separately from the old `FMSig`.
Its general certificate and same-witness contract use only standard logical axioms.

- `Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.insertion_issuance_exact`
- `Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.deletion_issuance_exact`
- `Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.rawFold_exact`
- `Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.issuer_merge_refines`
- `Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.invariants_of_mint`
- `Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.join_of_mint`
- `Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.replayAdequacy`
- `Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.replay_noninterleaving`
- `Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.fmChainBefore_snocR_iff`
- `Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.fmChainBefore_snocL_iff`
- `Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.exists_chain_construction`
- `Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.births_refine`
- `Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.staged_legal`
- `Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.finalNodes_eq_live`
- `Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.verified`
- `Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.correct`
- `Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.IssuerSPOT.finite_guard_rejects_wrong`

Run `./scripts/check-mrdt-refactor.sh` to check the manifest’s imported ledger,
forbidden-import and proof-hole scans, and all runtime conformance tests.
